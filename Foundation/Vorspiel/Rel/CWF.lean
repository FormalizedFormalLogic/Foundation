module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Lattice.Fold
public import Foundation.Vorspiel.Rel.Connected


@[expose]
public section


section

abbrev ConverseWellFounded {α} (rel : Rel α α) := WellFounded $ flip rel

class IsConverseWellFounded (α) (rel : Rel α α) : Prop where cwf : ConverseWellFounded rel

end



section

variable {α} {R : Rel α α}

lemma ConverseWellFounded.iff_has_max : ConverseWellFounded R ↔ (∀ (s : Set α), Set.Nonempty s → ∃ m ∈ s, ∀ x ∈ s, ¬(R m x)) := by
  simp [ConverseWellFounded, WellFounded.wellFounded_iff_has_min, flip]

lemma ConverseWellFounded.has_max (h : ConverseWellFounded R) : ∀ (s : Set α), Set.Nonempty s → ∃ m ∈ s, ∀ x ∈ s, ¬(R m x) := by
  apply ConverseWellFounded.iff_has_max.mp h;

theorem Finite.converseWellFounded_of_trans_of_irrefl [Finite α] [IsTrans α R] [Std.Irrefl R] : ConverseWellFounded R := by
  apply @Finite.wellFounded_of_trans_of_irrefl _ _ _
    ⟨by intro a b c rba rcb; exact IsTrans.trans c b a rcb rba⟩
    ⟨by simp [flip, Std.Irrefl.irrefl]⟩

instance [Finite α] [IsTrans α R] [Std.Irrefl R] : IsConverseWellFounded _ R :=
  ⟨Finite.converseWellFounded_of_trans_of_irrefl⟩

namespace IsConverseWellFounded




end IsConverseWellFounded

variable (R)

open Classical in
noncomputable def cwfHeight [IsConverseWellFounded α R] [Fintype α] : α → ℕ :=
  WellFounded.fix (r := flip R) (C := fun _ ↦ ℕ) IsConverseWellFounded.cwf fun x ih ↦
    Finset.univ.sup fun y : {y : α // R x y} ↦ ih y y.prop + 1

variable {R}

section cwfHeight

variable [Fintype α] [IsConverseWellFounded α R]

open Classical

lemma cwfHeight_eq (a : α) :
    cwfHeight R a = Finset.sup {x : α | R a x} (fun b ↦ cwfHeight R b + 1) := by
  have h : cwfHeight R a = Finset.univ.sup fun b : {y : α // R a y} ↦ cwfHeight R b + 1 :=
    WellFounded.fix_eq _ _ a
  suffices
    Finset.univ.sup (fun b : {y : α // R a y} ↦ cwfHeight R b + 1) =
    Finset.sup {y : α | R a y} fun b ↦ cwfHeight R b + 1 from h.trans this
  apply eq_of_le_of_ge
  · apply Finset.sup_le
    intro b _
    exact Finset.le_sup (f := fun b ↦ cwfHeight R b + 1) (by simp [b.prop])
  · apply Finset.sup_le
    intro b hb
    simpa using Finset.le_sup (f := fun b : {y : α // R a y} ↦ cwfHeight R b + 1)
      (b := ⟨b, by simpa using hb⟩) (s := Finset.univ) (by simp)

lemma cwfHeight_gt_of {a b} :
    R a b → cwfHeight R a > cwfHeight R b := fun h ↦ calc
  cwfHeight R a = Finset.sup {x : α | R a x} fun b ↦ cwfHeight R b + 1 := cwfHeight_eq a
  _               ≥ cwfHeight R b + 1 := Finset.le_sup (f := fun b ↦ cwfHeight R b + 1) (by simp [h])

lemma cwfHeight_eq_zero_iff {a : α} :
    cwfHeight R a = 0 ↔ ∀ b, ¬R a b := by
  constructor
  · intro h b hb
    have : cwfHeight R a > cwfHeight R b := cwfHeight_gt_of hb
    exact Nat.not_succ_le_zero (cwfHeight R b) (h ▸ this)
  · intro ha
    apply Nat.eq_zero_of_le_zero
    calc
      cwfHeight R a = Finset.sup {x : α | R a x} fun b ↦ cwfHeight R b + 1 := cwfHeight_eq a
      _               ≤ 0 := Finset.sup_le fun b hb ↦ False.elim <| ha b (by simpa using hb)

lemma cwfHeight_le {a : α}
    (h : ∀ b, R a b → cwfHeight R b < n) : cwfHeight R a ≤ n := by
  rw [cwfHeight_eq]
  apply Finset.sup_le
  intro b hab
  exact h b (by simpa using hab)

lemma lt_cwfHeight {a : α} (hb : R a b) (h : n ≤ cwfHeight R b) : n < cwfHeight R a := by
  have : cwfHeight R b < cwfHeight R a := by
    apply Nat.lt_of_succ_le
    rw [cwfHeight_eq a]
    exact Finset.le_sup (s := {x : α | R a x})
      (f := fun b ↦ cwfHeight R b + 1) (b := b) (by simp [hb])
  exact lt_of_le_of_lt h this

lemma cwfHeight_eq_of_lt_of_le {a : α}
    (hR : ∀ b, R a b → cwfHeight R b < n) (h : ∃ b, R a b ∧ n ≤ cwfHeight R b + 1) : cwfHeight R a = n := by
  suffices cwfHeight R a ≤ n ∧ cwfHeight R a ≥ n from Nat.eq_iff_le_and_ge.mpr this
  constructor
  · exact cwfHeight_le hR
  · rcases h with ⟨b, hb, hn⟩
    suffices n - 1 < cwfHeight R a from Nat.le_of_pred_lt this
    apply lt_cwfHeight hb
    exact Nat.sub_le_of_le_add hn

lemma cwfHeight_eq_succ {a : α} (h : cwfHeight R a ≠ 0) :
    ∃ b, R a b ∧ cwfHeight R a = cwfHeight R b + 1 := by
  have : ∃ b, R a b := by
    by_contra A
    have : cwfHeight R a = 0 := cwfHeight_eq_zero_iff.mpr <| by simpa using A
    simp_all
  have : ({x : α | R a x} : Finset α).Nonempty := by simpa [Finset.filter_nonempty_iff] using this
  simpa [cwfHeight_eq (R := R) a] using Finset.exists_mem_eq_sup _ this (fun b ↦ cwfHeight R b + 1)

lemma cwfHeight_eq_succ_cwfHeight {a b : α} (h : R a b) (hb : ∀ c, R a c → R b c ∨ b = c) :
    cwfHeight R a = cwfHeight R b + 1 := by
  apply cwfHeight_eq_of_lt_of_le
  · intro c Rac
    rcases hb c Rac with (Rbc | rfl)
    · suffices cwfHeight R c < cwfHeight R b from Nat.lt_add_right 1 this
      exact cwfHeight_gt_of Rbc
    · simp
  · use b

lemma cwfHeight_lt [IsTrans α R] {a : α} :
    ∀ {n}, n < cwfHeight R a → ∃ b, R a b ∧ cwfHeight R b = n := by
  apply WellFounded.induction (r := flip R) IsConverseWellFounded.cwf a
  intro a ih
  rcases ha : cwfHeight R a with (_ | n)
  · simp
  · intro k hk
    have : ∃ b, R a b ∧ cwfHeight R b = n := by
      rcases cwfHeight_eq_succ (R := R) (a := a) (by simp [ha]) with ⟨b, hb, e⟩
      exact ⟨b, hb, by grind⟩
    rcases this with ⟨b, hb, rfl⟩
    have : k = cwfHeight R b ∨ k < cwfHeight R b := Nat.eq_or_lt_of_le <| Nat.le_of_lt_succ hk
    rcases this with (rfl | hk)
    · exact ⟨b, hb, rfl⟩
    · have : ∃ c, R b c ∧ cwfHeight R c = k := ih b hb hk
      rcases this with ⟨c, hc, rfl⟩
      exact ⟨c, IsTrans.trans _ _ _ hb hc, rfl⟩

/-- `cwfHeight` is invariant under an equivalence of relations: if `f : α ≃ β` carries `R`
to `R'`, then the heights of corresponding points agree. -/
lemma cwfHeight_congr {β} [Fintype β] {R' : Rel β β} [IsConverseWellFounded β R']
    (f : α ≃ β) (hf : ∀ a b, R a b ↔ R' (f a) (f b)) (a : α) :
    cwfHeight R a = cwfHeight R' (f a) := by
  apply WellFounded.induction (r := flip R) IsConverseWellFounded.cwf a
  intro a ih
  apply le_antisymm
  · apply cwfHeight_le
    intro b hab
    rw [ih b hab]
    exact cwfHeight_gt_of ((hf a b).mp hab)
  · apply cwfHeight_le
    intro b' hab'
    obtain ⟨b, rfl⟩ := f.surjective b'
    have hab : R a b := (hf a b).mpr hab'
    rw [← ih b hab]
    exact cwfHeight_gt_of hab

end cwfHeight

end

end
