import Mathlib.Data.Fintype.Card
import Mathlib.Order.WellFounded
import Foundation.Vorspiel.HRel.Connected
import Mathlib.Data.Finset.Lattice.Fold

section

abbrev ConverseWellFounded {α} (rel : HRel α) := WellFounded $ flip rel

class IsConverseWellFounded (α) (rel : HRel α) : Prop where cwf : ConverseWellFounded rel

end


section

variable {α} {R : HRel α}

lemma ConverseWellFounded.iff_has_max : ConverseWellFounded R ↔ (∀ (s : Set α), Set.Nonempty s → ∃ m ∈ s, ∀ x ∈ s, ¬(R m x)) := by
  simp [ConverseWellFounded, WellFounded.wellFounded_iff_has_min, flip]

lemma ConverseWellFounded.has_max (h : ConverseWellFounded R) : ∀ (s : Set α), Set.Nonempty s → ∃ m ∈ s, ∀ x ∈ s, ¬(R m x) := by
  apply ConverseWellFounded.iff_has_max.mp h;

instance [Finite α] [IsTrans α R] [IsIrrefl α R] : IsConverseWellFounded _ R := ⟨by
  apply @Finite.wellFounded_of_trans_of_irrefl _ _ _
    ⟨by intro a b c rba rcb; exact IsTrans.trans c b a rcb rba⟩
    ⟨by simp [flip, IsIrrefl.irrefl]⟩
⟩

lemma Finite.converseWellFounded_of_trans_irrefl'
    (hFinite : Finite α) (hTrans : Transitive R) (hIrrefl : Irreflexive R) : ConverseWellFounded R :=
  @Finite.wellFounded_of_trans_of_irrefl _ _ _
    ⟨by simp [flip]; intro a b c ba cb; exact hTrans cb ba;⟩
    ⟨by simp [flip]; exact hIrrefl⟩

variable (R)

open Classical in
noncomputable def fcwHeight [IsConverseWellFounded α R] [Fintype α] : α → ℕ :=
  WellFounded.fix (r := flip R) (C := fun _ ↦ ℕ) IsConverseWellFounded.cwf fun x ih ↦
    Finset.univ.sup fun y : {y : α // R x y} ↦ ih y y.prop + 1

variable {R}

section fcwHeight

variable [Fintype α] [IsConverseWellFounded α R]

open Classical

lemma fcwHeight_eq (a : α) :
    fcwHeight R a = Finset.sup {x : α | R a x} (fun b ↦ fcwHeight R b + 1) := by
  have h : fcwHeight R a = Finset.univ.sup fun b : {y : α // R a y} ↦ fcwHeight R b + 1 :=
    WellFounded.fix_eq _ _ a
  suffices
    Finset.univ.sup (fun b : {y : α // R a y} ↦ fcwHeight R b + 1) =
    Finset.sup {y : α | R a y} fun b ↦ fcwHeight R b + 1 from h.trans this
  apply eq_of_le_of_ge
  · apply Finset.sup_le
    intro b _
    exact Finset.le_sup (f := fun b ↦ fcwHeight R b + 1) (by simp [b.prop])
  · apply Finset.sup_le
    intro b hb
    simpa using Finset.le_sup (f := fun b : {y : α // R a y} ↦ fcwHeight R b + 1)
      (b := ⟨b, by simpa using hb⟩) (s := Finset.univ) (by simp)

lemma fcwHeight_gt_of {a b} :
    R a b → fcwHeight R a > fcwHeight R b := fun h ↦ calc
  fcwHeight R a = Finset.sup {x : α | R a x} fun b ↦ fcwHeight R b + 1 := fcwHeight_eq a
  _               ≥ fcwHeight R b + 1 := Finset.le_sup (f := fun b ↦ fcwHeight R b + 1) (by simp [h])

lemma fcwHeight_eq_zero_iff {a : α} :
    fcwHeight R a = 0 ↔ ∀ b, ¬R a b := by
  constructor
  · intro h b hb
    have : fcwHeight R a > fcwHeight R b := fcwHeight_gt_of hb
    exact Nat.not_succ_le_zero (fcwHeight R b) (h ▸ this)
  · intro ha
    apply Nat.eq_zero_of_le_zero
    calc
      fcwHeight R a = Finset.sup {x : α | R a x} fun b ↦ fcwHeight R b + 1 := fcwHeight_eq a
      _               ≤ 0 := Finset.sup_le fun b hb ↦ False.elim <| ha b (by simpa using hb)

lemma fcwHeight_eq_succ {a : α} (h : fcwHeight R a ≠ 0) :
    ∃ b, R a b ∧ fcwHeight R a = fcwHeight R b + 1 := by
  have : ∃ b, R a b := by
    by_contra A
    have : fcwHeight R a = 0 := fcwHeight_eq_zero_iff.mpr <| by simpa using A
    simp_all
  have : ({x : α | R a x} : Finset α).Nonempty := by simpa [Finset.filter_nonempty_iff] using this
  simpa [fcwHeight_eq (R := R) a] using Finset.exists_mem_eq_sup _ this (fun b ↦ fcwHeight R b + 1)

lemma fcwHeight_lt [IsTrans α R] {a : α} :
    ∀ {n}, n < fcwHeight R a → ∃ b, R a b ∧ fcwHeight R b = n := by
  apply WellFounded.induction (r := flip R) IsConverseWellFounded.cwf a
  intro a ih
  rcases ha : fcwHeight R a with (_ | n)
  · simp
  · intro k hk
    have : ∃ b, R a b ∧ fcwHeight R b = n := by
      rcases fcwHeight_eq_succ (R := R) (a := a) (by simp [ha]) with ⟨b, hb, e⟩
      exact ⟨b, hb, by grind⟩
    rcases this with ⟨b, hb, rfl⟩
    have : k = fcwHeight R b ∨ k < fcwHeight R b := Nat.eq_or_lt_of_le <| Nat.le_of_lt_succ hk
    rcases this with (rfl | hk)
    · exact ⟨b, hb, rfl⟩
    · have : ∃ c, R b c ∧ fcwHeight R c = k := ih b hb hk
      rcases this with ⟨c, hc, rfl⟩
      exact ⟨c, IsTrans.trans _ _ _ hb hc, rfl⟩

end fcwHeight

end
