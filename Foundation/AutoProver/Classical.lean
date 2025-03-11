import Foundation.Propositional.Classical.Basic
import Foundation.Propositional.Tait.Calculus
import Foundation.Propositional.Classical.Tait
import Mathlib.Algebra.Order.BigOperators.Group.List

namespace List

def smin (l : List ℕ) : ℕ := l.min?.casesOn 0 .succ

@[simp] lemma smin_nil : [].smin = 0 := rfl

end List

namespace LO.Propositional

variable {α : Type*}

namespace NNFormula

@[simp] lemma ne_neg (φ : NNFormula α) : ∼φ ≠ φ := by
  induction φ using NNFormula.rec' <;> simp

inductive IsAtomic : NNFormula α → Prop
  |  atom (a : α) : IsAtomic (.atom a)
  | natom (a : α) : IsAtomic (.natom a)

attribute [simp] IsAtomic.atom IsAtomic.natom

@[simp] lemma IsAtomic.not_cons_verum : ¬IsAtomic (⊤ : NNFormula α) := by rintro ⟨⟩
@[simp] lemma IsAtomic.not_cons_falsum : ¬IsAtomic (⊥ : NNFormula α) := by rintro ⟨⟩
@[simp] lemma IsAtomic.not_cons_and {φ ψ : NNFormula α} : ¬IsAtomic (φ ⋏ ψ) := by rintro ⟨⟩
@[simp] lemma IsAtomic.not_cons_or {φ ψ : NNFormula α} : ¬IsAtomic (φ ⋎ ψ) := by rintro ⟨⟩

instance : DecidablePred (IsAtomic (α := α)) := fun φ ↦
  match φ with
  |  .atom a => .isTrue (by simp)
  | .natom a => .isTrue (by simp)
  |        ⊤ => .isFalse (by simp)
  |        ⊥ => .isFalse (by simp)
  |    _ ⋏ _ => .isFalse (by simp)
  |    _ ⋎ _ => .isFalse (by simp)

def weight : NNFormula α → ℕ
| atom _  => 0
| natom _ => 0
| ⊤       => 1
| ⊥       => 1
| φ ⋏ ψ   => φ.weight + ψ.weight + 1
| φ ⋎ ψ   => φ.weight + ψ.weight + 1

@[simp] lemma weight_atom (a : α) : complexity (atom a) = 0 := rfl
@[simp] lemma weight_natom (a : α) : complexity (natom a) = 0 := rfl
@[simp] lemma weight_verum : weight (⊤ : NNFormula α) = 1 := rfl
@[simp] lemma weight_falsum : weight (⊥ : NNFormula α) = 1 := rfl
@[simp] lemma weight_and (φ ψ : NNFormula α) : weight (φ ⋏ ψ) = φ.weight + ψ.weight + 1 := rfl
@[simp] lemma weight_or (φ ψ : NNFormula α) : weight (φ ⋎ ψ) = φ.weight + ψ.weight + 1 := rfl

end NNFormula

variable {Γ Δ : Sequent α}

namespace Sequent

def weight (Γ : Sequent α) : ℕ := (Γ.map NNFormula.weight).sum

@[simp] lemma weight_nil : weight ([] : Sequent α) = 0 := rfl

@[simp] lemma weight_cons (φ) (Γ : Sequent α) : weight (φ :: Γ) = φ.weight + Γ.weight := rfl

@[simp] lemma weight_append (Γ Δ : Sequent α) : weight (Γ ++ Δ) = Γ.weight + Δ.weight := by
  unfold weight; simp

lemma weight_le_weight_of_mem {φ : NNFormula α} {Γ : Sequent α} (h : φ ∈ Γ) : φ.weight ≤ Γ.weight :=
  List.le_sum_of_mem (List.mem_map_of_mem NNFormula.weight h)

lemma weight_remove [DecidableEq α] (Γ : Sequent α) (φ) :
    weight (Γ.remove φ) = Γ.weight - Γ.count φ * φ.weight := by
  suffices weight (Γ.remove φ) + Γ.count φ * φ.weight = Γ.weight from Nat.eq_sub_of_add_eq this
  induction Γ
  case nil => simp
  case cons ψ Γ ih =>
    by_cases e : φ = ψ
    · rcases e
      simp [add_mul, ←add_assoc, add_comm φ.weight, ih]
    · simp [e, Γ.remove_cons_of_ne (Ne.symm e), add_assoc, ih]

lemma weight_remove_le_of_mem [DecidableEq α] {φ} {Γ : Sequent α} (h : φ ∈ Γ) :
    weight (Γ.remove φ) ≤ Γ.weight - φ.weight := calc
  weight (Γ.remove φ) = Γ.weight - Γ.count φ * φ.weight := weight_remove Γ φ
  _                   ≤ Γ.weight - φ.weight             :=
    Nat.sub_le_sub_left (Nat.le_mul_of_pos_left φ.weight (List.count_pos_iff.mpr h)) Γ.weight

def IsAtomic (Γ : Sequent α) : Prop := ∀ φ ∈ Γ, φ.IsAtomic

@[simp] lemma IsAtomic.nil : IsAtomic ([] : Sequent α) := by intro _; simp

instance : DecidablePred (IsAtomic (α := α)) := List.decidableBAll NNFormula.IsAtomic

@[simp] lemma IsAtomic.cons_atom_iff : IsAtomic (φ :: Γ) ↔ φ.IsAtomic ∧ IsAtomic Γ := by
  simp [IsAtomic]

def chooseNonAtomic (Γ : Sequent α) (H : ¬Γ.IsAtomic) : NNFormula α :=
  Γ.choose (fun φ ↦ ¬φ.IsAtomic) (by simpa [IsAtomic] using H)

@[simp] lemma chooseNonAtomic_mem {Γ : Sequent α} (h : ¬Γ.IsAtomic) : Γ.chooseNonAtomic h ∈ Γ := List.choose_mem _ _ _

@[simp] lemma chooseNonAtomic_property (Γ : Sequent α) (h : ¬Γ.IsAtomic) : ¬(Γ.chooseNonAtomic h).IsAtomic :=
  List.choose_property (fun φ : NNFormula α ↦ ¬φ.IsAtomic) _ _

end Sequent

abbrev Sequents (α : Type*) := List (Sequent α)

namespace Sequents

def weight (S : Sequents α) (h : S ≠ []) : ℕ := (S.map Sequent.weight).min?.get (by
  have : ∃ x, x ∈ S := List.exists_mem_of_ne_nil S h
  rcases this with ⟨x, hx⟩
  exact List.isSome_min?_of_mem (a := x.weight) (List.mem_map_of_mem Sequent.weight hx))

end Sequents

abbrev Derivations (T : Theory α) (S : Sequents α) := ∀ Γ ∈ S, T ⟹ Γ

abbrev Derivations! (T : Theory α) (S : Sequents α) : Prop := ∀ Γ ∈ S, T ⟹! Γ

namespace Derivations

variable {T : Theory α} {S₁ S₂ : Sequents α}

def ofSubset (ss : S₁ ⊆ S₂) : Derivations T S₂ → Derivations T S₁ := fun d Γ hΓ ↦ d Γ (ss hΓ)

def nil : Derivations T [] := fun _ h ↦ False.elim <| by simp at h

end Derivations

namespace Derivations!

@[simp] lemma nil : Derivations! T [] := fun _ h ↦ False.elim <| by simp at h

end Derivations!


def Sequent.IsClosed (Γ : Sequent α) : Prop := ∃ φ ∈ Γ, ∼φ ∈ Γ

lemma Sequent.IsClosed.cons_iff {Γ : Sequent α} :
    IsClosed (φ :: Γ) ↔ ∼φ ∈ Γ ∨ Γ.IsClosed := by
  simp [IsClosed]
  constructor
  · rintro (h | ⟨ψ, h, (rfl | hn)⟩)
    · simp [*]
    · simp [*]
    · right; exact ⟨ψ, by simp [*]⟩
  · rintro (h | ⟨ψ, h, hn⟩)
    · simp [*]
    · right; exact ⟨ψ, h, by simp [*]⟩

instance [DecidableEq α] : DecidablePred (Sequent.IsClosed (α := α)) :=
  List.rec
    (.isFalse <| by simp [Sequent.IsClosed])
    fun φ Γ d ↦
    if h : ∼φ ∈ Γ then .isTrue ⟨φ, by simp [h]⟩ else
    match d with
    | .isFalse hΓ => .isFalse <| by simp [Sequent.IsClosed.cons_iff, *]
    |  .isTrue hΓ => .isTrue <| by simp [Sequent.IsClosed.cons_iff, hΓ]

def Sequent.IsClosed.choose [DecidableEq α] : (Γ : Sequent α) → Γ.IsClosed → {φ // φ ∈ Γ ∧ ∼φ ∈ Γ}
  |     [], h => False.elim (by rcases h; simp_all)
  | φ :: Γ, h =>
    if hn : ∼φ ∈ Γ then ⟨φ, by simp [hn]⟩ else
    have : IsClosed Γ := by simpa [Sequent.IsClosed.cons_iff, hn] using h
    let ⟨ψ, hψ⟩ := this.choose
    ⟨ψ, by simp [hψ]⟩

def Derivation.ofIsClosed [DecidableEq α] {T : Theory α} {Γ : Sequent α} (h : Γ.IsClosed) : T ⟹ Γ :=
  let ⟨φ, h, hn⟩ := h.choose
  em (φ := φ) h hn

abbrev Sequent.IsOpen (Γ : Sequent α) : Prop := Γ.IsAtomic ∧ ¬Γ.IsClosed

instance [DecidableEq α] : DecidablePred (Sequent.IsOpen (α := α)) := inferInstance

lemma Sequent.IsOpen.not_tautology (h : Γ.IsOpen) : ¬Γ.IsTautology :=
  Sequent.notTautology_iff.mpr ⟨⟨fun a ↦ .atom a ∉ Γ⟩, fun φ hφ ↦ by
    rcases show φ.IsAtomic from h.1 φ hφ
    case atom a =>
      simp [hφ]
    case natom a =>
      suffices NNFormula.atom a ∉ Γ by simpa
      intro ha
      exact h.2 ⟨.atom a, by simp [*]⟩⟩

def Sequents.IsClosed (S : Sequents α) : Prop := ∀ Γ ∈ S, Γ.IsClosed

instance [DecidableEq α] : DecidablePred (Sequents.IsClosed (α := α)) := List.decidableBAll Sequent.IsClosed

variable {Γ Δ : Sequent α}

def Sequent.reduction [DecidableEq α] {Γ : Sequent α} (h : ¬Γ.IsAtomic) : Sequents α :=
  match H : Γ.chooseNonAtomic h with
  |  .atom a => by have := Γ.chooseNonAtomic_property h; simp_all
  | .natom a => by have := Γ.chooseNonAtomic_property h; simp_all
  |        ⊤ => []
  |        ⊥ => [Γ.remove ⊥]
  |    φ ⋏ ψ => [Γ.remove (φ ⋏ ψ) |>.concat φ, Γ.remove (φ ⋏ ψ) |>.concat ψ]
  |    φ ⋎ ψ => [Γ.remove (φ ⋎ ψ) |>.concat φ |>.concat ψ]

section

variable [DecidableEq α]

lemma Sequent.reduction_verum {h : ¬Γ.IsAtomic} (H : Γ.chooseNonAtomic h = ⊤) : Γ.reduction h = [] := by
  unfold Sequent.reduction; split <;> simp_all

lemma Sequent.reduction_falsum {h : ¬Γ.IsAtomic} (H : Γ.chooseNonAtomic h = ⊥) : Γ.reduction h = [Γ.remove ⊥] := by
  unfold Sequent.reduction; split <;> simp_all

lemma Sequent.reduction_and {h : ¬Γ.IsAtomic} (H : Γ.chooseNonAtomic h = φ ⋏ ψ) :
    Γ.reduction h = [Γ.remove (φ ⋏ ψ) |>.concat φ, Γ.remove (φ ⋏ ψ) |>.concat ψ] := by
  unfold Sequent.reduction; split <;> simp_all
  · rcases H; simp

lemma Sequent.reduction_or {h : ¬Γ.IsAtomic} (H : Γ.chooseNonAtomic h = φ ⋎ ψ) :
    Γ.reduction h = [Γ.remove (φ ⋎ ψ) |>.concat φ |>.concat ψ] := by
  unfold Sequent.reduction; split <;> simp_all
  · rcases H; simp

lemma Sequent.weight_lt_weight_of_mem_reduction {h : ¬Γ.IsAtomic} : Δ ∈ Γ.reduction h → Δ.weight < Γ.weight := by
  match H : Γ.chooseNonAtomic h with
  |  .atom a => have := Γ.chooseNonAtomic_property h; simp_all
  | .natom a => have := Γ.chooseNonAtomic_property h; simp_all
  |        ⊤ => simp [Sequent.reduction_verum H]
  |        ⊥ =>
    suffices weight (List.remove ⊥ Γ) < Γ.weight by simp [Sequent.reduction_falsum H]; rintro rfl; exact this
    have : ⊥ ∈ Γ := by simpa [*] using Sequent.chooseNonAtomic_mem h
    calc weight (List.remove ⊥ Γ) ≤ Γ.weight - NNFormula.weight ⊥ := Sequent.weight_remove_le_of_mem this
    _                             < Γ.weight                      := Nat.sub_lt_of_pos_le (by simp) (weight_le_weight_of_mem this)
  |    φ ⋏ ψ =>
    have : φ ⋏ ψ ∈ Γ := by simpa [*] using Sequent.chooseNonAtomic_mem h
    suffices
      weight (List.remove (φ ⋏ ψ) Γ ++ [φ]) < Γ.weight ∧
      weight (List.remove (φ ⋏ ψ) Γ ++ [ψ]) < Γ.weight by
        simp [Sequent.reduction_and H]; rintro (rfl | rfl); { exact this.1 }; { exact this.2 }
    constructor
    · calc
        weight (List.remove (φ ⋏ ψ) Γ ++ [φ]) = weight (List.remove (φ ⋏ ψ) Γ) + φ.weight := by simp
        _                                     ≤ Γ.weight - (φ ⋏ ψ).weight + φ.weight      :=
          (add_le_add_iff_right _).mpr (Sequent.weight_remove_le_of_mem this)
        _                                     = Γ.weight + φ.weight - (φ ⋏ ψ).weight      :=
          Eq.symm <| Nat.sub_add_comm <| weight_le_weight_of_mem this
        _                                     < Γ.weight                                  :=
          Nat.sub_lt_left_of_lt_add (Nat.le_add_right_of_le (weight_le_weight_of_mem this)) (by simp; omega)
    · calc
        weight (List.remove (φ ⋏ ψ) Γ ++ [ψ]) = weight (List.remove (φ ⋏ ψ) Γ) + ψ.weight := by simp
        _                                     ≤ Γ.weight - (φ ⋏ ψ).weight + ψ.weight      :=
          (add_le_add_iff_right _).mpr (Sequent.weight_remove_le_of_mem this)
        _                                     = Γ.weight + ψ.weight - (φ ⋏ ψ).weight      :=
          Eq.symm <| Nat.sub_add_comm <| weight_le_weight_of_mem this
        _                                     < Γ.weight                                  :=
          Nat.sub_lt_left_of_lt_add (Nat.le_add_right_of_le (weight_le_weight_of_mem this)) (by simp; omega)
  |    φ ⋎ ψ =>
    have : φ ⋎ ψ ∈ Γ := by simpa [*] using Sequent.chooseNonAtomic_mem h
    suffices weight (List.remove (φ ⋎ ψ) Γ ++ [φ, ψ]) < Γ.weight by simp [Sequent.reduction_or H]; rintro rfl; exact this
    calc weight (List.remove (φ ⋎ ψ) Γ ++ [φ, ψ]) = weight (List.remove (φ ⋎ ψ) Γ) + (φ.weight + ψ.weight) := by simp
    _                                             ≤ Γ.weight - (φ ⋎ ψ).weight + (φ.weight + ψ.weight)      :=
      (add_le_add_iff_right _).mpr (Sequent.weight_remove_le_of_mem this)
    _                                             = Γ.weight + (φ.weight + ψ.weight) - (φ ⋎ ψ).weight      :=
      Eq.symm <| Nat.sub_add_comm <| weight_le_weight_of_mem this
    _                                             < Γ.weight :=
      Nat.sub_lt_left_of_lt_add (Nat.le_add_right_of_le (weight_le_weight_of_mem this)) (by simp; omega)

def Derivation.ofReduction {Γ : Sequent α} {hΓ : ¬Γ.IsAtomic}
    (d : Derivations T (Γ.reduction hΓ)) : T ⟹ Γ :=
    match H : Γ.chooseNonAtomic hΓ with
    |  .atom a => by have := Γ.chooseNonAtomic_property hΓ; simp_all
    | .natom a => by have := Γ.chooseNonAtomic_property hΓ; simp_all
    |        ⊤ => verum' (by simpa [H] using Sequent.chooseNonAtomic_mem hΓ)
    |        ⊥ =>
      have : T ⟹ Γ.remove ⊥ := d (Γ.remove ⊥) (by simp [Sequent.reduction_falsum H])
      this.wk (by simp)
    |    φ ⋏ ψ =>
      have : T ⟹ (Γ.remove (φ ⋏ ψ)).concat φ := d _ (by simp [Sequent.reduction_and H])
      have dφ : T ⟹ φ :: Γ.remove (φ ⋏ ψ) := this.wk (by simp)
      have : T ⟹ (Γ.remove (φ ⋏ ψ)).concat ψ := d _ (by simp [Sequent.reduction_and H])
      have dψ : T ⟹ ψ :: Γ.remove (φ ⋏ ψ) := this.wk (by simp)
      dφ.and dψ |>.wk (by simpa [H] using Sequent.chooseNonAtomic_mem hΓ)
    |    φ ⋎ ψ =>
      have : T ⟹ ((Γ.remove (φ ⋎ ψ)).concat φ).concat ψ := d _ (by simp [Sequent.reduction_or H])
      have : T ⟹ φ :: ψ :: Γ.remove (φ ⋎ ψ) := this.wk <| by simp
      this.or |>.wk (by simpa [H] using Sequent.chooseNonAtomic_mem hΓ)

lemma Derivation.toReduction {Γ : Sequent α} (hΓ : ¬Γ.IsAtomic)
    (d : T ⟹! Γ) : Derivations! T (Γ.reduction hΓ) := by
    match H : Γ.chooseNonAtomic hΓ with
    |  .atom a => have := Γ.chooseNonAtomic_property hΓ; simp_all
    | .natom a => have := Γ.chooseNonAtomic_property hΓ; simp_all
    |        ⊤ => simpa [Sequent.reduction_verum H] using Derivations!.nil
    |        ⊥ =>
      suffices T ⟹! List.remove ⊥ Γ by
        simp only [Sequent.reduction_falsum H]
        intro Γ; simp; rintro rfl; assumption
      exact Tait.cut! (φ := ⊥) (Tait.wk! d <| by simp) (by simp [Tait.verum!])
    | φ ⋏ ψ =>
      suffices T ⟹! φ :: List.remove (φ ⋏ ψ) Γ ∧ T ⟹! ψ :: List.remove (φ ⋏ ψ) Γ by
        simp [Sequent.reduction_and H]
        intro Γ; simp
        rintro (rfl | rfl); { exact Tait.wk! this.1 (by simp) }; { exact Tait.wk! this.2 (by simp) }
      have : T ⟹! φ ⋏ ψ :: List.remove (φ ⋏ ψ) Γ := Tait.wk! d
      constructor
      · exact Tait.modusPonens! Entailment.and₁! this
      · exact Tait.modusPonens! Entailment.and₂! this
    | φ ⋎ ψ =>
      suffices T ⟹! φ :: ψ :: List.remove (φ ⋎ ψ) Γ by
        simp [Sequent.reduction_or H]
        intro Γ; simp; rintro rfl
        exact Tait.wk! (by assumption)
      have : T ⟹! φ ⋎ ψ :: List.remove (φ ⋎ ψ) Γ := Tait.wk! d
      apply Tait.cut! (φ := φ ⋎ ψ)
      · exact Tait.wk! this <|
          List.cons_subset_cons _ <| List.subset_cons_of_subset _ <| by simp
      · simp only [DeMorgan.or]
        refine Tait.and! (Tait.em! (φ := φ) (by simp) (by simp)) (Tait.em! (φ := ψ) (by simp) (by simp))

end

abbrev Sequents.Refuted (S : Sequents α) : Prop := ∃ Γ ∈ S, Γ.IsAtomic ∧ ¬Γ.IsClosed

lemma Sequents.Refuted.not_iff {S : Sequents α} : ¬S.Refuted ↔ ∀ Γ ∈ S, Γ.IsAtomic → Γ.IsClosed := by
  simp [Refuted]

instance [DecidableEq α] : DecidablePred (Sequents.Refuted (α := α)) := List.decidableBEx _

def Sequents.reduction [DecidableEq α] (S : Sequents α) : Sequents α :=
  S.flatMap fun Γ ↦ if h : Γ.IsAtomic then [] else Γ.reduction h

lemma Sequent.reduction_sublist [DecidableEq α] {Γ : Sequent α} (hΓ : ¬Γ.IsAtomic) {S : Sequents α}
    (h : Γ ∈ S) : (Γ.reduction hΓ).Sublist S.reduction :=
  List.sublist_flatten_of_mem <| List.mem_map.mpr ⟨Γ, h, by simp_all⟩

def Derivations.ofReduction [DecidableEq α] {S : Sequents α} (hS : ¬S.Refuted)
    (d : Derivations T S.reduction) : Derivations T S := fun Γ h ↦
  if hΓ : Γ.IsAtomic then
    have : Γ.IsClosed := Sequents.Refuted.not_iff.mp hS Γ h hΓ
    Derivation.ofIsClosed this
  else
    Derivation.ofReduction <| d.ofSubset <| (Sequent.reduction_sublist hΓ h).subset

lemma Derivations.toReduction [DecidableEq α] {S : Sequents α}
    (d : Derivations! T S) : Derivations! T S.reduction := fun Γ h ↦ by
  have : ∃ Δ ∈ S, ∃ (h : ¬Δ.IsAtomic), Γ ∈ Sequent.reduction h := by simpa [Sequents.reduction] using h
  rcases this with ⟨Δ, hΔS, hΔ, H⟩
  exact Derivation.toReduction hΔ (d Δ hΔS) Γ H


end LO.Propositional
