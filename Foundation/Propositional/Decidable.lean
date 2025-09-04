import Foundation.Propositional.ClassicalSemantics.Basic
import Foundation.Propositional.Tait.Calculus
import Foundation.Propositional.ClassicalSemantics.Tait
import Mathlib.Algebra.Order.BigOperators.Group.List

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
  List.le_sum_of_mem (List.mem_map_of_mem h)

lemma weight_remove [DecidableEq α] (Γ : Sequent α) (φ) :
    weight (Γ.remove φ) = Γ.weight - Γ.count φ * φ.weight := by
  suffices weight (Γ.remove φ) + Γ.count φ * φ.weight = Γ.weight from Nat.eq_sub_of_add_eq this
  induction Γ
  case nil => simp
  case cons ψ Γ ih =>
    by_cases e : φ = ψ
    · rcases e
      simp [add_mul, ←add_assoc, add_comm φ.weight, ih]
    · simp [Γ.remove_cons_of_ne (Ne.symm e), add_assoc, ih, List.count_cons_of_ne (Ne.symm e)]

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

def weight (S : Sequents α) : ℕ := (S.map Sequent.weight).max?.casesOn 0 .succ

variable {S S₁ S₂ : Sequents α}

@[simp] lemma weight_nil : weight ([] : Sequents α) = 0 := rfl

@[simp] lemma weight_eq_zero_iff_eq_nil : weight S = 0 ↔ S = [] := by
  cases h : (List.map Sequent.weight S).max? <;> simp [weight, h]
  · simpa using h
  · rintro rfl; simp at h

lemma weight_eq_succ_iff {S : Sequents α} :
    S.weight = n + 1 ↔ ∃ Γ ∈ S, Γ.weight = n ∧ ∀ Δ ∈ S, Δ.weight ≤ n := by
  match h : (List.map Sequent.weight S).max? with
  |   .none => simp [show S = [] by simpa using h]
  | .some a =>
    have : (∃ Γ ∈ S, Γ.weight = a) ∧ ∀ Δ ∈ S, Δ.weight ≤ a := by simpa using List.max?_eq_some_iff'.mp h
    rcases this with ⟨⟨Γ, hΓS, rfl⟩, hS⟩
    have : S.weight = Γ.weight + 1 := by simp [Sequents.weight, h]
    constructor
    · intro e
      have : n = Γ.weight := by simp [e] at this; simp_all
      rcases this
      exact ⟨Γ, by assumption, rfl, hS⟩
    · rintro ⟨Γ', _, rfl, H⟩
      have : Γ.weight ≤ Γ'.weight := H Γ (by assumption)
      have : Γ'.weight ≤ Γ.weight := hS Γ' (by assumption)
      simp [weight, h]; exact Nat.le_antisymm (by assumption) (by assumption)

lemma weight_eq_of_mem_max (hm : m ∈ (S.map Sequent.weight).max?) :
    S.weight = m + 1 := by simp [weight, show (S.map Sequent.weight).max? = .some m from hm]

lemma weight_lt_weight_of {Γ} (hΓ : Γ ∈ S₂) (h : ∀ Δ ∈ S₁, Δ.weight < Γ.weight) : S₁.weight < S₂.weight := by
  match hS₁ : S₁.weight, hS₂ : S₂.weight with
  |      _,      0 => rcases weight_eq_zero_iff_eq_nil.mp hS₂; simp_all
  |      0,  _ + 1 => simp
  | n₁ + 1, n₂ + 1 =>
    rcases weight_eq_succ_iff.mp hS₁ with ⟨Γ₁, hΓS₁, rfl, H₁⟩
    rcases weight_eq_succ_iff.mp hS₂ with ⟨Γ₂, hΓS₂, rfl, H₂⟩
    have : Γ₁.weight < Γ₂.weight := lt_of_lt_of_le (h Γ₁ hΓS₁) (H₂ Γ hΓ)
    simpa

end Sequents

abbrev Derivations (T : Theory α) (S : Sequents α) := ∀ Γ ∈ S, T ⇒ Γ

abbrev Derivations! (T : Theory α) (S : Sequents α) : Prop := ∀ Γ ∈ S, T ⇒! Γ

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

def Derivation.ofIsClosed [DecidableEq α] {T : Theory α} {Γ : Sequent α} (h : Γ.IsClosed) : T ⇒ Γ :=
  let ⟨φ, h, hn⟩ := h.choose
  em (φ := φ) h hn

abbrev Sequent.IsOpen (Γ : Sequent α) : Prop := Γ.IsAtomic ∧ ¬Γ.IsClosed

instance [DecidableEq α] : DecidablePred (Sequent.IsOpen (α := α)) := inferInstance

lemma Sequent.IsOpen.not_tautology (h : Γ.IsOpen) : ¬Γ.IsTautology :=
  Sequent.notTautology_iff.mpr ⟨fun a ↦ .atom a ∉ Γ, fun φ hφ ↦ by
    rcases show φ.IsAtomic from h.1 φ hφ
    case atom a =>
      simp [hφ]
    case natom a =>
      suffices NNFormula.atom a ∉ Γ by simpa
      intro ha
      exact h.2 ⟨.atom a, by simp [*]⟩⟩

def Sequents.IsClosed (S : Sequents α) : Prop := ∀ Γ ∈ S, Γ.IsClosed

instance [DecidableEq α] : DecidablePred (Sequents.IsClosed (α := α)) := List.decidableBAll Sequent.IsClosed

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
    (d : Derivations T (Γ.reduction hΓ)) : T ⇒ Γ :=
    match H : Γ.chooseNonAtomic hΓ with
    |  .atom a => by have := Γ.chooseNonAtomic_property hΓ; simp_all
    | .natom a => by have := Γ.chooseNonAtomic_property hΓ; simp_all
    |        ⊤ => verum' (by simpa [H] using Sequent.chooseNonAtomic_mem hΓ)
    |        ⊥ =>
      have : T ⇒ Γ.remove ⊥ := d (Γ.remove ⊥) (by simp [Sequent.reduction_falsum H])
      this.wk (by simp)
    |    φ ⋏ ψ =>
      have : T ⇒ (Γ.remove (φ ⋏ ψ)).concat φ := d _ (by simp [Sequent.reduction_and H])
      have dφ : T ⇒ φ :: Γ.remove (φ ⋏ ψ) := this.wk (by simp)
      have : T ⇒ (Γ.remove (φ ⋏ ψ)).concat ψ := d _ (by simp [Sequent.reduction_and H])
      have dψ : T ⇒ ψ :: Γ.remove (φ ⋏ ψ) := this.wk (by simp)
      dφ.and dψ |>.wk (by simpa [H] using Sequent.chooseNonAtomic_mem hΓ)
    |    φ ⋎ ψ =>
      have : T ⇒ ((Γ.remove (φ ⋎ ψ)).concat φ).concat ψ := d _ (by simp [Sequent.reduction_or H])
      have : T ⇒ φ :: ψ :: Γ.remove (φ ⋎ ψ) := this.wk <| by simp
      this.or |>.wk (by simpa [H] using Sequent.chooseNonAtomic_mem hΓ)

lemma Derivation.toReduction {Γ : Sequent α} (hΓ : ¬Γ.IsAtomic)
    (d : T ⇒! Γ) : Derivations! T (Γ.reduction hΓ) := by
    match H : Γ.chooseNonAtomic hΓ with
    |  .atom a => have := Γ.chooseNonAtomic_property hΓ; simp_all
    | .natom a => have := Γ.chooseNonAtomic_property hΓ; simp_all
    |        ⊤ => simpa [Sequent.reduction_verum H] using Derivations!.nil
    |        ⊥ =>
      suffices T ⇒! List.remove ⊥ Γ by
        simp only [Sequent.reduction_falsum H]
        intro Γ; simp; rintro rfl; assumption
      exact ⟨Tait.cutFalsum <| (d.get).wk <| by simp⟩
    | φ ⋏ ψ =>
      suffices T ⇒! φ :: List.remove (φ ⋏ ψ) Γ ∧ T ⇒! ψ :: List.remove (φ ⋏ ψ) Γ by
        simp [Sequent.reduction_and H]
        intro Γ; simp
        rintro (rfl | rfl); { exact Tait.wk! this.1 (by simp) }; { exact Tait.wk! this.2 (by simp) }
      have : T ⇒! φ ⋏ ψ :: List.remove (φ ⋏ ψ) Γ := Tait.wk! d
      constructor
      · exact Tait.modusPonens! Entailment.and₁! this
      · exact Tait.modusPonens! Entailment.and₂! this
    | φ ⋎ ψ =>
      suffices T ⇒! φ :: ψ :: List.remove (φ ⋎ ψ) Γ by
        simp [Sequent.reduction_or H]
        intro Γ; simp; rintro rfl
        exact Tait.wk! (by assumption)
      exact ⟨Tait.orReversion <| (d.get).wk <| by simp⟩

end

abbrev Sequents.Refuted (S : Sequents α) : Prop := ∃ Γ ∈ S, Γ.IsOpen

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

lemma Sequents.reduction_weight_lt_weight [DecidableEq α] (S : Sequents α) (h : S ≠ []) : S.reduction.weight < S.weight := by
  match hS : S.weight with
  |     0 => simp at hS; contradiction
  | n + 1 =>
    rcases Sequents.weight_eq_succ_iff.mp hS with ⟨Γ, hΓS, rfl, HΓ⟩
    have : S.reduction.weight < S.weight :=
      Sequents.weight_lt_weight_of hΓS (S₁ := S.reduction) <| by
        intro Δ hΔ
        have : ∃ Ξ ∈ S, ∃ (h : ¬Ξ.IsAtomic), Δ ∈ Sequent.reduction h := by simpa [reduction] using hΔ
        rcases this with ⟨Ξ, hΞS, hΞ, hΔΞ⟩
        have : Δ.weight < Ξ.weight := Sequent.weight_lt_weight_of_mem_reduction hΔΞ
        exact lt_of_lt_of_le this (HΓ Ξ hΞS)
    simpa [hS] using this

inductive Derivations.Dec : Sequents α → Type _ where
  |   provable : Derivations ∅ S → Derivations.Dec S
  | unprovable (Γ : Sequent α) : Γ ∈ S → ¬Sequent.IsTautology Γ → Derivations.Dec S

def Derivations.Dec.ofReduction [DecidableEq α] {S : Sequents α} (hS : ¬S.Refuted) : Derivations.Dec S.reduction → Derivations.Dec S
  |             .provable d => .provable <| LO.Propositional.Derivations.ofReduction hS d
  | .unprovable Γ hΓSr hΓNT =>
    let Δ := S.choose (fun Δ ↦ ∃ h : ¬Δ.IsAtomic, Γ ∈ Sequent.reduction h) (by simpa [Sequents.reduction] using hΓSr)
    .unprovable Δ (S.choose_mem _ _) (by
      intro hΔT
      have : ∃ h : ¬Δ.IsAtomic, Γ ∈ Sequent.reduction h := S.choose_property (fun Δ ↦ ∃ h : ¬Δ.IsAtomic, Γ ∈ Sequent.reduction h) _
      rcases this with ⟨hΔ, hΓr⟩
      have : Γ.IsTautology := Derivation.toReduction hΔ hΔT Γ hΓr
      contradiction)

def Sequents.dec [DecidableEq α] : (S : Sequents α) → Derivations.Dec S := fun S ↦
  if hS : S = [] then
    .provable (by rw [hS]; exact Derivations.nil)
  else if h : S.Refuted then
    let ⟨Γ, hΓS, hΓ⟩ := S.chooseX Sequent.IsOpen h
    .unprovable Γ hΓS (Sequent.IsOpen.not_tautology hΓ)
  else
    S.reduction.dec.ofReduction h
  termination_by S => S.weight
  decreasing_by
    exact S.reduction_weight_lt_weight hS

instance [DecidableEq α] : DecidablePred fun Γ : Sequent α ↦ Γ.IsTautology := fun Γ ↦
  match Sequents.dec [Γ] with
  |           .provable d => .isTrue ⟨d Γ (by simp)⟩
  | .unprovable Δ hΔ hΔNT => .isFalse <| by
    have : Δ = Γ := by simpa using hΔ
    rcases this; assumption

instance [DecidableEq α] : DecidablePred fun φ : NNFormula α ↦ φ.IsTautology := fun _ ↦ inferInstance

end LO.Propositional
