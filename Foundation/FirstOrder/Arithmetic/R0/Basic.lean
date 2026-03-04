module

public import Foundation.FirstOrder.Arithmetic.Basic

@[expose] public section
/-!
# Cobham's theory $\mathsf{R_0}$

-/

noncomputable section

namespace LO.FirstOrder.Arithmetic

inductive R0 : ArithmeticTheory
  | equal : ∀ φ ∈ 𝗘𝗤, R0 φ
  | Ω₁ (n m : ℕ) : R0 “↑n + ↑m = ↑(n + m)”
  | Ω₂ (n m : ℕ) : R0 “↑n * ↑m = ↑(n * m)”
  | Ω₃ (n m : ℕ) : n ≠ m → R0 “↑n ≠ ↑m”
  | Ω₄ (n : ℕ) : R0 “∀ x, x < ↑n ↔ ⋁ i < n, x = ↑i”

notation "𝗥₀" => R0

namespace R0

instance : 𝗘𝗤 ⪯ 𝗥₀ := Entailment.WeakerThan.ofSubset <| fun φ hp ↦ R0.equal φ hp

instance : ℕ ⊧ₘ* 𝗥₀ := ⟨by
  intro σ h
  rcases h <;> try { simp [models_iff]; done }
  case equal h =>
    have : ℕ ⊧ₘ* (𝗘𝗤 : ArithmeticTheory) := inferInstance
    simpa [models_iff] using modelsTheory_iff.mp this h
  case Ω₃ h =>
    simpa [models_iff, ←le_iff_eq_or_lt] using h⟩

end R0

section model

variable {M : Type*} [ORingStructure M] [M ⊧ₘ* 𝗥₀]

open Language ORingStructure

lemma numeral_add_numeral (n m : ℕ) : (numeral n : M) + numeral m = numeral (n + m) := by
  simpa [models_iff] using ModelsTheory.models M (R0.Ω₁ n m)

lemma numeral_mul_numeral (n m : ℕ) : (numeral n : M) * numeral m = numeral (n * m) := by
  simpa [models_iff] using ModelsTheory.models M (R0.Ω₂ n m)

lemma numeral_ne_numeral_of_ne {n m : ℕ} (h : n ≠ m) : (numeral n : M) ≠ numeral m := by
  simpa [models_iff] using ModelsTheory.models M (R0.Ω₃ n m h)

lemma lt_numeral_iff {x : M} {n : ℕ} : x < numeral n ↔ ∃ i : Fin n, x = numeral i := by
  have := by simpa [models_iff] using ModelsTheory.models M (R0.Ω₄ n)
  constructor
  · intro hx
    rcases (this x).mp hx with ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, by simp⟩
  · rintro ⟨i, rfl⟩
    exact (this (numeral i)).mpr ⟨i, by simp, rfl⟩

@[simp] lemma numeral_inj_iff {n m : ℕ} : (numeral n : M) = numeral m ↔ n = m :=
  ⟨by contrapose; exact numeral_ne_numeral_of_ne, by rintro rfl; rfl⟩

@[simp] lemma numeral_lt_numeral_iff : (numeral n : M) < numeral m ↔ n < m :=
  ⟨by contrapose
      intro h H
      rcases lt_numeral_iff.mp H with ⟨i, hi⟩
      rcases numeral_inj_iff.mp hi
      exact (lt_self_iff_false m).mp (lt_of_le_of_lt (Nat.le_of_not_gt h) i.prop),
   fun h ↦ lt_numeral_iff.mpr ⟨⟨n, h⟩, by simp⟩⟩

open Hierarchy

lemma val_numeral {n} : ∀ (t : ArithmeticSemiterm ξ n),
    ∀ v f, Semiterm.valm M (fun x ↦ numeral (v x)) (fun x ↦ numeral (f x)) t = numeral (Semiterm.valm ℕ v f t)
  | #_,                                 _, _ => by simp
  | &x,                                 _, _ => by simp
  | Semiterm.func Language.Zero.zero _, e, f => by simp
  | Semiterm.func Language.One.one _,   e, f => by simp
  | Semiterm.func Language.Add.add v,   e, f => by simp [Semiterm.val_func, val_numeral (v 0), val_numeral (v 1), numeral_add_numeral]
  | Semiterm.func Language.Mul.mul v,   e, f => by simp [Semiterm.val_func, val_numeral (v 0), val_numeral (v 1), numeral_mul_numeral]

lemma bold_sigma_one_completeness {n} {φ : ArithmeticSemiformula ξ n} (hp : Hierarchy 𝚺 1 φ) {e f} :
    Semiformula.Evalm ℕ e f φ → Semiformula.Evalm M (fun x ↦ numeral (e x)) (fun x ↦ numeral (f x)) φ := by
  revert e
  apply sigma₁_induction' hp
  case hVerum => simp
  case hFalsum => simp
  case hEQ => intro n t₁ t₂ e; simp [val_numeral]
  case hNEQ => intro n t₁ t₂ e; simp [val_numeral]
  case hLT => intro n t₁ t₂ e; simp [val_numeral]
  case hNLT => intro n t₁ t₂ e; simp [val_numeral]
  case hAnd =>
    simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq, and_imp]
    intro n φ ψ _ _ ihp ihq e hp hq
    exact ⟨ihp hp, ihq hq⟩
  case hOr =>
    simp only [LogicalConnective.HomClass.map_or, LogicalConnective.Prop.or_eq]
    rintro n φ ψ _ _ ihp ihq e (hp | hq)
    · left; exact ihp hp
    · right; exact ihq hq
  case hBall =>
    simp only [Semiformula.eval_ball, Nat.succ_eq_add_one, Semiformula.eval_operator_two,
      Semiterm.val_bvar, Matrix.cons_val_zero, Semiterm.val_bShift, Structure.LT.lt, val_numeral]
    intro n t φ _ ihp e hp x hx
    rcases lt_numeral_iff.mp hx with ⟨x, rfl⟩
    simpa [Matrix.comp_vecCons'] using ihp (hp x (by simp))
  case hExs =>
    simp only [Semiformula.eval_ex, Nat.succ_eq_add_one, forall_exists_index]
    intro n φ _ ihp e x hp
    exact ⟨numeral x, by simpa [Matrix.comp_vecCons'] using ihp hp⟩

lemma R0.model_complete {σ : ArithmeticSentence} (hσ : Hierarchy 𝚺 1 σ) :
    ℕ ⊧ₘ σ → M ⊧ₘ σ := by
  suffices Semiformula.Evalbm ℕ ![] σ → Semiformula.Evalbm M ![] σ by simpa [models_iff]
  intro h
  simpa [Matrix.empty_eq, Empty.eq_elim] using bold_sigma_one_completeness hσ h

variable (M)

lemma nat_extention_sigmaOne {σ : ArithmeticSentence} (hσ : Hierarchy 𝚺 1 σ) :
    ℕ ⊧ₘ σ → M ⊧ₘ σ := fun h ↦ by
  simpa [Matrix.empty_eq] using R0.model_complete (M := M) hσ h

lemma nat_extention_piOne {σ : ArithmeticSentence} (hσ : Hierarchy 𝚷 1 σ) :
    M ⊧ₘ σ → ℕ ⊧ₘ σ := by
  contrapose
  simpa using nat_extention_sigmaOne M (σ := ∼σ) (by simpa using hσ)

variable {M}

lemma bold_sigma_one_completeness' {n} {σ : ArithmeticSemisentence n} (hσ : Hierarchy 𝚺 1 σ) {e} :
    Semiformula.Evalbm ℕ e σ → Semiformula.Evalbm M (fun x ↦ numeral (e x)) σ := fun h ↦ by
  simpa [Empty.eq_elim] using bold_sigma_one_completeness (M := M) (φ := σ) hσ (f := Empty.elim) (e := e) h

instance consistent : Entailment.Consistent 𝗥₀ :=
  Sound.consistent_of_satisfiable ⟨_, inferInstanceAs (ℕ ⊧ₘ* 𝗥₀)⟩

end model

variable {T : ArithmeticTheory} [𝗥₀ ⪯ T]

theorem sigma_one_completeness {σ : ArithmeticSentence} (hσ : Hierarchy 𝚺 1 σ) :
    ℕ ⊧ₘ σ → T ⊢ σ := fun H =>
  haveI : 𝗘𝗤 ⪯ T := Entailment.WeakerThan.trans (𝓣 := 𝗥₀) inferInstance inferInstance
  provable_of_models.{0} _ _ <| fun M _ _ ↦ by
    haveI : M ⊧ₘ* 𝗥₀ := ModelsTheory.of_provably_subtheory M 𝗥₀ T inferInstance
    exact R0.model_complete hσ H

open Classical in
theorem sigma_one_completeness_iff [T.SoundOnHierarchy 𝚺 1] {σ : ArithmeticSentence} (hσ : Hierarchy 𝚺 1 σ) :
    ℕ ⊧ₘ σ ↔ T ⊢ σ :=
  haveI : 𝗥₀ ⪯ T := Entailment.WeakerThan.trans (𝓣 := T) inferInstance inferInstance
  ⟨fun h ↦ sigma_one_completeness hσ h, fun h ↦ T.soundOnHierarchy 𝚺 1 h (by simp [hσ])⟩

/-!
## Unprovable theorems of $\mathsf{R}_0$

$\omega + 1$ (the structure of order type $\omega + 1$) is a models of $\mathsf{R}_0$.
-/

/-! ω + 1 models 𝗥₀ -/
namespace R0.Countermodel

def OmegaAddOne := Option ℕ

namespace OmegaAddOne

instance : NatCast OmegaAddOne := ⟨fun i ↦ .some i⟩

instance (n : ℕ) : OfNat OmegaAddOne n := ⟨.some n⟩

instance : Top OmegaAddOne := ⟨.none⟩

instance : ORingStructure OmegaAddOne where
  add a b :=
    match a, b with
    | .some i, .some j => i + j
    |   .none,       _ => 0
    |       _,   .none => 0
  mul a b :=
    match a, b with
    | .some i, .some j => (i * j)
    |   .none,       _ => 0
    |       _,   .none => 0
  lt a b :=
    match a, b with
    | .some i, .some j => i < j
    |   .none,       _ => False
    | .some _,   .none => True

@[simp] lemma coe_zero : (↑(0 : ℕ) : OmegaAddOne) = 0 := rfl

@[simp] lemma coe_one : (↑(1 : ℕ) : OmegaAddOne) = 1 := rfl

@[simp] lemma coe_add (a b : ℕ) : ↑(a + b) = ((↑a + ↑b) : OmegaAddOne) := rfl

@[simp] lemma coe_mul (a b : ℕ) : ↑(a * b) = ((↑a * ↑b) : OmegaAddOne) := rfl

@[simp] lemma lt_coe_iff (n m : ℕ) : (n : OmegaAddOne) < (m : OmegaAddOne) ↔ n < m := by rfl

@[simp] lemma not_top_lt (n : ℕ) : ¬⊤ < (n : OmegaAddOne) := by rintro ⟨⟩

@[simp] lemma lt_top (n : ℕ) : (n : OmegaAddOne) < ⊤ := by trivial

@[simp] lemma top_add_zero : (⊤ : OmegaAddOne) + 0 = 0 := by rfl

lemma exists_add_zero_ne_self : ∃ x : OmegaAddOne, x + 0 ≠ x :=
  ⟨⊤, by simp⟩

@[simp] lemma numeral_eq (n : ℕ) : (ORingStructure.numeral n : OmegaAddOne) = n :=
  match n with
  |     0 => rfl
  |     1 => rfl
  | n + 2 => by simp [ORingStructure.numeral, numeral_eq (n + 1)]; rfl

@[simp] lemma coe_inj_iff (n m : ℕ) : (↑n : OmegaAddOne) = (↑m : OmegaAddOne) ↔ n = m := Option.some_inj

def cases' {P : OmegaAddOne → Sort*}
    (nat : (n : ℕ) → P n)
    (top : P ⊤) : ∀ x : OmegaAddOne, P x
  | .some n => nat n
  |   .none => top

set_option linter.flexible false in
instance : OmegaAddOne ⊧ₘ* 𝗥₀ := ⟨by
  intro σ h
  rcases h <;> simp [models_iff]
  case equal h =>
    have : OmegaAddOne ⊧ₘ* (𝗘𝗤 : ArithmeticTheory) := inferInstance
    exact modelsTheory_iff.mp this h
  case Ω₃ h => exact h
  case Ω₄ n =>
    intro x
    cases x using cases' <;> simp⟩

end OmegaAddOne

end Countermodel

lemma unprovable_addZero : 𝗥₀ ⊬ “∀ x, x + 0 = x” :=
  unprovable_of_countermodel (M := Countermodel.OmegaAddOne) <| by
    simpa [models_iff] using Countermodel.OmegaAddOne.exists_add_zero_ne_self

end R0

end LO.FirstOrder.Arithmetic

end
