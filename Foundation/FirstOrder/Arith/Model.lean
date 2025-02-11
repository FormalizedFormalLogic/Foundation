import Foundation.FirstOrder.Arith.Theory

namespace LO

namespace FirstOrder

namespace Arith
open Language

section

variable {L : Language} [L.ORing]

@[simp] lemma oringEmb_operator_zero_val :
    Semiterm.Operator.Zero.zero.term.lMap (Language.oringEmb : ℒₒᵣ →ᵥ L) = Semiterm.Operator.Zero.zero.term := by
  simp [Semiterm.Operator.Zero.term_eq, Semiterm.lMap_func, Matrix.empty_eq]

@[simp] lemma oringEmb_operator_one_val :
    Semiterm.Operator.One.one.term.lMap (Language.oringEmb : ℒₒᵣ →ᵥ L) = Semiterm.Operator.One.one.term := by
  simp [Semiterm.Operator.One.term_eq, Semiterm.lMap_func, Matrix.empty_eq]

@[simp] lemma oringEmb_operator_add_val :
    Semiterm.Operator.Add.add.term.lMap (Language.oringEmb : ℒₒᵣ →ᵥ L) = Semiterm.Operator.Add.add.term := by
  simp [Semiterm.Operator.Add.term_eq, Semiterm.lMap_func, Matrix.empty_eq]

@[simp] lemma oringEmb_operator_mul_val :
    Semiterm.Operator.Mul.mul.term.lMap (Language.oringEmb : ℒₒᵣ →ᵥ L) = Semiterm.Operator.Mul.mul.term := by
  simp [Semiterm.Operator.Mul.term_eq, Semiterm.lMap_func, Matrix.empty_eq]

@[simp] lemma oringEmb_operator_eq_val :
    .lMap (Language.oringEmb : ℒₒᵣ →ᵥ L) Semiformula.Operator.Eq.eq.sentence = Semiformula.Operator.Eq.eq.sentence := by
  simp [Semiformula.Operator.Eq.sentence_eq, Semiformula.lMap_rel, Matrix.empty_eq]

@[simp] lemma oringEmb_operator_lt_val :
    .lMap (Language.oringEmb : ℒₒᵣ →ᵥ L) Semiformula.Operator.LT.lt.sentence = Semiformula.Operator.LT.lt.sentence := by
  simp [Semiformula.Operator.LT.sentence_eq, Semiformula.lMap_rel, Matrix.empty_eq]

end

section model

section

variable (M : Type*) [ORingStruc M]

instance standardModel : Structure ℒₒᵣ M where
  func := fun _ f =>
    match f with
    | ORing.Func.zero => fun _ => 0
    | ORing.Func.one  => fun _ => 1
    | ORing.Func.add  => fun v => v 0 + v 1
    | ORing.Func.mul  => fun v => v 0 * v 1
  rel := fun _ r =>
    match r with
    | ORing.Rel.eq => fun v => v 0 = v 1
    | ORing.Rel.lt => fun v => v 0 < v 1

instance : Structure.Eq ℒₒᵣ M :=
  ⟨by intro a b; simp[standardModel, Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq, Semiformula.eval_rel]⟩

instance : Structure.Zero ℒₒᵣ M := ⟨rfl⟩

instance : Structure.One ℒₒᵣ M := ⟨rfl⟩

instance : Structure.Add ℒₒᵣ M := ⟨fun _ _ => rfl⟩

instance : Structure.Mul ℒₒᵣ M := ⟨fun _ _ => rfl⟩

instance : Structure.Eq ℒₒᵣ M := ⟨fun _ _ => iff_of_eq rfl⟩

instance : Structure.LT ℒₒᵣ M := ⟨fun _ _ => iff_of_eq rfl⟩

instance : ORing ℒₒᵣ := ORing.mk

lemma standardModel_unique' (s : Structure ℒₒᵣ M)
    (hZero : Structure.Zero ℒₒᵣ M) (hOne : Structure.One ℒₒᵣ M) (hAdd : Structure.Add ℒₒᵣ M) (hMul : Structure.Mul ℒₒᵣ M)
    (hEq : Structure.Eq ℒₒᵣ M) (hLT : Structure.LT ℒₒᵣ M) : s = standardModel M := Structure.ext
  (funext₃ fun k f _ =>
    match k, f with
    | _, Language.Zero.zero => by simp[Matrix.empty_eq]
    | _, Language.One.one   => by simp[Matrix.empty_eq]
    | _, Language.Add.add   => by simp
    | _, Language.Mul.mul   => by simp)
  (funext₃ fun k r _ =>
    match k, r with
    | _, Language.Eq.eq => by simp
    | _, Language.LT.lt => by simp)

lemma standardModel_unique (s : Structure ℒₒᵣ M)
    [hZero : Structure.Zero ℒₒᵣ M] [hOne : Structure.One ℒₒᵣ M] [hAdd : Structure.Add ℒₒᵣ M] [hMul : Structure.Mul ℒₒᵣ M]
    [hEq : Structure.Eq ℒₒᵣ M] [hLT : Structure.LT ℒₒᵣ M] : s = standardModel M :=
  standardModel_unique' M s hZero hOne hAdd hMul hEq hLT

variable {L : Language} [L.ORing] [s : Structure L M]
  [Structure.Zero L M] [Structure.One L M] [Structure.Add L M] [Structure.Mul L M] [Structure.Eq L M] [Structure.LT L M]

lemma standardModel_lMap_oringEmb_eq_standardModel : s.lMap (Language.oringEmb : ℒₒᵣ →ᵥ L) = standardModel M := by
  apply standardModel_unique' M _
  · exact @Structure.Zero.mk ℒₒᵣ M (s.lMap Language.oringEmb) _ _ (by simp [Semiterm.Operator.val, ←Semiterm.val_lMap]; exact Structure.Zero.zero)
  · exact @Structure.One.mk ℒₒᵣ M (s.lMap Language.oringEmb) _ _ (by simp [Semiterm.Operator.val, ←Semiterm.val_lMap]; exact Structure.One.one)
  · exact @Structure.Add.mk ℒₒᵣ M (s.lMap Language.oringEmb) _ _ (fun a b ↦ by simp [Semiterm.Operator.val, ←Semiterm.val_lMap]; exact Structure.Add.add a b)
  · exact @Structure.Mul.mk ℒₒᵣ M (s.lMap Language.oringEmb) _ _ (fun a b ↦ by simp [Semiterm.Operator.val, ←Semiterm.val_lMap]; exact Structure.Mul.mul a b)
  · exact @Structure.Eq.mk ℒₒᵣ M (s.lMap Language.oringEmb) _ (fun a b ↦ by
      simp [Semiformula.Operator.val, ←Semiformula.eval_lMap]; exact Structure.Eq.eq a b)
  · exact @Structure.LT.mk ℒₒᵣ M (s.lMap Language.oringEmb) _ _ (fun a b ↦ by
      simp [Semiformula.Operator.val, ←Semiformula.eval_lMap]; exact Structure.LT.lt a b)

variable {M} {e : Fin n → M} {ε : ξ → M}

@[simp] lemma val_lMap_oringEmb {t : Semiterm ℒₒᵣ ξ n} :
    (t.lMap Language.oringEmb : Semiterm L ξ n).valm M e ε = t.valm M e ε := by
  simp [Semiterm.val_lMap, standardModel_lMap_oringEmb_eq_standardModel]

@[simp] lemma eval_lMap_oringEmb {φ : Semiformula ℒₒᵣ ξ n} :
    Semiformula.Evalm M e ε (.lMap Language.oringEmb φ : Semiformula L ξ n) ↔ Semiformula.Evalm M e ε φ := by
  simp [Semiformula.eval_lMap, standardModel_lMap_oringEmb_eq_standardModel]

end

section

variable {L : Language} [L.ORing]
variable {M : Type*} [ORingStruc M] [s : Structure L M]
  [Structure.Zero L M] [Structure.One L M] [Structure.Add L M] [Structure.Mul L M] [Structure.Eq L M] [Structure.LT L M]

@[simp] lemma modelsTheory_lMap_oringEmb (T : Theory ℒₒᵣ) :
    M ⊧ₘ* (T.lMap oringEmb : Theory L) ↔ M ⊧ₘ* T := by
  simp [modelsTheory_iff]
  constructor
  · intro H φ hp f
    exact eval_lMap_oringEmb.mp <| @H (Semiformula.lMap oringEmb φ) (Set.mem_image_of_mem _ hp) f
  · simp [Theory.lMap]
    intro H φ hp f; exact eval_lMap_oringEmb.mpr (H hp f)

instance [M ⊧ₘ* 𝐈open] : M ⊧ₘ* 𝐏𝐀⁻ := ModelsTheory.of_add_left M 𝐏𝐀⁻ (Theory.indScheme _ Semiformula.Open)

instance [M ⊧ₘ* 𝐈open] : M ⊧ₘ* Theory.indScheme ℒₒᵣ Semiformula.Open :=
  ModelsTheory.of_add_right M 𝐏𝐀⁻ (Theory.indScheme _ Semiformula.Open)

def models_PAMinus_of_models_indH (Γ n) [M ⊧ₘ* 𝐈𝐍𝐃 Γ n] : M ⊧ₘ* 𝐏𝐀⁻ := ModelsTheory.of_add_left M 𝐏𝐀⁻ (Theory.indScheme _ (Arith.Hierarchy Γ n))

def models_indScheme_of_models_indH (Γ n) [M ⊧ₘ* 𝐈𝐍𝐃 Γ n] : M ⊧ₘ* Theory.indScheme ℒₒᵣ (Arith.Hierarchy Γ n) :=
  ModelsTheory.of_add_right M 𝐏𝐀⁻ (Theory.indScheme _ (Arith.Hierarchy Γ n))

instance models_PAMinus_of_models_peano [M ⊧ₘ* 𝐏𝐀] : M ⊧ₘ* 𝐏𝐀⁻ := ModelsTheory.of_add_left M 𝐏𝐀⁻ (Theory.indScheme _ Set.univ)

end

end model

namespace Standard

variable {ξ : Type v} (e : Fin n → ℕ) (ε : ξ → ℕ)

instance models_CobhamR0 : ℕ ⊧ₘ* 𝐑₀ := ⟨by
  intro σ h
  rcases h <;> simp [models_def, ←le_iff_eq_or_lt]
  case equal h =>
    have : ℕ ⊧ₘ* (𝐄𝐐 : Theory ℒₒᵣ) := inferInstance
    exact modelsTheory_iff.mp this h
  case Ω₃ h => exact h⟩

instance models_PAMinus : ℕ ⊧ₘ* 𝐏𝐀⁻ := ⟨by
  intro σ h
  rcases h <;> simp [models_def, ←le_iff_eq_or_lt]
  case addAssoc => intro f; exact add_assoc _ _ _
  case addComm  => intro f; exact add_comm _ _
  case mulAssoc => intro f; exact mul_assoc _ _ _
  case mulComm  => intro f; exact mul_comm _ _
  case addEqOfLt => intro f h; exact ⟨f 1 - f 0, Nat.add_sub_of_le (le_of_lt h)⟩
  case oneLeOfZeroLt => intro n hn; exact hn
  case mulLtMul => rintro f h hl; exact (mul_lt_mul_right hl).mpr h
  case distr => intro f; exact Nat.mul_add _ _ _
  case ltTrans => intro f; exact Nat.lt_trans
  case ltTri => intro f; exact Nat.lt_trichotomy _ _
  case equal h =>
    have : ℕ ⊧ₘ* (𝐄𝐐 : Theory ℒₒᵣ) := inferInstance
    exact modelsTheory_iff.mp this h⟩

lemma models_succInd (φ : Semiformula ℒₒᵣ ℕ 1) : ℕ ⊧ₘ succInd φ := by
  simp[Empty.eq_elim, succInd, models_iff, Matrix.constant_eq_singleton, Matrix.comp_vecCons',
    Semiformula.eval_substs, Semiformula.eval_rew_q Rew.toS, Function.comp]
  intro e hzero hsucc x; induction' x with x ih
  · exact hzero
  · exact hsucc x ih

instance models_iSigma (Γ k) : ℕ ⊧ₘ* 𝐈𝐍𝐃Γ k := by
  simp [Theory.indScheme, models_PAMinus]; rintro _ φ _ rfl; simp [models_succInd]

instance models_iSigmaZero : ℕ ⊧ₘ* 𝐈𝚺₀ := inferInstance

instance models_iSigmaOne : ℕ ⊧ₘ* 𝐈𝚺₁ := inferInstance

instance models_peano : ℕ ⊧ₘ* 𝐏𝐀 := by
  simp [Theory.peano, Theory.indScheme, models_PAMinus]; rintro _ φ _ rfl; simp [models_succInd]

end Standard

section

variable (L : Language.{u}) [ORing L]

structure Cut (M : Type w) [s : Structure L M] where
  domain : Set M
  closedSucc : ∀ x ∈ domain, (‘x. x + 1’).valb s ![x] ∈ domain
  closedLt : ∀ x y : M, Semiformula.Evalb s ![x, y] “x y. x < y” → y ∈ domain → x ∈ domain

structure ClosedCut (M : Type w) [s : Structure L M] extends Structure.ClosedSubset L M where
  closedLt : ∀ x y : M, Semiformula.Evalb s ![x, y] “x y. x < y” → y ∈ domain → x ∈ domain

end

abbrev Theory.TrueArith : Theory ℒₒᵣ := Structure.theory ℒₒᵣ ℕ

notation "𝐓𝐀" => Theory.TrueArith

instance Standard.models_trueArith : ℕ ⊧ₘ* 𝐓𝐀 :=
  modelsTheory_iff.mpr fun {φ} ↦ by simp

variable (T : Theory ℒₒᵣ) [𝐄𝐐 ⪯ T]

lemma oRing_consequence_of (φ : SyntacticFormula ℒₒᵣ) (H : ∀ (M : Type*) [ORingStruc M] [M ⊧ₘ* T], M ⊧ₘ φ) :
    T ⊨ φ := consequence_of T φ fun M _ s _ _ ↦ by
  rcases standardModel_unique M s
  exact H M

end Arith

namespace Theory

open Arith

instance CobhamR0.consistent : Entailment.Consistent 𝐑₀ :=
  Sound.consistent_of_satisfiable ⟨_, Standard.models_CobhamR0⟩

instance Peano.consistent : Entailment.Consistent 𝐏𝐀 :=
  Sound.consistent_of_satisfiable ⟨_, Standard.models_peano⟩

end Theory

end FirstOrder

end LO
