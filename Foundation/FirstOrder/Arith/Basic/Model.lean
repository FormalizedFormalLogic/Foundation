import Foundation.FirstOrder.Arith.Basic.ORingStruc

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
    |  ORing.Func.one => fun _ => 1
    |  ORing.Func.add => fun v => v 0 + v 1
    |  ORing.Func.mul => fun v => v 0 * v 1
  rel := fun _ r =>
    match r with
    | ORing.Rel.eq => fun v => v 0 = v 1
    | ORing.Rel.lt => fun v => v 0 < v 1

instance : Structure.Eq ℒₒᵣ M :=
  ⟨by intro a b; simp [standardModel, Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq, Semiformula.eval_rel]⟩

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
    | _, Language.Zero.zero => by simp [Matrix.empty_eq]
    | _,   Language.One.one => by simp [Matrix.empty_eq]
    | _,   Language.Add.add => by simp
    | _,   Language.Mul.mul => by simp)
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
  · exact @Structure.Zero.mk ℒₒᵣ M (s.lMap Language.oringEmb) _ _ (by simpa [Semiterm.Operator.val, ←Semiterm.val_lMap] using Structure.Zero.zero)
  · exact @Structure.One.mk ℒₒᵣ M (s.lMap Language.oringEmb) _ _ (by simpa [Semiterm.Operator.val, ←Semiterm.val_lMap] using Structure.One.one)
  · exact @Structure.Add.mk ℒₒᵣ M (s.lMap Language.oringEmb) _ _ (fun a b ↦ by simpa [Semiterm.Operator.val, ←Semiterm.val_lMap] using Structure.Add.add a b)
  · exact @Structure.Mul.mk ℒₒᵣ M (s.lMap Language.oringEmb) _ _ (fun a b ↦ by simpa [Semiterm.Operator.val, ←Semiterm.val_lMap] using Structure.Mul.mul a b)
  · exact @Structure.Eq.mk ℒₒᵣ M (s.lMap Language.oringEmb) _ (fun a b ↦ by
      simpa [Semiformula.Operator.val, ←Semiformula.eval_lMap] using Structure.Eq.eq a b)
  · exact @Structure.LT.mk ℒₒᵣ M (s.lMap Language.oringEmb) _ _ (fun a b ↦ by
      simpa [Semiformula.Operator.val, ←Semiformula.eval_lMap] using Structure.LT.lt a b)

variable {M} {e : Fin n → M} {ε : ξ → M}

@[simp] lemma val_lMap_oringEmb {t : Semiterm ℒₒᵣ ξ n} :
    (t.lMap Language.oringEmb : Semiterm L ξ n).valm M e ε = t.valm M e ε := by
  simp [Semiterm.val_lMap, standardModel_lMap_oringEmb_eq_standardModel]

@[simp] lemma eval_lMap_oringEmb {φ : Semiformula ℒₒᵣ ξ n} :
    Semiformula.Evalm M e ε (.lMap Language.oringEmb φ : Semiformula L ξ n) ↔ Semiformula.Evalm M e ε φ := by
  simp [Semiformula.eval_lMap, standardModel_lMap_oringEmb_eq_standardModel]

end

section

variable {M : Type*} [ORingStruc M]

@[simp] lemma modelsTheory_lMap_oringEmb
    {L : Language} [L.ORing] [Structure L M]
    [Structure.Zero L M] [Structure.One L M] [Structure.Add L M] [Structure.Mul L M]
    [Structure.Eq L M] [Structure.LT L M]
    (T : Theory ℒₒᵣ) :
    M ⊧ₘ* (T.lMap oringEmb : Theory L) ↔ M ⊧ₘ* T := by
  simp only [modelsTheory_iff]
  constructor
  · intro H φ hp f
    exact eval_lMap_oringEmb.mp <| @H (Semiformula.lMap oringEmb φ) (Set.mem_image_of_mem _ hp) f
  · simp only [Theory.lMap, Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro H φ hp f; exact eval_lMap_oringEmb.mpr (H hp f)

/-
instance [M ⊧ₘ* 𝐈open] : M ⊧ₘ* 𝐏𝐀⁻ := ModelsTheory.of_add_left M 𝐏𝐀⁻ (Theory.InductionScheme _ Semiformula.Open)

instance [M ⊧ₘ* 𝐈open] : M ⊧ₘ* Theory.InductionScheme ℒₒᵣ Semiformula.Open :=
  ModelsTheory.of_add_right M 𝐏𝐀⁻ (Theory.InductionScheme _ Semiformula.Open)

def models_PeanoMinus_of_models_InductionOnHierarchy (Γ n) [M ⊧ₘ* 𝐈𝐍𝐃 Γ n] : M ⊧ₘ* 𝐏𝐀⁻ := ModelsTheory.of_add_left M 𝐏𝐀⁻ (Theory.InductionScheme _ (Arith.Hierarchy Γ n))

def models_InductionScheme_of_models_InductionOnHierarchy (Γ n) [M ⊧ₘ* 𝐈𝐍𝐃 Γ n] : M ⊧ₘ* Theory.InductionScheme ℒₒᵣ (Arith.Hierarchy Γ n) :=
  ModelsTheory.of_add_right M 𝐏𝐀⁻ (Theory.InductionScheme _ (Arith.Hierarchy Γ n))

instance models_PeanoMinus_of_models_Peano [M ⊧ₘ* 𝐏𝐀] : M ⊧ₘ* 𝐏𝐀⁻ := ModelsTheory.of_add_left M 𝐏𝐀⁻ (Theory.InductionScheme _ Set.univ)

-/

end

end model

/-
namespace Standard

variable {ξ : Type v} (e : Fin n → ℕ) (ε : ξ → ℕ)

set_option linter.flexible false in
lemma models_succInd (φ : Semiformula ℒₒᵣ ℕ 1) : ℕ ⊧ₘ succInd φ := by
  simp [Empty.eq_elim, succInd, models_iff, Matrix.constant_eq_singleton, Matrix.comp_vecCons',
    Semiformula.eval_substs, Semiformula.eval_rew_q Rew.toS, Function.comp]
  intro e hzero hsucc x; induction' x with x ih
  · exact hzero
  · exact hsucc x ih

set_option linter.flexible false in
instance models_ISigma (Γ k) : ℕ ⊧ₘ* 𝐈𝐍𝐃Γ k := by
  simp [Theory.InductionScheme, models_PeanoMinus]; rintro _ φ _ rfl; simp [models_succInd]

instance models_ISigmaZero : ℕ ⊧ₘ* 𝐈𝚺₀ := inferInstance

instance models_ISigmaOne : ℕ ⊧ₘ* 𝐈𝚺₁ := inferInstance

set_option linter.flexible false in
instance models_Peano : ℕ ⊧ₘ* 𝐏𝐀 := by
  simp [Theory.Peano, Theory.InductionScheme, models_PeanoMinus]; rintro _ φ _ rfl; simp [models_succInd]

end Standard

-/

section

variable (L : Language.{u}) [ORing L]

structure Cut (M : Type w) [s : Structure L M] where
  domain : Set M
  closedSucc : ∀ x ∈ domain, (‘x. x + 1’).valb s ![x] ∈ domain
  closedLt : ∀ x y : M, Semiformula.Evalb s ![x, y] “x y. x < y” → y ∈ domain → x ∈ domain

structure ClosedCut (M : Type w) [s : Structure L M] extends Structure.ClosedSubset L M where
  closedLt : ∀ x y : M, Semiformula.Evalb s ![x, y] “x y. x < y” → y ∈ domain → x ∈ domain

end

lemma oRing_consequence_of (T : Theory ℒₒᵣ) [𝐄𝐐 ⪯ T] (φ : SyntacticFormula ℒₒᵣ) (H : ∀ (M : Type*) [ORingStruc M] [M ⊧ₘ* T], M ⊧ₘ φ) :
    T ⊨ φ := consequence_of T φ fun M _ s _ _ ↦ by
  rcases standardModel_unique M s
  exact H M

lemma oRing_provable_of (T : Theory ℒₒᵣ) [𝐄𝐐 ⪯ T] (φ : SyntacticFormula ℒₒᵣ) (H : ∀ (M : Type*) [ORingStruc M] [M ⊧ₘ* T], M ⊧ₘ φ) :
    T ⊢! φ := complete <| oRing_consequence_of _ _ H

lemma oRing_provable₀_of (T : Theory ℒₒᵣ) [𝐄𝐐 ⪯ T] (σ : Sentence ℒₒᵣ) (H : ∀ (M : Type*) [ORingStruc M] [M ⊧ₘ* T], M ⊧ₘ₀ σ) :
    T ⊢!. σ := complete (T := T) <| oRing_consequence_of _ _ H

lemma oRing_weakerThan_of (T S : Theory ℒₒᵣ) [𝐄𝐐 ⪯ S]
    (H : ∀ (M : Type*)
           [ORingStruc M]
           [M ⊧ₘ* S],
           M ⊧ₘ* T) : T ⪯ S :=
  Entailment.weakerThan_iff.mpr fun h ↦ complete <| oRing_consequence_of _ _ fun M _ _ ↦ sound! h (H M)

end Arith

namespace Theory

open Arith

/-

instance Peano.consistent : Entailment.Consistent 𝐏𝐀 :=
  Sound.consistent_of_satisfiable ⟨_, inferInstanceAs (ℕ ⊧ₘ* 𝐏𝐀)⟩

instance TrueArith.consistent : Entailment.Consistent 𝐓𝐀 :=
  Sound.consistent_of_satisfiable ⟨_, inferInstanceAs (ℕ ⊧ₘ* 𝐓𝐀)⟩

-/

end Theory

end FirstOrder

end LO
