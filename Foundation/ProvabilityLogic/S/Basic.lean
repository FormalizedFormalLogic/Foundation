import Foundation.Modal.Logic.WellKnown
import Foundation.Modal.Logic.Extension
import Foundation.ProvabilityLogic.GL.Completeness
import Foundation.ProvabilityLogic.Soundness
import Foundation.Incompleteness.Arith.Second


namespace LO.Modal

open Logic

protected abbrev Logic.S := addQuasiNormal Logic.GL (Axioms.T (.atom 0))

private inductive Logic.S' : Logic
  | mem_GL {φ} : φ ∈ Logic.GL → Logic.S' φ
  | axiomT (φ) : Logic.S' (Axioms.T φ)
  | mdp  {φ ψ} : Logic.S' (φ ➝ ψ) → Logic.S' φ → Logic.S' ψ

private lemma Logic.eq_S_S' : Logic.S = Logic.S' := by
  ext φ;
  constructor;
  . intro h;
    induction h with
    | mem₁ h => exact Logic.S'.mem_GL h;
    | mem₂ h => subst h; exact Logic.S'.axiomT (.atom 0);
    | mdp _ _ ihφψ ihφ => exact Logic.S'.mdp ihφψ ihφ;
    | @subst φ s hφ ihφ =>
      clear hφ;
      induction ihφ with
      | mem_GL h =>
        apply Logic.S'.mem_GL;
        exact Logic.subst h;
      | axiomT _ => apply Logic.S'.axiomT;
      | mdp _ _ ihφψ ihφ =>
        simp at ihφψ;
        apply Logic.S'.mdp ihφψ ihφ;
  . intro h;
    induction h with
    | mem_GL h => exact sumQuasiNormal.mem₁ h;
    | mdp _ _ ihφψ ihφ => exact sumQuasiNormal.mdp ihφψ ihφ;
    | axiomT φ =>
      exact sumQuasiNormal.subst (φ := Axioms.T (.atom 0)) (s := λ _ => φ) $ by
        apply Logic.sumQuasiNormal.mem₂;
        simp;

-- TODO: Remove `eq_S_S'`?
protected def Logic.S.rec'
  {motive : (φ : Formula ℕ) → φ ∈ Logic.S → Prop}
  (mem_GL : ∀ {φ}, (h : φ ∈ Logic.GL) → motive φ (sumQuasiNormal.mem₁ h))
  (axiomT : ∀ {φ}, motive (Axioms.T φ) (sumQuasiNormal.subst (φ := Axioms.T (.atom 0)) (s := λ _ => φ) (sumQuasiNormal.mem₂ (by tauto))))
  (mdp : ∀ {φ ψ}, {hφψ : φ ➝ ψ ∈ Logic.S} → {hφ : φ ∈ Logic.S} → (motive (φ ➝ ψ) hφψ) → (motive φ hφ) → motive ψ (sumQuasiNormal.mdp hφψ hφ))
  : ∀ {φ}, (h : φ ∈ Logic.S) → motive φ h := by
  intro φ h;
  rw [Logic.eq_S_S'] at h;
  induction h with
  | mem_GL h =>
    apply mem_GL;
    assumption;
  | axiomT h =>
    exact axiomT;
  | @mdp φ ψ hφψ hφ ihφψ ihφ =>
    apply mdp;
    . apply ihφψ;
    . apply ihφ;
    . rwa [←Logic.eq_S_S'] at hφψ;
    . rwa [←Logic.eq_S_S'] at hφ;

end LO.Modal



namespace LO.FirstOrder.DerivabilityCondition

namespace ProvabilityPredicate

variable {L} [Semiterm.Operator.GoedelNumber L (Sentence L)] [L.DecidableEq]
         {M : Type*} [Nonempty M] [Structure L M]
         {T₀ T : FirstOrder.Theory L} [T₀ ⪯ T] [Diagonalization T₀]
         {𝔅 : ProvabilityPredicate T₀ T} [𝔅.HBL]

class Justified (𝔅 : ProvabilityPredicate T₀ T) (M) [Nonempty M] [Structure L M] where
  protected justified {σ : Sentence L} : T ⊢!. σ ↔ M ⊧ₘ₀ 𝔅 σ

protected alias justified := Justified.justified

end ProvabilityPredicate

end LO.FirstOrder.DerivabilityCondition



namespace LO.ProvabilityLogic

open Entailment
open Modal
open FirstOrder FirstOrder.DerivabilityCondition
open ProvabilityPredicate

variable {L} [Semiterm.Operator.GoedelNumber L (Sentence L)] [L.DecidableEq]
         {T₀ T : FirstOrder.Theory L} [T₀ ⪯ T] [Diagonalization T₀]
         {M} [Nonempty M] [Structure L M]
         {𝔅 : ProvabilityPredicate T₀ T} [𝔅.HBL] [𝔅.Justified M]
         {A : Formula ℕ}

lemma arithmetical_soundness_S
  (hSound : ∀ {σ}, T ⊢!. σ → M ⊧ₘ₀ σ)  -- TODO: remove
  (h : A ∈ Logic.S) (f : Realization L) : M ⊧ₘ₀ (f.interpret 𝔅 A) := by
  induction h using Logic.S.rec' with
  | mem_GL h => exact hSound $ arithmetical_soundness_GL h
  | axiomT =>
    simp only [Realization.interpret, models₀_imply_iff];
    intro h;
    exact hSound $ 𝔅.justified (M := M) |>.mpr h;
  | mdp ihAB ihA =>
    simp only [Realization.interpret, models₀_imply_iff] at ihAB;
    apply ihAB ihA;

end LO.ProvabilityLogic
