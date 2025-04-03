import Foundation.Modal.Logic.Extension
import Foundation.ProvabilityLogic.GL.Completeness
import Foundation.ProvabilityLogic.Soundness
import Mathlib.Tactic.TFAE

namespace LO


namespace Entailment

open Entailment
open FiniteContext

variable {F : Type*} [LogicalConnective F] [DecidableEq F]
         {S : Type*} [Entailment F S]
         {𝓢 : S} [Entailment.Classical 𝓢]
         {φ ψ ξ : F}

lemma ENIpqApNq! : 𝓢 ⊢! ∼(φ ➝ ψ) ⭤ (φ ⋏ ∼ψ) := by
  apply and₃'!;
  . apply deduct'!;
    apply and₃'!;
    . apply deductInv'!;
      apply contra₂'!;
      exact efq_imply_not₁!
    . apply deductInv'!;
      apply contra₂'!;
      apply imp_swap'!;
      apply deduct'!;
      exact dne!;
  . apply not_imply_prem''! and₁! and₂!;

lemma NIpq_ApNq! : 𝓢 ⊢! ∼(φ ➝ ψ) ↔ 𝓢 ⊢! (φ ⋏ ∼ψ) := by
  constructor;
  . intro h; exact (and₁'! ENIpqApNq!) ⨀ h;
  . intro h; exact (and₂'! ENIpqApNq!) ⨀ h;

lemma p_Nq_NIpq! (hp : 𝓢 ⊢! φ) (hnq : 𝓢 ⊢! ∼ψ) : 𝓢 ⊢! ∼(φ ➝ ψ) := by
  apply NIpq_ApNq!.mpr;
  apply and₃'!;
  . exact hp;
  . exact hnq;

end Entailment



namespace Modal


section

variable {M : Kripke.Model} {x : M.World} {φ ψ : Formula ℕ} {Γ : FormulaFinset ℕ}

lemma Formula.Kripke.Satisfies.finset_conj_def : x ⊧ Γ.conj ↔ ∀ φ ∈ Γ, x ⊧ φ := by
  simp only [Semantics.realize_finset_conj, Satisfies.iff_models];

end

section


open Logic

protected abbrev Logic.S := addQuasiNormal Logic.GL (Axioms.T (.atom 0))
instance : Logic.S.QuasiNormal where
  subset_K := by
    intro φ hφ;
    apply Logic.sumQuasiNormal.mem₁;
    exact Logic.of_mem_K hφ;
  mdp_closed := by
    intro φ ψ hφψ hφ;
    apply Logic.sumQuasiNormal.mdp hφψ hφ;
  subst_closed := by
    intro φ hφ s;
    apply Logic.sumQuasiNormal.subst;
    exact hφ;

lemma Logic.S.mem_axiomT : □φ ➝ φ ∈ Logic.S := by
  apply Logic.subst (φ := Axioms.T (.atom 0)) (s := λ _ => φ);
  apply Logic.sumQuasiNormal.mem₂;
  tauto;

lemma GL_subset_S : Logic.GL ⊆ Logic.S := by
  intro φ hφ;
  apply Logic.sumQuasiNormal.mem₁;
  assumption;

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
    | subst hφ ihφ =>
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
  | mem_GL h => apply mem_GL; assumption;
  | axiomT h => exact axiomT;
  | mdp hφψ hφ ihφψ ihφ =>
    apply mdp;
    . apply ihφψ;
    . apply ihφ;
    . rwa [←Logic.eq_S_S'] at hφψ;
    . rwa [←Logic.eq_S_S'] at hφ;


lemma Logic.conj_iff {L : Modal.Logic} [L.QuasiNormal] {Γ : FormulaFinset ℕ} : Γ.conj ∈ L ↔ ∀ φ ∈ Γ, φ ∈ L := by
  constructor;
  . intro h φ hφ;
    sorry;
  . intro h;
    sorry;

end

variable {α} [DecidableEq α]

noncomputable abbrev Formula.rflSubformula (φ : Formula α) : FormulaFinset α := (φ.subformulas.prebox.image (λ ψ => □ψ ➝ ψ))

end Modal



namespace FirstOrder.DerivabilityCondition

namespace ProvabilityPredicate

variable {L} [Semiterm.Operator.GoedelNumber L (Sentence L)] [L.DecidableEq]
         {M : Type*} [Nonempty M] [Structure L M]
         {T₀ T : FirstOrder.Theory L} [T₀ ⪯ T] [Diagonalization T₀]
         {𝔅 : ProvabilityPredicate T₀ T} [𝔅.HBL]

class Justified (𝔅 : ProvabilityPredicate T₀ T) (M) [Nonempty M] [Structure L M] where
  protected justified {σ : Sentence L} : T ⊢!. σ ↔ M ⊧ₘ₀ 𝔅 σ

protected alias justified := Justified.justified

end ProvabilityPredicate

end FirstOrder.DerivabilityCondition



namespace ProvabilityLogic

open Entailment
open Modal
open FirstOrder FirstOrder.DerivabilityCondition
open ProvabilityPredicate

variable {L} [Semiterm.Operator.GoedelNumber L (Sentence L)] [L.DecidableEq]
         {T₀ T : FirstOrder.Theory L} [T₀ ⪯ T] [Diagonalization T₀]
         {M : Type*} [Nonempty M] [Structure L M] [M ⊧ₘ* T]
         {𝔅 : ProvabilityPredicate T₀ T} [𝔅.HBL] [𝔅.Justified M]
         {A B : Formula ℕ}

-- TODO: rename and move
omit
  [Semiterm.Operator.GoedelNumber L (Sentence L)]
  [L.DecidableEq]
in
lemma sound_models (h : T ⊢!. σ) : M ⊧ₘ₀ σ := consequence_iff.mp (sound! (T := T) h) M inferInstance

theorem arithmetical_soundness_S
  (h : A ∈ Logic.S) (f : Realization L) : M ⊧ₘ₀ (f.interpret 𝔅 A) := by
  induction h using Logic.S.rec' with
  | mem_GL h =>
    exact sound_models $ arithmetical_soundness_GL h;
  | axiomT =>
    simp only [Realization.interpret, models₀_imply_iff];
    intro h;
    exact sound_models $ (𝔅.justified (M := M) |>.mpr h);
  | mdp ihAB ihA =>
    simp only [Realization.interpret, models₀_imply_iff] at ihAB;
    apply ihAB ihA;


section

instance : 𝐏𝐀.Delta1Definable := by sorry

instance {T : FirstOrder.Theory ℒₒᵣ} [𝐏𝐀 ⪯ T] [T.Delta1Definable] : (𝐏𝐀.standardDP T).Justified ℕ := ⟨by sorry⟩

lemma _root_.LO.Modal.Logic.iff_provable_GL_provable_box_S : A ∈ Logic.GL ↔ □A ∈ Logic.S := by
  constructor;
  . intro h;
    apply Logic.sumQuasiNormal.mem₁;
    apply nec! h;
  . intro h;
    apply arithmetical_completeness_GL (𝔅 := 𝐏𝐀.standardDP 𝐏𝐀);
    intro f;
    exact (𝐏𝐀.standardDP 𝐏𝐀).justified (M := ℕ) |>.mpr $ arithmetical_soundness_S h f;

end


section

open Entailment FiniteContext
open Modal
open Modal.Kripke
open Modal.Formula.Kripke

lemma GL_S_TFAE :
  [
    (A.rflSubformula.conj ➝ A) ∈ Logic.GL,
    A ∈ Logic.S,
    ∀ f : Realization L, M ⊧ₘ₀ (f.interpret 𝔅 A)
  ].TFAE := by
  tfae_have 1 → 2 := by
    intro h;
    apply Logic.S.mdp (GL_subset_S h) ?_;
    apply Logic.conj_iff.mpr;
    suffices ∀ B, □B ∈ A.subformulas → □B ➝ B ∈ Logic.S by simpa [Formula.rflSubformula];
    rintro B _;
    exact Logic.S.mem_axiomT;
  tfae_have 2 → 3 := by
    intro h f;
    apply arithmetical_soundness_S;
    exact h;
  tfae_have 3 → 1 := by
    contrapose;
    push_neg;
    intro hA;
    obtain ⟨M₁, r₁, _, hA⟩ := Hilbert.GL.Kripke.iff_unprovable_exists_unsatisfies_FiniteTransitiveTree.mp hA;
    let M₀ := Model.extendRoot M₁ r₁;
    let r₀ : M₀.World := Model.extendRoot.root;
    replace hA := Formula.Kripke.Satisfies.imp_def.not.mp hA;
    push_neg at hA;
    obtain ⟨hA₁, hA₂⟩ := hA;
    replace hA₁ : ∀ φ ∈ A.rflSubformula, Satisfies M₀ r₁ φ := Satisfies.finset_conj_def.mp $ Model.extendRoot.modal_equivalence_original_world.mp hA₁;
    replace hA₂ : ¬Satisfies M₀ r₁ A := Model.extendRoot.modal_equivalence_original_world.not.mp hA₂;
    let σ : SolovaySentences 𝔅 M₁.toFrame r₁ := by sorry;
    use σ.realization;

    let r₀ := Kripke.Model.extendRoot.root (M := M₁) (r := r₁);
    have H :
      ∀ B ∈ A.subformulas,
      (Satisfies M₀ r₁ B → T₀ ⊢!. (σ r₀) ➝ (σ.realization.interpret 𝔅 B)) ∧
      (¬Satisfies M₀ r₁ B → T₀ ⊢!. (σ r₀) ➝ ∼(σ.realization.interpret 𝔅 B)) := by
      intro B B_sub;
      induction B using Formula.rec' with
      | hfalsum => simp [Satisfies, Realization.interpret];
      | himp B C ihB ihC =>
        dsimp [Realization.interpret];
        constructor;
        . intro h;
          rcases Satisfies.imp_def₂.mp h with (hA | hB);
          . exact imp_trans''! (ihB (Formula.subformulas.mem_imp B_sub |>.1) |>.2 hA) efq_imply_not₁!;
          . exact imp_trans''! (ihC (Formula.subformulas.mem_imp B_sub |>.2) |>.1 hB) imply₁!;
        . intro h;
          have := Satisfies.imp_def.not.mp h;
          push_neg at this;
          obtain ⟨hA, hB⟩ := this;
          apply deduct'!;
          apply p_Nq_NIpq!;
          . exact deductInv'! $ ihB (Formula.subformulas.mem_imp B_sub |>.1) |>.1 hA;
          . exact deductInv'! $ ihC (Formula.subformulas.mem_imp B_sub |>.2) |>.2 hB;
      | hatom =>
        constructor;
        . intro h;
          apply imply_fdisj;
          simpa;
        . intro h;
          apply contra₁'!;
          apply fdisj_imply!;
          intro i hi;
          apply σ.SC1;
          by_contra hC; subst hC;
          apply h;
          simpa using hi;
      | hbox B ihB =>
        simp only [Realization.interpret];
        constructor;
        . intro h;
          apply imply₁'!;
          apply 𝔅.D1;
          apply Entailment.WeakerThan.pbl (𝓢 := T₀.alt);
          have : T₀ ⊢!. ((⩖ j, σ j)) ➝ σ.realization.interpret 𝔅 B := by
            apply fdisj_imply!;
            have hrfl : Satisfies M₀ (Sum.inr r₁) (□B ➝ B) := by
              apply hA₁;
              simpa [Formula.rflSubformula];
            rintro (_ | i) _;
            . suffices T₀ ⊢!. σ r₀ ➝ σ.realization.interpret 𝔅 B by convert this;
              apply ihB (Formula.subformulas.mem_box B_sub) |>.1;
              exact Satisfies.mdp hrfl h;
            . by_cases e : i = r₁;
              . rw [e];
                apply σ.mainlemma (A := B) (i := r₁) |>.1;
                exact Model.extendRoot.modal_equivalence_original_world.mpr $ Satisfies.mdp hrfl h;
              . apply σ.mainlemma (A := B) (i := i) |>.1;
                apply Model.extendRoot.modal_equivalence_original_world.mpr;
                apply h;
                suffices r₁ ≺ i by simpa [Frame.Rel', Model.extendRoot, Frame.extendRoot, M₀];
                apply Frame.IsRooted.direct_rooted_of_trans;
                assumption;
          exact this ⨀ (by sorry); -- `T₀ ⊢!. ⩖ j, σ j`
        . intro h;
          have := Satisfies.box_def.not.mp h;
          push_neg at this;
          obtain ⟨(_ | i), Rij, hA⟩ := this;
          . simp only [Frame.Rel', Model.extendRoot, Frame.extendRoot, M₀] at Rij;
          have : T₀ ⊢!. σ.σ (Sum.inr i) ➝ ∼σ.realization.interpret 𝔅 B := σ.mainlemma (A := B) (i := i) |>.2
            $ Model.extendRoot.modal_equivalence_original_world |>.not.mpr hA;
          have : T₀ ⊢!. ∼𝔅 (∼σ.σ (Sum.inr i)) ➝ ∼𝔅 (σ.realization.interpret 𝔅 B) := contra₀'! $ 𝔅.prov_distribute_imply' $ contra₁'! $ this;
          refine imp_trans''! ?_ this;
          apply σ.SC2;
          tauto;
    have : M ⊧ₘ* T₀ := models_of_subtheory (U := T₀) (T := T) (M := M) inferInstance;
    have : M ⊧ₘ₀ σ.σ r₀ ➝ ∼σ.realization.interpret 𝔅 A := sound_models $ H A (by simp) |>.2 hA₂;
    simp only [models₀_imply_iff, models₀_not_iff] at this;
    exact this $ by sorry; -- by lemma 2.1.1(4)
  tfae_finish;

theorem arithmetical_completeness_S : A ∈ Logic.S ↔ ∀ f : Realization L, M ⊧ₘ₀ (f.interpret 𝔅 A) := GL_S_TFAE.out 1 2

lemma _root_.LO.Modal.Logic.iff_provable_rfl_GL_provable_S : (A.rflSubformula.conj ➝ A) ∈ Logic.GL ↔ A ∈ Logic.S := GL_S_TFAE (𝔅 := 𝐏𝐀.standardDP 𝐏𝐀) (M := ℕ) |>.out 0 1

end

end ProvabilityLogic

end LO
