import Foundation.Modal.Logic.Extension
import Foundation.Modal.Logic.S.Basic
import Foundation.ProvabilityLogic.GL.Completeness
import Foundation.ProvabilityLogic.S.Soundness
import Foundation.Modal.Boxdot.Basic
import Mathlib.Tactic.TFAE


noncomputable abbrev LO.Modal.Formula.rflSubformula [DecidableEq α] (φ : Formula α) : FormulaFinset α
  := (φ.subformulas.prebox.image (λ ψ => □ψ ➝ ψ))


namespace LO.ProvabilityLogic

open Entailment
open Modal
open FirstOrder FirstOrder.DerivabilityCondition
open ProvabilityPredicate

variable {T₀ T : FirstOrder.Theory ℒₒᵣ} [T₀ ⪯ T] [Diagonalization T₀]
         {𝔅 : ProvabilityPredicate T₀ T} [𝔅.HBL] [ℕ ⊧ₘ* T] [𝔅.Sound ℕ]
         {A B : Formula ℕ}

open Entailment FiniteContext
open Modal
open Modal.Kripke
open Modal.Formula.Kripke
open Arith

variable [T.Delta1Definable] [𝐈𝚺₁ ⪯ T] [SoundOn T (Hierarchy 𝚷 2)]

lemma GL_S_TFAE :
  [
    (A.rflSubformula.conj ➝ A) ∈ Logic.GL,
    A ∈ Logic.S,
    ∀ f : Realization ℒₒᵣ, ℕ ⊧ₘ₀ (f.interpret ((𝐈𝚺₁).standardDP T) A)
  ].TFAE := by
  tfae_have 1 → 2 := by
    intro h;
    apply Logic.S.mdp (Logic.GL_subset_S h) ?_;
    apply Logic.conj_iff.mpr;
    suffices ∀ B, □B ∈ A.subformulas → □B ➝ B ∈ Logic.S by simpa [Formula.rflSubformula];
    rintro B _;
    exact Logic.S.mem_axiomT;
  tfae_have 2 → 3 := by
    intro h f;
    apply S.arithmetical_soundness;
    exact h;
  tfae_have 3 → 1 := by
    contrapose;
    push_neg;
    intro hA;
    obtain ⟨M₁, r₁, _, hA⟩ := Hilbert.GL.Kripke.iff_unprovable_exists_unsatisfies_FiniteTransitiveTree.mp hA;
    let M₀ := Model.extendRoot M₁ r₁ 1;
    let r₀ : M₀.World := Model.extendRoot.root;
    replace hA := Formula.Kripke.Satisfies.imp_def.not.mp hA;
    push_neg at hA;
    obtain ⟨hA₁, hA₂⟩ := hA;
    replace hA₁ : ∀ φ ∈ A.rflSubformula, r₁ ⊧ φ := by
      intro φ hφ;
      apply Model.extendRoot.inr_satisfies_iff.mp
        $ (Satisfies.fconj_def.mp
        $ Model.extendRoot.inr_satisfies_iff (n := 1) |>.mpr hA₁) φ hφ;
    have : M₀.IsFiniteTree r₀ := Frame.extendRoot.instIsFiniteTree
    have : Fintype M₀.World := Fintype.ofFinite _
    let σ : SolovaySentences ((𝐈𝚺₁).standardDP T) (M₀.toFrame) r₀ :=
      SolovaySentences.standard M₀.toFrame Frame.extendRoot.root T
    use σ.realization;
    have H :
      ∀ B ∈ A.subformulas,
      (r₁ ⊧ B → 𝐈𝚺₁ ⊢!. (σ r₀) ➝ (σ.realization.interpret ((𝐈𝚺₁).standardDP T) B)) ∧
      (¬r₁ ⊧ B → 𝐈𝚺₁ ⊢!. (σ r₀) ➝ ∼(σ.realization.interpret ((𝐈𝚺₁).standardDP T) B)) := by
      intro B B_sub;
      induction B with
      | hfalsum => simp [Satisfies, Realization.interpret];
      | himp B C ihB ihC =>
        dsimp [Realization.interpret];
        constructor;
        . intro h;
          rcases Satisfies.imp_def₂.mp h with (hA | hB);
          . exact C!_trans (ihB (Formula.subformulas.mem_imp B_sub |>.1) |>.2 hA) CNC!;
          . exact C!_trans (ihC (Formula.subformulas.mem_imp B_sub |>.2) |>.1 hB) imply₁!;
        . intro h;
          have := Satisfies.imp_def.not.mp h;
          push_neg at this;
          obtain ⟨hA, hB⟩ := this;
          apply deduct'!;
          apply NC!_of_N!_of_!;
          . exact deductInv'! $ ihB (Formula.subformulas.mem_imp B_sub |>.1) |>.1 hA;
          . exact deductInv'! $ ihC (Formula.subformulas.mem_imp B_sub |>.2) |>.2 hB;
      | hatom =>
        constructor;
        . intro h;
          apply right_Fdisj'!_intro;
          simpa;
        . intro h;
          apply CN!_of_CN!_right;
          apply left_Fdisj'!_intro;
          intro i hi;
          apply σ.SC1;
          by_contra hC; subst hC;
          apply h;
          simpa using hi;
      | hbox B ihB =>
        simp only [Realization.interpret];
        constructor;
        . intro h;
          apply C!_of_conseq!;
          apply ((𝐈𝚺₁).standardDP T).D1;
          apply Entailment.WeakerThan.pbl (𝓢 := 𝐈𝚺₁.alt);
          have : 𝐈𝚺₁ ⊢!. ((⩖ j, σ j)) ➝ σ.realization.interpret ((𝐈𝚺₁).standardDP T) B := by
            apply left_Fdisj'!_intro;
            have hrfl : r₁ ⊧ □B ➝ B := by
              apply hA₁;
              simpa [Formula.rflSubformula];
            rintro (i | i) _;
            . rw [(show (Sum.inl i) = r₀ by simp [r₀]; omega)]
              suffices 𝐈𝚺₁ ⊢!. σ r₀ ➝ σ.realization.interpret ((𝐈𝚺₁).standardDP T) B by convert this;
              apply ihB (Formula.subformulas.mem_box B_sub) |>.1;
              exact hrfl h;
            . by_cases e : i = r₁;
              . rw [e];
                apply σ.mainlemma (i := r₁) (by trivial) |>.1;
                exact Model.extendRoot.inr_satisfies_iff (n := 1) |>.mpr $ hrfl h;
              . apply σ.mainlemma (i := i) (by trivial) |>.1;
                apply Model.extendRoot.inr_satisfies_iff (n := 1) |>.mpr;
                apply h;
                apply Frame.IsRooted.direct_rooted_of_trans;
                assumption
          have b : 𝐈𝚺₁ ⊢!. ⩖ j, σ j := oRing_provable₀_of _ _ fun (V : Type) _ _ ↦ by
            simpa [models₀_iff, σ, SolovaySentences.standard_σ_def] using ISigma1.Metamath.SolovaySentences.solovay_disjunction
          exact this ⨀ b
        . intro h;
          have := Satisfies.box_def.not.mp h;
          push_neg at this;
          obtain ⟨i, Rij, hA⟩ := this;
          have : 𝐈𝚺₁ ⊢!. σ.σ (Sum.inr i) ➝ ∼σ.realization.interpret ((𝐈𝚺₁).standardDP T) B :=
            σ.mainlemma (A := B) (i := i) (by trivial) |>.2
            <| Model.extendRoot.inr_satisfies_iff (n := 1) |>.not.mpr hA;
          have : 𝐈𝚺₁ ⊢!. ∼((𝐈𝚺₁).standardDP T) (∼σ (Sum.inr i)) ➝ ∼((𝐈𝚺₁).standardDP T) (σ.realization.interpret ((𝐈𝚺₁).standardDP T) B) :=
            contra!
            $ ((𝐈𝚺₁).standardDP T).prov_distribute_imply'
            $ CN!_of_CN!_right $ this;
          refine C!_trans ?_ this;
          apply σ.SC2;
          tauto;
    have : ℕ ⊧ₘ* 𝐈𝚺₁ := models_of_subtheory (U := 𝐈𝚺₁) (T := T) (M := ℕ) inferInstance;
    have : ℕ ⊧ₘ₀ σ.σ r₀ ➝ ∼σ.realization.interpret ((𝐈𝚺₁).standardDP T) A := models_of_provable₀ inferInstance $ H A (by simp) |>.2 hA₂;
    simp only [models₀_imply_iff, models₀_not_iff] at this;
    exact this <| by
      simpa [models₀_iff, σ, SolovaySentences.standard_σ_def] using ISigma1.Metamath.SolovaySentences.solovay_root_sound
  tfae_finish;

theorem S.arithmetical_completeness_iff : A ∈ Logic.S ↔ ∀ f : Realization ℒₒᵣ, ℕ ⊧ₘ₀ (f.interpret ((𝐈𝚺₁).standardDP T) A) := GL_S_TFAE.out 1 2

end ProvabilityLogic

end LO
