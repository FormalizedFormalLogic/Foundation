import Foundation.Modal.Logic.Extension
import Foundation.Modal.Logic.S.Basic
import Foundation.ProvabilityLogic.GL.Completeness
import Foundation.ProvabilityLogic.S.Soundness
import Foundation.Modal.Boxdot.Basic
import Foundation.FirstOrder.Incompleteness.Tarski
import Mathlib.Tactic.TFAE

noncomputable abbrev LO.Modal.Formula.rflSubformula [DecidableEq α] (φ : Formula α) : FormulaFinset α :=
  (φ.subformulas.prebox.image (λ ψ => □ψ ➝ ψ))

namespace LO.ProvabilityLogic

open Entailment
open Modal
open FirstOrder
open Provability
open ArithmeticTheory (ProvabilityLogic)

variable {T₀ T : ArithmeticTheory} [T₀ ⪯ T] [Diagonalization T₀]
         {𝔅 : Provability T₀ T} [𝔅.HBL] [ℕ ⊧ₘ* T] [𝔅.SoundOnModel ℕ]
         {A B : Formula ℕ}

open Entailment FiniteContext
open Modal
open Modal.Kripke
open Modal.Formula.Kripke
open Arithmetic

variable [T.Δ₁] [𝗜𝚺₁ ⪯ T]

lemma GL_S_TFAE :
    [
      Modal.GL ⊢! (A.rflSubformula.conj ➝ A),
      Modal.S ⊢! A,
      ∀ f : T.StandardRealization, ℕ ⊧ₘ (f A)
    ].TFAE := by
  tfae_have 1 → 2 := by
    intro h;
    have h : Modal.S ⊢! Finset.conj A.rflSubformula ➝ A := WeakerThan.pbl h;
    apply h ⨀ ?_;
    apply FConj!_iff_forall_provable.mpr;
    simp [-Logic.iff_provable];
  tfae_have 2 → 3 := by
    intro h f;
    have : 𝗥₀ ⪯ T := WeakerThan.trans (inferInstanceAs (𝗥₀ ⪯ 𝗜𝚺₁)) inferInstance
    apply S.arithmetical_soundness;
    exact h;
  tfae_have 3 → 1 := by
    contrapose;
    push_neg;
    intro hA;
    obtain ⟨M₁, r₁, _, hA⟩ := GL.Kripke.iff_unprovable_exists_unsatisfies_FiniteTransitiveTree.mp hA;
    let M₀ := Model.extendRoot M₁ 1;
    let r₀ : M₀.World := Model.extendRoot.root;
    replace hA := Formula.Kripke.Satisfies.imp_def.not.mp hA;
    push_neg at hA;
    obtain ⟨hA₁, hA₂⟩ := hA;
    replace hA₁ : ∀ φ ∈ A.rflSubformula, r₁ ⊧ φ := by
      intro φ hφ;
      apply Model.extendRoot.inr_satisfies_iff.mp
        $ (Satisfies.fconj_def.mp
        $ Model.extendRoot.inr_satisfies_iff (n := 1) |>.mpr hA₁) φ hφ;
    have : Fintype M₀.World := Fintype.ofFinite _
    let σ : SolovaySentences T.standardProvability (M₀.toFrame) r₀ :=
      SolovaySentences.standard T M₀.toFrame
    use σ.realization;
    have H :
      ∀ B ∈ A.subformulas,
      (r₁ ⊧ B → 𝗜𝚺₁ ⊢! (σ r₀) ➝ (σ.realization B)) ∧
      (¬r₁ ⊧ B → 𝗜𝚺₁ ⊢! (σ r₀) ➝ ∼(σ.realization B)) := by
      intro B B_sub;
      induction B with
      | hfalsum => simp [Realization.interpret];
      | himp B C ihB ihC =>
        dsimp [Realization.interpret];
        constructor;
        . intro h;
          rcases Satisfies.imp_def₂.mp h with (hA | hB);
          . exact C!_trans (ihB (by grind) |>.2 hA) CNC!;
          . exact C!_trans (ihC (by grind) |>.1 hB) imply₁!;
        . intro h;
          have := Satisfies.imp_def.not.mp h;
          push_neg at this;
          obtain ⟨hA, hB⟩ := this;
          apply deduct'!;
          apply NC!_of_N!_of_!;
          . exact deductInv'! $ ihB (by grind) |>.1 hA;
          . exact deductInv'! $ ihC (by grind) |>.2 hB;
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
          apply T.standardProvability.D1;
          apply Entailment.WeakerThan.pbl (𝓢 := 𝗜𝚺₁);
          have : 𝗜𝚺₁ ⊢! (⩖ j, σ j) ➝ σ.realization B := by
            apply left_Fdisj'!_intro;
            have hrfl : r₁ ⊧ □B ➝ B := by
              apply hA₁;
              simpa [Formula.rflSubformula];
            rintro (i | i) _;
            . rw [(show (Sum.inl i) = r₀ by simp [r₀]; omega)]
              suffices 𝗜𝚺₁ ⊢! σ r₀ ➝ σ.realization B by convert this;
              apply ihB (by grind) |>.1;
              exact hrfl h;
            . by_cases e : i = r₁;
              . rw [e];
                apply σ.mainlemma (i := r₁) (by trivial);
                exact Model.extendRoot.inr_satisfies_iff (n := 1) |>.mpr $ hrfl h;
              . apply σ.mainlemma (i := i) (by trivial);
                apply Model.extendRoot.inr_satisfies_iff (n := 1) |>.mpr;
                apply h;
                apply Frame.root_genaretes'!;
                assumption
          have b : 𝗜𝚺₁ ⊢! ⩖ j, σ j := oRing_provable_of _ _ fun (V : Type) _ _ ↦ by
            simpa [models_iff, σ, SolovaySentences.standard_σ_def] using ISigma1.Metamath.SolovaySentences.disjunctive
          exact this ⨀ b
        . intro h;
          have := Satisfies.box_def.not.mp h;
          push_neg at this;
          obtain ⟨i, Rij, hA⟩ := this;
          have : 𝗜𝚺₁ ⊢! σ.σ (Sum.inr i) ➝ ∼σ.realization B :=
            σ.mainlemma_neg (A := B) (i := i) (by trivial)
            <| Model.extendRoot.inr_satisfies_iff (n := 1) |>.not.mpr hA;
          have : 𝗜𝚺₁ ⊢! ∼T.standardProvability (∼σ (Sum.inr i)) ➝ ∼T.standardProvability (σ.realization B) :=
            contra!
            $ T.standardProvability.prov_distribute_imply'
            $ CN!_of_CN!_right $ this;
          refine C!_trans ?_ this;
          apply σ.SC2;
          tauto;
    have : ℕ ⊧ₘ* 𝗜𝚺₁ := models_of_subtheory (U := 𝗜𝚺₁) (T := T) (M := ℕ) inferInstance;
    have : ℕ ⊧ₘ σ.σ r₀ ➝ ∼σ.realization A := models_of_provable inferInstance $ H A (by simp) |>.2 hA₂;
    simp only [Models, LO.Semantics.Not.realize_not, LO.Semantics.Imp.realize_imp] at this;
    exact this <| by
      simpa [models_iff, σ, SolovaySentences.standard_σ_def] using ISigma1.Metamath.SolovaySentences.solovay_root_sound
  tfae_finish;

theorem S.arithmetical_completeness_iff : Modal.S ⊢! A ↔ ∀ f : T.StandardRealization, ℕ ⊧ₘ f A := GL_S_TFAE.out 1 2

theorem provabilityLogic_PA_TA_eq_S :
    ProvabilityLogic T 𝗧𝗔 ≊ Modal.S := by
  apply Logic.iff_equal_provable_equiv.mp
  ext A;
  simpa [ArithmeticTheory.ProvabilityLogic, FirstOrderTrueArith.provable_iff, ←Logic.iff_provable] using
    S.arithmetical_completeness_iff.symm;

instance : ProvabilityLogic 𝗣𝗔 𝗧𝗔 ≊ Modal.S := provabilityLogic_PA_TA_eq_S

end LO.ProvabilityLogic
