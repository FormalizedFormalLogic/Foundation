module

public import Foundation.Modal.Logic.SumNormal
public import Foundation.Modal.Logic.S.Basic
public import Foundation.ProvabilityLogic.GL.Completeness
public import Foundation.ProvabilityLogic.S.Soundness
public import Foundation.Modal.Boxdot.Basic
public import Foundation.FirstOrder.Incompleteness.Tarski
public import Mathlib.Tactic.TFAE

@[expose] public section
noncomputable abbrev LO.Modal.Formula.rflSubformula [DecidableEq α] (φ : Formula α) : FormulaFinset α :=
  ((□⁻¹'φ.subformulas).image (λ ψ => □ψ ➝ ψ))

namespace LO.ProvabilityLogic

open Entailment
open Modal
open FirstOrder FirstOrder.ProvabilityAbstraction
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

namespace SolovaySentences

section

omit [ℕ ⊧ₘ* T]

variable {M₁ : Kripke.Model} {r₁ : M₁} [M₁.IsFiniteTree r₁] {A : Formula _}

lemma refl_mainlemma_aux (hA : ¬r₁ ⊧ (A.rflSubformula.conj ➝ A)) :
  let M₀ := M₁.extendRoot 1
  let r₀ : M₀ := Model.extendRoot.root
  have : Fintype M₀.World := Fintype.ofFinite _
  let S := SolovaySentences.standard T M₀.toFrame
  ∀ B ∈ A.subformulas,
  (r₁ ⊧ B → 𝗜𝚺₁ ⊢ (S r₀) ➝ (S.realization B)) ∧
  (r₁ ⊭ B → 𝗜𝚺₁ ⊢ (S r₀) ➝ ∼(S.realization B)) := by
  intro M₀ r₀ _ S B B_sub;

  replace hA := Formula.Kripke.Satisfies.imp_def.not.mp hA;
  push_neg at hA;
  obtain ⟨hA₁, hA₂⟩ := hA;
  replace hA₁ : ∀ φ ∈ A.rflSubformula, r₁ ⊧ φ := by
    intro φ hφ;
    apply Model.extendRoot.inr_satisfies_iff.mp
      $ (Satisfies.fconj_def.mp
      $ Model.extendRoot.inr_satisfies_iff (n := 1) |>.mpr hA₁) φ hφ;

  induction B with
  | hfalsum => simp [Realization.interpret];
  | himp B C ihB ihC =>
    replace ihB := ihB (by grind);
    replace ihC := ihC (by grind);
    dsimp [Realization.interpret];
    constructor;
    . intro h;
      rcases Satisfies.imp_def₂.mp h with (hA | hB);
      . exact C!_trans (ihB.2 hA) CNC!;
      . exact C!_trans (ihC.1 hB) implyK!;
    . intro h;
      have := Satisfies.imp_def.not.mp h;
      push_neg at this;
      obtain ⟨hA, hB⟩ := this;
      have h₁ := ihB.1 hA;
      have h₂ := ihC.2 hB;
      cl_prover [h₁, h₂];
  | hatom =>
    constructor;
    . intro h;
      apply right_Fdisj'!_intro;
      simpa;
    . intro h;
      apply CN!_of_CN!_right;
      apply left_Fdisj'!_intro;
      intro i hi;
      apply S.SC1;
      by_contra hC; subst hC;
      apply h;
      simpa using hi;
  | hbox B ihB =>
    simp only [Realization.interpret];
    constructor;
    . intro h;
      apply C!_of_conseq!;
      apply D1;
      apply Entailment.WeakerThan.pbl (𝓢 := 𝗜𝚺₁);
      have : 𝗜𝚺₁ ⊢ ((⩖ j, S j)) ➝ S.realization B := by
        apply left_Fdisj'!_intro;
        have hrfl : r₁ ⊧ □B ➝ B := by
          apply hA₁;
          simp [Formula.rflSubformula, Finset.LO.preboxItr];
          grind;
        rintro (i | i) _;
        . rw [(show (Sum.inl i) = r₀ by simp [r₀];)]
          suffices 𝗜𝚺₁ ⊢ S r₀ ➝ S.realization B by convert this;
          apply ihB (by grind) |>.1;
          exact hrfl h;
        . by_cases e : i = r₁;
          . rw [e];
            apply S.mainlemma (i := r₁) (by trivial);
            exact Model.extendRoot.inr_satisfies_iff (n := 1) |>.mpr $ hrfl h;
          . apply S.mainlemma (i := i) (by trivial);
            apply Model.extendRoot.inr_satisfies_iff (n := 1) |>.mpr;
            apply h;
            apply Frame.root_genaretes'!;
            assumption
      have b : 𝗜𝚺₁ ⊢ ⩖ j, S j := provable_of_models _ _ fun (V : Type) _ _ ↦ by
        simpa [models_iff, S, SolovaySentences.standard_σ_def] using FirstOrder.Arithmetic.Bootstrapping.SolovaySentences.disjunctive
      exact this ⨀ b
    . intro h;
      have := Satisfies.box_def.not.mp h;
      push_neg at this;
      obtain ⟨i, Rij, hA⟩ := this;
      have : 𝗜𝚺₁ ⊢ S (Sum.inr i) ➝ ∼S.realization B :=
        S.mainlemma_neg (A := B) (i := i) (by trivial)
        <| Model.extendRoot.inr_satisfies_iff (n := 1) |>.not.mpr hA;
      have : 𝗜𝚺₁ ⊢ ∼T.standardProvability (∼S (Sum.inr i)) ➝ ∼T.standardProvability (S.realization B) :=
        contra!
        $ prov_distribute_imply'
        $ CN!_of_CN!_right $ this;
      refine C!_trans ?_ this;
      apply S.SC2;
      tauto;

lemma rfl_mainlemma (hA : ¬r₁ ⊧ (A.rflSubformula.conj ➝ A)) :
  letI M₀ := M₁.extendRoot 1
  letI r₀ : M₀ := Model.extendRoot.root
  haveI : Fintype M₀.World := Fintype.ofFinite _
  letI S := SolovaySentences.standard T M₀.toFrame
  ∀ B ∈ A.subformulas, r₁ ⊧ B → 𝗜𝚺₁ ⊢ (S r₀) ➝ (S.realization B) := fun B B_sub => (refl_mainlemma_aux hA B B_sub).1

lemma rfl_mainlemma_neg (hA : ¬r₁ ⊧ (A.rflSubformula.conj ➝ A)) :
  letI M₀ := M₁.extendRoot 1
  letI r₀ : M₀ := Model.extendRoot.root
  haveI : Fintype M₀.World := Fintype.ofFinite _
  letI S := SolovaySentences.standard T M₀.toFrame
  ∀ B ∈ A.subformulas, r₁ ⊭ B → 𝗜𝚺₁ ⊢ (S r₀) ➝ ∼(S.realization B) := λ B B_sub => (refl_mainlemma_aux hA B B_sub).2

end

end SolovaySentences


lemma GL_S_TFAE :
    [
      Modal.GL ⊢ (A.rflSubformula.conj ➝ A),
      Modal.S ⊢ A,
      ∀ f : T.StandardRealization, ℕ ⊧ₘ (f A)
    ].TFAE := by
  tfae_have 1 → 2 := by
    intro h;
    have h : Modal.S ⊢ Finset.conj A.rflSubformula ➝ A := WeakerThan.pbl h;
    apply h ⨀ ?_;
    apply FConj!_iff_forall_provable.mpr;
    simp
  tfae_have 2 → 3 := by
    intro h f;
    have : 𝗥₀ ⪯ T := WeakerThan.trans (inferInstanceAs (𝗥₀ ⪯ 𝗜𝚺₁)) inferInstance
    apply S.arithmetical_soundness;
    exact h;
  tfae_have 3 → 1 := by
    have : ℕ ⊧ₘ* 𝗜𝚺₁ := models_of_subtheory (U := 𝗜𝚺₁) (T := T) (M := ℕ) inferInstance;

    contrapose;
    push_neg;
    intro hA;
    obtain ⟨M₁, r₁, _, hA⟩ := GL.Kripke.iff_unprovable_exists_unsatisfies_FiniteTransitiveTree.mp hA;

    let M₀ := Model.extendRoot M₁ 1;
    let r₀ : M₀.World := Model.extendRoot.root;
    have : Fintype M₀.World := Fintype.ofFinite _
    let S := SolovaySentences.standard T M₀.toFrame
    use S.realization;

    have := Formula.Kripke.Satisfies.not_imp_def.mp hA |>.2;
    have : ℕ ⊧ₘ S r₀ ➝ ∼S.realization A := models_of_provable inferInstance $ by
      convert SolovaySentences.rfl_mainlemma_neg (T := T) hA A (by grind) $ Formula.Kripke.Satisfies.not_imp_def.mp hA |>.2;
    simp only [Models, LO.Semantics.Not.models_not, LO.Semantics.Imp.models_imply] at this;
    exact this <| by
      simpa [models_iff, S, SolovaySentences.standard_σ_def] using FirstOrder.Arithmetic.Bootstrapping.SolovaySentences.solovay_root_sound
  tfae_finish;

theorem S.arithmetical_completeness_iff : Modal.S ⊢ A ↔ ∀ f : T.StandardRealization, ℕ ⊧ₘ f A := GL_S_TFAE.out 1 2

theorem provabilityLogic_PA_TA_eq_S : ProvabilityLogic T 𝗧𝗔 ≊ Modal.S := by
  apply Logic.iff_equal_provable_equiv.mp
  ext A;
  simpa [ArithmeticTheory.ProvabilityLogic, TA.provable_iff, ←Logic.iff_provable] using
    S.arithmetical_completeness_iff.symm;

instance : ProvabilityLogic 𝗣𝗔 𝗧𝗔 ≊ Modal.S := provabilityLogic_PA_TA_eq_S

end LO.ProvabilityLogic
