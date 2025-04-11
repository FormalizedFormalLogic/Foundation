import Foundation.Modal.Logic.Extension
import Foundation.ProvabilityLogic.GL.Completeness
import Mathlib.Tactic.TFAE

namespace LO

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


namespace Logic

open Entailment

variable {L : Modal.Logic} [L.QuasiNormal] {φ ψ : Formula ℕ}

lemma p_q_Apq (hφ : φ ∈ L) (hψ : ψ ∈ L) : φ ⋏ ψ ∈ L := by
  apply Logic.mdp (φ := ψ);
  apply Logic.mdp (φ := φ) (ψ := ψ ➝ φ ⋏ ψ);
  . apply Logic.of_mem_K;
    exact and₃!;
  . assumption;
  . assumption;

lemma conj_iffAux {Γ : List (Formula ℕ)} : Γ.conj₂ ∈ L ↔ ∀ φ ∈ Γ, φ ∈ L := by
  constructor;
  . intro h φ hφ;
    refine Logic.mdp ?_ h;
    apply Logic.of_mem_K;
    apply general_conj'! hφ;
  . intro h;
    induction Γ using List.induction_with_singleton with
    | hnil =>
      simp only [List.conj₂_nil];
      apply Logic.of_mem_K;
      exact verum!;
    | hsingle φ =>
      apply h;
      simp;
    | @hcons φ Γ hΓ ih =>
      simp [List.conj₂_cons_nonempty hΓ];
      apply p_q_Apq;
      . apply h; tauto;
      . apply ih; tauto;

lemma conj_iff {Γ : FormulaFinset ℕ} : Γ.conj ∈ L ↔ ∀ φ ∈ Γ, φ ∈ L := by
  constructor;
  . intro h φ hφ;
    apply Logic.conj_iffAux (Γ := Γ.toList) |>.mp $ h;
    simpa;
  . intro h;
    apply Logic.conj_iffAux (Γ := Γ.toList) |>.mpr;
    intro φ hφ;
    apply h;
    simpa using hφ;

end Logic

end

variable {α} [DecidableEq α]

noncomputable abbrev Formula.rflSubformula (φ : Formula α) : FormulaFinset α := (φ.subformulas.prebox.image (λ ψ => □ψ ➝ ψ))

end Modal

namespace ProvabilityLogic

open Entailment
open Modal
open FirstOrder FirstOrder.DerivabilityCondition
open ProvabilityPredicate

variable {T₀ T : FirstOrder.Theory ℒₒᵣ} [T₀ ⪯ T] [Diagonalization T₀]
         {𝔅 : ProvabilityPredicate T₀ T} [𝔅.HBL] [ℕ ⊧ₘ* T] [𝔅.Sound ℕ]
         {A B : Formula ℕ}

theorem arithmetical_soundness_S (h : A ∈ Logic.S) (f : Realization ℒₒᵣ) : ℕ ⊧ₘ₀ f.interpret 𝔅 A := by
  induction h using Logic.S.rec' with
  | mem_GL h =>
    exact models_of_provable₀ inferInstance (GL.arithmetical_soundness (L := ℒₒᵣ) h);
  | axiomT =>
    simp only [Realization.interpret, models₀_imply_iff];
    intro h;
    exact models_of_provable₀ inferInstance (Iff.mp 𝔅.sound h)
  | mdp ihAB ihA =>
    simp only [Realization.interpret, models₀_imply_iff] at ihAB;
    apply ihAB ihA;

section

instance : 𝐈𝚺₁.Delta1Definable := by sorry

instance [𝐈𝚺₁ ⪯ T] [T.Delta1Definable] : ((𝐈𝚺₁).standardDP T).Sound ℕ := ⟨fun {σ} ↦ by
  have : 𝐑₀ ⪯ T := Entailment.WeakerThan.trans (𝓣 := 𝐈𝚺₁) inferInstance inferInstance
  simp [Arith.standardDP_def, models₀_iff]⟩

lemma _root_.LO.Modal.Logic.iff_provable_GL_provable_box_S : A ∈ Logic.GL ↔ □A ∈ Logic.S := by
  constructor;
  . intro h;
    apply Logic.sumQuasiNormal.mem₁;
    apply nec! h;
  . intro h;
    apply GL.arithmetical_completeness (T := 𝐈𝚺₁);
    intro f;
    exact Iff.mp ((𝐈𝚺₁).standardDP 𝐈𝚺₁).sound (arithmetical_soundness_S h f)

end

section

open Entailment FiniteContext
open Modal
open Modal.Kripke
open Modal.Formula.Kripke
open Arith

variable [T.Delta1Definable] [𝐈𝚺₁ ⪯ T] [SoundOn T (Hierarchy 𝚷 2)]

instance instIsFiniteTree {F : Frame} (r : F) [F.IsFiniteTree r] : (F.extendRoot r).IsFiniteTree Frame.extendRoot.root where

lemma GL_S_TFAE :
  [
    (A.rflSubformula.conj ➝ A) ∈ Logic.GL,
    A ∈ Logic.S,
    ∀ f : Realization ℒₒᵣ, ℕ ⊧ₘ₀ (f.interpret ((𝐈𝚺₁).standardDP T) A)
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
    replace hA₁ : ∀ φ ∈ A.rflSubformula, r₁ ⊧ φ := by simpa using Satisfies.finset_conj_def.mp (Model.extendRoot.modal_equivalence_original_world.mp hA₁)
    replace hA₂ : ¬r₁ ⊧ A := by simpa using Model.extendRoot.modal_equivalence_original_world.not.mp hA₂;
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
          apply ((𝐈𝚺₁).standardDP T).D1;
          apply Entailment.WeakerThan.pbl (𝓢 := 𝐈𝚺₁.alt);
          have : 𝐈𝚺₁ ⊢!. ((⩖ j, σ j)) ➝ σ.realization.interpret ((𝐈𝚺₁).standardDP T) B := by
            apply fdisj_imply!;
            have hrfl : r₁ ⊧ □B ➝ B := by
              apply hA₁;
              simpa [Formula.rflSubformula];
            rintro (_ | i) _;
            . suffices 𝐈𝚺₁ ⊢!. σ r₀ ➝ σ.realization.interpret ((𝐈𝚺₁).standardDP T) B by convert this;
              apply ihB (Formula.subformulas.mem_box B_sub) |>.1;
              exact hrfl h;
            . by_cases e : i = r₁;
              . rw [e];
                apply σ.mainlemma (i := r₁) (by trivial) |>.1;
                exact Model.extendRoot.modal_equivalence_original_world.mpr
                  <| Model.extendRoot.inr_forces_iff.mpr <| Model.extendRoot.inr_forces_iff.mpr (hrfl h);
              . apply σ.mainlemma (i := i) (by trivial) |>.1;
                apply Model.extendRoot.modal_equivalence_original_world.mpr;
                apply Model.extendRoot.inr_forces_iff.mpr
                apply Model.extendRoot.inr_forces_iff.mpr
                apply h;
                suffices r₁ ≺ i by simpa [Frame.Rel', Model.extendRoot, Frame.extendRoot, M₀];
                apply Frame.IsRooted.direct_rooted_of_trans;
                assumption
          have b : 𝐈𝚺₁ ⊢!. ⩖ j, σ j := oRing_provable₀_of _ _ fun (V : Type) _ _ ↦ by
            simpa [models₀_iff, σ, SolovaySentences.standard_σ_def] using SolovaySentences.solovay_disjunction
          exact this ⨀ b
        . intro h;
          have := Satisfies.box_def.not.mp h;
          push_neg at this;
          obtain ⟨i, Rij, hA⟩ := this;
          have : 𝐈𝚺₁ ⊢!. σ.σ (Sum.inr i) ➝ ∼σ.realization.interpret ((𝐈𝚺₁).standardDP T) B := σ.mainlemma (A := B) (i := i) (by trivial) |>.2
            <| Model.extendRoot.modal_equivalence_original_world |>.not.mpr <| by
              simpa [Model.extendRoot.inr_forces_iff (M := M₀), Model.extendRoot.inr_forces_iff (M := M₁)] using hA
          have : 𝐈𝚺₁ ⊢!. ∼((𝐈𝚺₁).standardDP T) (∼σ (Sum.inr i)) ➝ ∼((𝐈𝚺₁).standardDP T) (σ.realization.interpret ((𝐈𝚺₁).standardDP T) B) :=
            contra₀'!
            $ ((𝐈𝚺₁).standardDP T).prov_distribute_imply'
            $ contra₁'! $ this;
          refine imp_trans''! ?_ this;
          apply σ.SC2;
          tauto;
    have : ℕ ⊧ₘ* 𝐈𝚺₁ := models_of_subtheory (U := 𝐈𝚺₁) (T := T) (M := ℕ) inferInstance;
    have : ℕ ⊧ₘ₀ σ.σ r₀ ➝ ∼σ.realization.interpret ((𝐈𝚺₁).standardDP T) A := models_of_provable₀ inferInstance $ H A (by simp) |>.2 hA₂;
    simp only [models₀_imply_iff, models₀_not_iff] at this;
    exact this <| by
      simpa [models₀_iff, σ, SolovaySentences.standard_σ_def] using SolovaySentences.solovay_root_sound
  tfae_finish;

theorem S.arithmetical_completeness_iff : A ∈ Logic.S ↔ ∀ f : Realization ℒₒᵣ, ℕ ⊧ₘ₀ (f.interpret ((𝐈𝚺₁).standardDP T) A) := GL_S_TFAE.out 1 2

lemma _root_.LO.Modal.Logic.iff_provable_rfl_GL_provable_S : (A.rflSubformula.conj ➝ A) ∈ Logic.GL ↔ A ∈ Logic.S := GL_S_TFAE (T := 𝐈𝚺₁) |>.out 0 1

end

end ProvabilityLogic

end LO
