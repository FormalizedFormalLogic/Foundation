module

public import Foundation.Modal.ComplementClosedConsistentFinset
public import Foundation.Modal.Kripke.Logic.GL.Soundness
public import Foundation.Modal.Kripke.Logic.K4

@[expose] public section

namespace LO.Modal

open Kripke
open LO.Entailment LO.Entailment.FiniteContext LO.Modal.Entailment
open Formula
open Entailment Entailment.FiniteContext
open Formula.Kripke
open ComplementClosedConsistentFinset

namespace GL.Kripke

variable {φ ψ : Formula ℕ}

abbrev miniCanonicalFrame (φ : Formula ℕ) : Kripke.Frame where
  World := ComplementClosedConsistentFinset Modal.GL φ.subformulas
  Rel X Y :=
    (∀ ψ ∈ □⁻¹'φ.subformulas, □ψ ∈ X → (ψ ∈ Y ∧ □ψ ∈ Y)) ∧
    (∃ χ ∈ □⁻¹'φ.subformulas, □χ ∉ X ∧ □χ ∈ Y)

namespace miniCanonicalFrame

instance : (miniCanonicalFrame φ).IsFinite := inferInstance

instance : (miniCanonicalFrame φ).IsIrreflexive := ⟨by simp⟩

instance : (miniCanonicalFrame φ).IsTransitive := ⟨by
  rintro X Y Z ⟨RXY, ⟨χ, _, _, _⟩⟩ ⟨RYZ, _⟩;
  constructor;
  . rintro ψ hq₁ hq₂;
    exact RYZ ψ hq₁ $ RXY ψ hq₁ hq₂ |>.2;
  . use χ;
    refine ⟨by assumption, by assumption, ?_⟩;
    exact RYZ χ (by assumption) (by assumption) |>.2;
⟩

instance : (miniCanonicalFrame φ).IsFiniteGL where

end miniCanonicalFrame


abbrev miniCanonicalModel (φ : Formula ℕ) : Kripke.Model where
  toFrame := miniCanonicalFrame φ
  Val a X := (atom a) ∈ X


lemma truthlemma_lemma1
  {X : ComplementClosedConsistentFinset Modal.GL φ.subformulas} (hq : □ψ ∈ φ.subformulas)
  : ((□⁻¹'X.1 ∪ □'□⁻¹'X.1) ∪ {□ψ, -ψ}) ⊆ φ.subformulas⁻ := by
  intro χ hr;
  replace hr : χ = □ψ ∨ χ = -ψ ∨ □χ ∈ X ∨ ∃ a, □a ∈ X ∧ □a = χ := by
    simpa [Finset.LO.preboxItr, Finset.LO.boxItr] using hr;
  rcases hr with (rfl | rfl | hp | ⟨χ, hr, rfl⟩);
  . apply Finset.mem_union.mpr;
    tauto;
  . apply Finset.mem_union.mpr;
    right;
    apply Finset.mem_image.mpr;
    use ψ;
    grind;
  . have := X.closed.subset hp;
    have := FormulaFinset.complementary_mem_box (by grind) this;
    apply Finset.mem_union.mpr;
    grind;
  . exact X.closed.subset hr;

lemma truthlemma_lemma2
  {X : ComplementClosedConsistentFinset Modal.GL φ.subformulas}
  (hψ₁ : □ψ ∈ φ.subformulas)
  (hψ₂ : □ψ ∉ X)
  : FormulaFinset.Consistent Modal.GL ((□⁻¹'X.1 ∪ □'□⁻¹'X.1) ∪ {□ψ, -ψ}) := by
  apply FormulaFinset.intro_union_consistent;
  rintro Γ₁ Γ₂ hΓ₁ hΓ₂;
  by_contra hC;
  apply hψ₂;
  have := Context.deduct! $ Context.weakening! (Γ := Γ₁ ∪ Γ₂) (Δ := insert (-ψ) (insert (□ψ) Γ₁)) ?_ hC;
  . replace : (insert (□ψ) Γ₁) *⊢[Modal.GL] ψ := of_imply_complement_bot this;
    replace : ↑Γ₁ *⊢[Modal.GL] □ψ ➝ ψ:= Context.deduct! this;
    replace : ↑(□'Γ₁) *⊢[Modal.GL] □(□ψ ➝ ψ) := by simpa using Context.nec! this;
    replace : ↑(□'Γ₁) *⊢[Modal.GL] □ψ := axiomL! ⨀ this;
    replace : ↑(□'□⁻¹'X.1 ∪ □^[2]'□⁻¹'X.1) *⊢[Modal.GL] □ψ := Context.weakening! ?_ this;
    . replace : ↑(□'□⁻¹'X.1) *⊢[Modal.GL] ((□^[2]'□⁻¹'X.1).conj) ➝ □ψ := FConj_DT'.mpr this;
      replace : ↑(□'□⁻¹'X.1) *⊢[Modal.GL] (□'□⁻¹'X.1).conj ➝ □ψ := C!_trans ?_ this;
      . replace : ↑(□'□⁻¹'X.1 ∪ □'□⁻¹'↑X) *⊢[Modal.GL] □ψ := FConj_DT'.mp this;
        have : X *⊢[Modal.GL] □ψ := Context.weakening! (by grind) this;
        exact membership_iff hψ₁ |>.mpr this;
      . apply CFconjFconj!_of_provable;
        intro ξ hξ;
        obtain ⟨ξ, h, rfl⟩ := Finset.LO.exists_of_mem_boxItr hξ;
        apply axiomFour'!;
        apply Context.by_axm!
        grind;
    . intro ξ hξ;
      simp only [Finset.LO.boxItr, Finset.coe_image, Set.mem_image,
        SetLike.mem_coe, Finset.LO.preboxItr, Box.boxItr_succ, Finset.coe_union,
        Finset.coe_preimage, Set.mem_union, Set.mem_preimage] at ⊢ hξ;
      rcases hξ with ⟨ξ, ⟨hξ, rfl⟩⟩;
      rcases (Finset.mem_union.mp $ hΓ₁ hξ) with hξ | hξ;
      . grind;
      . right;
        obtain ⟨ζ, hζ, rfl⟩ := Finset.LO.exists_of_mem_boxItr hξ;
        use ζ;
        grind;
  . intro ξ;
    simp only [Set.mem_union, Finset.mem_coe, Set.mem_insert_iff];
    rintro (hξ₁ | hξ₂);
    . have := hΓ₁ hξ₁;
      tauto;
    . have := hΓ₂ hξ₂;
      simp at this;
      tauto;

set_option linter.style.multiGoal false in
lemma truthlemma {X : (miniCanonicalModel φ).World} (q_sub : ψ ∈ φ.subformulas) :
  Satisfies (miniCanonicalModel φ) X ψ ↔ ψ ∈ X := by
  induction ψ generalizing X with
  | hatom => simp [Satisfies];
  | hfalsum => simp [Satisfies];
  | himp ψ χ ihq ihr =>
    constructor;
    . contrapose;
      intro h;
      apply Satisfies.imp_def.not.mpr;
      push_neg;
      constructor;
      . apply ihq ?_ |>.mpr;
        apply iff_not_mem_imp ?_ ?_ ?_ |>.mp h |>.1;
        all_goals grind;
      . apply ihr ?_ |>.not.mpr;
        apply iff_not_mem_compl ?_ |>.not.mpr;
        push_neg;
        apply iff_not_mem_imp ?_ ?_ ?_ |>.mp h |>.2;
        all_goals grind;
    . contrapose!;
      intro h;
      replace h := Satisfies.imp_def.not.mp h; push_neg at h;
      obtain ⟨hq, hr⟩ := h;
      replace hq : ψ ∈ X := ihq ?_ |>.mp hq;
      replace hr : χ ∉ X := ihr ?_ |>.not.mp hr;
      apply iff_not_mem_imp ?_ ?_ ?_ |>.mpr;
      . constructor;
        . assumption;
        . apply iff_mem_compl ?_ |>.mp hr;
          grind;
      all_goals grind;
  | hbox ψ ih =>
    constructor;
    . contrapose;
      intro h;
      obtain ⟨Y, hY₁⟩ := lindenbaum (Ψ := φ.subformulas) (truthlemma_lemma1 q_sub) (truthlemma_lemma2 q_sub h);
      simp only [Finset.union_subset_iff] at hY₁;
      apply Satisfies.not_box_def.mpr;
      use Y;
      constructor;
      . constructor;
        . intros;
          constructor;
          . apply hY₁.1.1;
            simpa [Finset.LO.preboxItr];
          · apply hY₁.1.2;
            apply Finset.LO.mem_box_prebox_of_mem_of_mem_box;
            assumption;
        . use ψ;
          refine ⟨?_, ?_, ?_⟩;
          . simpa [Finset.LO.preboxItr, Finset.LO.boxItr];
          . simpa;
          . apply hY₁.2;
            simp;
      . apply ih ?_ |>.not.mpr;
        . apply iff_not_mem_compl (by grind) |>.not.mpr;
          push_neg;
          apply hY₁.2;
          simp;
        . grind;
    . intro h Y RXY;
      apply ih (by grind) |>.mpr;
      refine RXY.1 ψ ?_ h |>.1;
      simpa [Finset.LO.preboxItr, Finset.LO.boxItr];

instance FFP : Complete Modal.GL Kripke.FrameClass.finite_GL := ⟨by
  intro φ;
  contrapose;
  intro h;
  apply Semantics.set_models_iff.not.mpr;
  push_neg;
  use (miniCanonicalFrame φ);
  constructor;
  . apply Set.mem_setOf_eq.mpr;
    infer_instance;
  . apply ValidOnFrame.not_of_exists_model_world;
    obtain ⟨X, hX₁⟩ := lindenbaum (Φ := {-φ}) (Ψ := φ.subformulas)
      (by
        simp only [FormulaFinset.complementary, Finset.singleton_subset_iff, Finset.mem_union, Finset.mem_image];
        right;
        use φ;
        grind;
      )
      (FormulaFinset.unprovable_iff_singleton_compl_consistent.mpr h);
    use (miniCanonicalModel φ), X;
    constructor;
    . tauto;
    . apply truthlemma ?_ |>.not.mpr;
      apply iff_not_mem_compl ?_ |>.not.mpr
      . push_neg;
        apply hX₁;
        tauto;
      all_goals grind;
⟩

theorem finite_completeness_TFAE : [
  Modal.GL ⊢ φ,
  FrameClass.finite_GL ⊧ φ,
  ∀ F : Kripke.Frame, [F.IsFinite] → [F.IsTransitive] → [F.IsIrreflexive] → [F.IsRooted] → F ⊧ φ,
  ∀ M : Kripke.Model, [M.IsFinite] → [M.IsTransitive] → [M.IsIrreflexive] → [M.IsRooted] → M.root.1 ⊧ φ,
].TFAE := by
  tfae_have 1 → 2 := by apply Sound.sound;
  tfae_have 2 → 1 := by apply Complete.complete;
  tfae_have 2 → 3 := by
    intro h F _ _ Fcwf ⟨r, hr⟩ _;
    apply h;
    exact {}
  tfae_have 3 → 4 := by
    intro h F _ _ _ r;
    apply h;
  tfae_have 4 → 2 := by
    rintro H F ⟨_, F_trans, F_irrefl⟩ V x;
    let M : Kripke.Model := ⟨F, V⟩;
    simpa [Unique.uniq] using Model.pointGenerate.pMorphism M x |>.modal_equivalence _ |>.mp $ H (M↾x);
  tfae_finish;

lemma iff_unprovable_exists_finite_rooted_model : Modal.GL ⊬ φ ↔ ∃ M : Model, ∃ _ : M.IsFinite, ∃ _ : M.IsTransitive, ∃ _ : M.IsIrreflexive, ∃ _ : M.IsRooted, ¬M.root.1 ⊧ φ := by
  apply Iff.not_left;
  apply Iff.trans $ finite_completeness_TFAE (φ := φ) |>.out 0 3;
  push_neg;
  tauto;

theorem fintype_completeness_TFAE : [
  Modal.GL ⊢ φ,
  ∀ F : Kripke.Frame, [Fintype F] → [F.IsTransitive] → [F.IsIrreflexive] → [F.IsRooted] → F ⊧ φ,
  ∀ M : Kripke.Model, [Fintype M] → [M.IsTransitive] → [M.IsIrreflexive] → [M.IsRooted] → M.root.1 ⊧ φ,
].TFAE := by
  tfae_have 1 → 2 := by
    rintro h F _ _ _ _ _;
    have := finite_completeness_TFAE.out 0 2 |>.mp h;
    apply this;
  tfae_have 2 → 3 := by
    intro h F _ _ _ _;
    apply h;
  tfae_have 3 → 1 := by
    intro h;
    apply finite_completeness_TFAE (φ := φ) |>.out 3 0 |>.mp;
    intro M _;
    have : Fintype M := Fintype.ofFinite M;
    apply h;
  tfae_finish;

lemma iff_unprovable_exists_fintype_rooted_model : Modal.GL ⊬ φ ↔ ∃ M : Model, ∃ _ : Fintype M, ∃ _ : M.IsTransitive, ∃ _ : M.IsIrreflexive, ∃ _ : M.IsRooted, ¬M.root.1 ⊧ φ := by
  apply Iff.not_left;
  apply Iff.trans $ fintype_completeness_TFAE (φ := φ) |>.out 0 2;
  push_neg;
  tauto;

end GL.Kripke

end LO.Modal
end
