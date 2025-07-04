import Foundation.Modal.Entailment.GL
import Foundation.Modal.ComplementClosedConsistentFinset
import Foundation.Modal.Kripke.Logic.GL.Soundness
import Foundation.Modal.Kripke.Hilbert
import Foundation.Modal.Kripke.Logic.K4

namespace LO.Modal

open Kripke
open LO.Entailment LO.Entailment.FiniteContext LO.Modal.Entailment
open Formula
open Entailment Entailment.FiniteContext
open Formula.Kripke
open ComplementClosedConsistentFinset

namespace Logic.GL.Kripke

variable {φ ψ : Formula ℕ}

abbrev miniCanonicalFrame (φ : Formula ℕ) : Kripke.Frame where
  World := ComplementClosedConsistentFinset Logic.GL φ.subformulas
  Rel X Y :=
    (∀ ψ ∈ φ.subformulas.prebox, □ψ ∈ X → (ψ ∈ Y ∧ □ψ ∈ Y)) ∧
    (∃ χ ∈ φ.subformulas.prebox, □χ ∉ X ∧ □χ ∈ Y)

namespace miniCanonicalFrame

instance : (miniCanonicalFrame φ).IsFinite := inferInstance

instance : (miniCanonicalFrame φ).IsIrreflexive := ⟨by simp [Irreflexive]⟩

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
  Val X a := (atom a) ∈ X


lemma truthlemma_lemma1
  {X : ComplementClosedConsistentFinset Logic.GL φ.subformulas} (hq : □ψ ∈ φ.subformulas)
  : ((X.1.prebox ∪ X.1.prebox.box) ∪ {□ψ, -ψ}) ⊆ φ.subformulas⁻ := by
  intro χ hr;
  replace hr : χ = □ψ ∨ □χ ∈ X ∨ (∃ a, □a ∈ X ∧ □a = χ) ∨ χ = -ψ := by simpa using hr;
  rcases hr with (rfl | hp | ⟨χ, hr, rfl⟩ | rfl);
  . apply Finset.mem_union.mpr;
    tauto;
  . have := X.closed.subset hp;
    have := FormulaFinset.complementary_mem_box (by subformula) this;
    apply Finset.mem_union.mpr;
    subformula;
  . exact X.closed.subset hr;
  . apply Finset.mem_union.mpr;
    right;
    apply Finset.mem_image.mpr;
    use ψ;
    subformula;

lemma truthlemma_lemma2
  {X : ComplementClosedConsistentFinset Logic.GL φ.subformulas}
  (hψ₁ : □ψ ∈ φ.subformulas)
  (hψ₂ : □ψ ∉ X)
  : FormulaFinset.Consistent Logic.GL ((X.1.prebox ∪ X.1.prebox.box) ∪ {□ψ, -ψ}) := by
  apply FormulaFinset.intro_union_consistent;
  rintro Γ₁ Γ₂ hΓ₁ hΓ₂;
  by_contra hC;
  apply hψ₂;
  have := Context.deduct! $ Context.weakening! (Γ := Γ₁ ∪ Γ₂) (Δ := insert (-ψ) (insert (□ψ) Γ₁)) ?_ hC;
  . replace : (insert (□ψ) Γ₁) *⊢[Logic.GL]! ψ := of_imply_complement_bot this;
    replace := Context.deduct! this;
    replace : ↑Γ₁.box *⊢[Logic.GL]! □(□ψ ➝ ψ) := by simpa using Context.nec! this;
    replace := axiomL! ⨀ this;
    replace : (X.1.prebox.box ∪ X.1.prebox.multibox 2) *⊢[Logic.GL]! □ψ := Context.weakening! ?_ this;
    . replace : X.1.prebox.box *⊢[Logic.GL]! (X.1.prebox.multibox 2).conj ➝ □ψ := FConj_DT'.mpr $ by simpa using this;
      replace : X.1.prebox.box *⊢[Logic.GL]! (X.1.prebox.box).conj ➝ □ψ := C!_trans ?_ this;
      . replace := FConj_DT'.mp this;
        have : X *⊢[Logic.GL]! □ψ := Context.weakening! (by simp) this;
        exact membership_iff hψ₁ |>.mpr this;
      . apply CFconjFconj!_of_provable;
        intro ξ hξ;
        obtain ⟨ξ, h, rfl⟩ := Finset.exists_multibox_of_mem_multibox hξ;
        apply axiomFour'!;
        apply Context.by_axm!
        simpa using h;
    . simp only [Finset.coe_image, Function.iterate_one, Finset.coe_preimage, Box.multibox_succ, Set.image_subset_iff, Set.preimage_union, Box.box_injective, Set.preimage_image_eq];
      intro ξ hξ;
      simpa using hΓ₁ hξ;
  . intro ξ;
    simp only [Set.mem_union, Finset.mem_coe, Set.mem_insert_iff];
    rintro (hξ₁ | hξ₂);
    . have := hΓ₁ hξ₁;
      tauto;
    . have := hΓ₂ hξ₂;
      simp at this;
      tauto;

-- TODO: `subformula` tactic cannot handle, I don't know why.
lemma truthlemma {X : (miniCanonicalModel φ).World} (q_sub : ψ ∈ φ.subformulas) :
  Satisfies (miniCanonicalModel φ) X ψ ↔ ψ ∈ X := by
  induction ψ generalizing X with
  | hatom => simp [Satisfies];
  | hfalsum => simp [Satisfies];
  | himp ψ χ ihq ihr =>
    have : ψ ∈ φ.subformulas := subformulas.mem_imp q_sub |>.1;
    have : χ ∈ φ.subformulas := subformulas.mem_imp q_sub |>.2;
    constructor;
    . contrapose;
      intro h;
      apply Satisfies.imp_def.not.mpr;
      push_neg;
      constructor;
      . apply ihq (by subformula) |>.mpr;
        exact iff_not_mem_imp q_sub |>.mp h |>.1;
      . apply ihr (by subformula) |>.not.mpr;
        have := iff_not_mem_imp q_sub |>.mp h |>.2;
        exact iff_mem_compl (by subformula) |>.not.mpr (by simpa using this);
    . contrapose;
      intro h;
      replace h := Satisfies.imp_def.not.mp h; push_neg at h;
      obtain ⟨hq, hr⟩ := h;
      replace hq : ψ ∈ X := ihq (by subformula) |>.mp hq;
      replace hr : χ ∉ X := ihr (by subformula) |>.not.mp hr;
      apply iff_not_mem_imp q_sub |>.mpr;
      constructor;
      . assumption;
      . simpa using iff_mem_compl (by subformula) |>.not.mp (by simpa using hr);
  | hbox ψ ih =>
    have : ψ ∈ φ.subformulas := subformulas.mem_box q_sub;
    constructor;
    . contrapose;
      intro h;
      obtain ⟨Y, hY₁⟩ := lindenbaum (Ψ := φ.subformulas) (truthlemma_lemma1 q_sub) (truthlemma_lemma2 q_sub h);
      simp only [Finset.union_subset_iff] at hY₁;
      apply Satisfies.box_def.not.mpr;
      push_neg;
      use Y;
      constructor;
      . constructor;
        . aesop;
        . aesop;
      . apply ih ?_ |>.not.mpr;
        . apply iff_mem_compl (by subformula) |>.not.mpr;
          push_neg;
          apply hY₁.2;
          simp;
        . subformula;
    . intro h Y RXY;
      apply ih (by subformula) |>.mpr;
      refine RXY.1 ψ ?_ h |>.1;
      simpa;

instance finiteComplete : Complete Logic.GL Kripke.FrameClass.finite_GL := ⟨by
  intro φ;
  contrapose;
  intro h;
  apply Semantics.set_models_iff.not.mpr;
  push_neg;
  use (miniCanonicalFrame φ);
  constructor;
  . simp;
    infer_instance;
  . apply ValidOnFrame.not_of_exists_model_world;
    obtain ⟨X, hX₁⟩ := lindenbaum (Φ := {-φ}) (Ψ := φ.subformulas)
      (by
        simp only [FormulaFinset.complementary, Finset.singleton_subset_iff, Finset.mem_union, Finset.mem_image];
        right;
        use φ;
        subformula;
      )
      (FormulaFinset.unprovable_iff_singleton_compl_consistent.mpr h);
    use (miniCanonicalModel φ), X;
    constructor;
    . tauto;
    . apply truthlemma (by subformula) |>.not.mpr;
      exact iff_mem_compl (by subformula) |>.not.mpr $ by
        push_neg;
        apply hX₁;
        tauto;
⟩

end Logic.GL.Kripke

namespace Logic

open Formula
open Entailment
open Kripke

lemma GL.Kripke.finite_trans_irrefl : Logic.GL = FrameClass.finite_GL.logic := eq_hilbert_logic_frameClass_logic

end Logic


end LO.Modal
