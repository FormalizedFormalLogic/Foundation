import Foundation.Modal.Entailment.GL
import Foundation.Modal.ComplementClosedConsistentFinset
import Foundation.Modal.Kripke.Hilbert.GL.Soundness

namespace LO.Modal

open Kripke
open Entailment
open Formula
open Entailment Entailment.FiniteContext
open Formula.Kripke
open ComplementClosedConsistentFinset

namespace Hilbert.GL.Kripke

variable {φ ψ : Formula ℕ}

abbrev miniCanonicalFrame (φ : Formula ℕ) : Kripke.Frame where
  World := ComplementClosedConsistentFinset Hilbert.GL φ.subformulas
  Rel X Y :=
    (∀ ψ ∈ □''⁻¹φ.subformulas, □ψ ∈ X → (ψ ∈ Y ∧ □ψ ∈ Y)) ∧
    (∃ χ ∈ □''⁻¹φ.subformulas, □χ ∉ X ∧ □χ ∈ Y)

namespace miniCanonicalFrame

instance : Finite (miniCanonicalFrame φ).World := inferInstance

instance : IsIrrefl _ (miniCanonicalFrame φ).Rel := ⟨by simp [Irreflexive]⟩

instance : IsTrans _ (miniCanonicalFrame φ).Rel := ⟨by
  rintro X Y Z ⟨RXY, ⟨χ, _, _, _⟩⟩ ⟨RYZ, _⟩;
  constructor;
  . rintro ψ hq₁ hq₂;
    exact RYZ ψ hq₁ $ RXY ψ hq₁ hq₂ |>.2;
  . use χ;
    refine ⟨by assumption, by assumption, ?_⟩;
    exact RYZ χ (by assumption) (by assumption) |>.2;
⟩

end miniCanonicalFrame


abbrev miniCanonicalModel (φ : Formula ℕ) : Kripke.Model where
  toFrame := miniCanonicalFrame φ
  Val X a := (atom a) ∈ X


lemma truthlemma_lemma1
  {X : ComplementClosedConsistentFinset Hilbert.GL φ.subformulas} (hq : □ψ ∈ φ.subformulas)
  : ((X.1.prebox ∪ X.1.prebox.box) ∪ {□ψ, -ψ}) ⊆ φ.subformulas⁻ := by
  intro χ hr;
  replace hr : χ = □ψ ∨ □χ ∈ X ∨ (∃ a, □a ∈ X ∧ □a = χ) ∨ χ = -ψ := by simpa using hr;
  rcases hr with (rfl | hp | ⟨χ, hr, rfl⟩ | rfl);
  . apply Finset.mem_union.mpr;
    tauto;
  . have := X.closed.subset hp;
    have := FormulaFinset.complementary_mem_box (by apply subformulas.mem_imp₁) this;
    apply Finset.mem_union.mpr;
    left;
    exact subformulas.mem_box this;
  . exact X.closed.subset hr;
  . apply Finset.mem_union.mpr;
    right;
    apply Finset.mem_image.mpr;
    use ψ;
    constructor;
    . exact subformulas.mem_box hq;
    . tauto;


lemma truthlemma_lemma2
  {X : ComplementClosedConsistentFinset Hilbert.GL φ.subformulas}
  (hq₁ : □ψ ∈ φ.subformulas)
  (hq₂ : □ψ ∉ X)
  : FormulaFinset.Consistent Hilbert.GL ((X.1.prebox ∪ X.1.prebox.box) ∪ {□ψ, -ψ}) := by
  apply FormulaFinset.intro_union_consistent;
  rintro Γ₁ Γ₂ ⟨hΓ₁, hΓ₂⟩;

  replace hΓ₂ : ∀ χ ∈ Γ₂, χ = □ψ ∨ χ = -ψ := by
    intro χ hr;
    simpa using hΓ₂ χ hr;

  by_contra hC;
  have : Γ₁ ⊢[_]! ⋀Γ₂ ➝ ⊥ := provable_iff.mpr $ CK!_iff_CC!.mp hC;
  have : Γ₁ ⊢[_]! (□ψ ⋏ -ψ) ➝ ⊥ := C!_trans (by
    suffices Γ₁ ⊢[Hilbert.GL]! ⋀[□ψ, -ψ] ➝ ⋀Γ₂ by
      simpa only [ne_eq, List.cons_ne_self, not_false_eq_true, List.conj₂_cons_nonempty, List.conj₂_singleton];
    apply CConj₂Conj₂!_of_subset;
    simpa using hΓ₂;
  ) this;
  have : Γ₁ ⊢[_]! □ψ ➝ -ψ ➝ ⊥ := CK!_iff_CC!.mp this;
  have : Γ₁ ⊢[Hilbert.GL]! □ψ ➝ ψ := by
    rcases Formula.complement.or (φ := ψ) with (hp | ⟨ψ, rfl⟩);
    . rw [hp] at this;
      exact C!_trans this dne!;
    . simpa only [complement] using this;
  have : (□'Γ₁) ⊢[_]! □(□ψ ➝ ψ) := contextual_nec! this;
  have : (□'Γ₁) ⊢[_]! □ψ := axiomL! ⨀ this;
  have : _ ⊢! ⋀□'Γ₁ ➝ □ψ := provable_iff.mp this;
  have : _ ⊢! ⋀□'(X.1.prebox ∪ X.1.prebox.box |>.toList) ➝ □ψ := C!_trans (CConj₂Conj₂!_of_subset (by
    intro χ hχ;
    obtain ⟨ξ, hξ, rfl⟩ := List.exists_of_box hχ;
    apply List.box_mem_of;
    simp_all;
  )) this;
  have : _ ⊢! ⋀□'(X.1.prebox.toList) ➝ □ψ := C!_trans (CConj₂Conj₂!_of_provable (by
    intro χ hχ;
    obtain ⟨ξ, hξ, rfl⟩ := List.exists_of_box hχ;
    replace hξ : □ξ ∈ ↑X ∨ ∃ a, □a ∈ ↑X ∧ □a = ξ := by simpa using hξ;
    rcases hξ with (hξ | ⟨ξ, hξ, rfl⟩);
    . apply FiniteContext.by_axm!;
      apply List.box_mem_of;
      simpa;
    . apply axiomFour'!;
      apply FiniteContext.by_axm!;
      apply List.box_mem_of;
      simpa;
  )) this;
  have : X *⊢[Hilbert.GL]! □ψ := by
    apply Context.provable_iff.mpr;
    use □'X.1.prebox.toList;
    constructor;
    . intro ψ hψ;
      obtain ⟨ξ, hξ, rfl⟩ := List.exists_of_box hψ;
      simp_all;
    . assumption;
  have : □ψ ∈ X := membership_iff hq₁ |>.mpr this;
  contradiction;

lemma truthlemma {X : (miniCanonicalModel φ).World} (q_sub : ψ ∈ φ.subformulas) :
  Satisfies (miniCanonicalModel φ) X ψ ↔ ψ ∈ X := by
  induction ψ using Formula.rec' generalizing X with
  | hatom => simp [Satisfies];
  | hfalsum => simp [Satisfies];
  | himp ψ χ ihq ihr =>
    constructor;
    . contrapose;
      intro h;
      apply Satisfies.imp_def.not.mpr;
      push_neg;
      constructor;
      . apply ihq (subformulas.mem_imp₁ q_sub) |>.mpr;
        exact iff_not_mem_imp q_sub (subformulas.mem_imp₁ q_sub) (subformulas.mem_imp₂ q_sub) |>.mp h |>.1;
      . apply ihr (subformulas.mem_imp₂ q_sub) |>.not.mpr;
        have := iff_not_mem_imp q_sub (subformulas.mem_imp₁ q_sub) (subformulas.mem_imp₂ q_sub) |>.mp h |>.2;
        exact iff_mem_compl (subformulas.mem_imp₂ q_sub) |>.not.mpr (by simpa using this);
    . contrapose;
      intro h;
      replace h := Satisfies.imp_def.not.mp h; push_neg at h;
      obtain ⟨hq, hr⟩ := h;
      replace hq : ψ ∈ X := ihq (subformulas.mem_imp₁ q_sub) |>.mp hq;
      replace hr : χ ∉ X := ihr (subformulas.mem_imp₂ q_sub) |>.not.mp hr;
      apply iff_not_mem_imp q_sub (subformulas.mem_imp₁ q_sub) (subformulas.mem_imp₂ q_sub) |>.mpr;
      constructor;
      . assumption;
      . simpa using iff_mem_compl (subformulas.mem_imp₂ q_sub) |>.not.mp (by simpa using hr);
  | hbox ψ ih =>
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
        . apply iff_mem_compl (subformulas.mem_box q_sub) |>.not.mpr;
          push_neg;
          apply hY₁.2;
          simp;
        . exact subformulas.mem_box q_sub;
    . intro h Y RXY;
      apply ih (subformulas.mem_box q_sub) |>.mpr;
      refine RXY.1 ψ ?_ h |>.1;
      assumption;

instance finiteComplete : Complete Hilbert.GL Kripke.FrameClass.finite_trans_irrefl := ⟨by
  intro φ;
  contrapose;
  intro h;
  apply Semantics.set_models_iff.not.mpr;
  push_neg;
  use (miniCanonicalFrame φ);
  constructor;
  . exact ⟨inferInstance, inferInstance, inferInstance⟩;
  . apply ValidOnFrame.not_of_exists_model_world;
    obtain ⟨X, hX₁⟩ := lindenbaum (Φ := {-φ}) (Ψ := φ.subformulas)
      (by
        simp only [FormulaFinset.complementary, Finset.singleton_subset_iff, Finset.mem_union, Finset.mem_image];
        right;
        use φ;
        constructor <;> simp;
      )
      (FormulaFinset.unprovable_iff_singleton_compl_consistent.mpr h);
    use (miniCanonicalModel φ), X;
    constructor;
    . tauto;
    . apply truthlemma (by simp) |>.not.mpr;
      exact iff_mem_compl (by simp) |>.not.mpr $ by
        push_neg;
        apply hX₁;
        tauto;
⟩

end LO.Modal.Hilbert.GL.Kripke
