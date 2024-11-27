import Foundation.Modal.Hilbert.Complemental
import Foundation.Modal.Kripke.GL.Definability
import Foundation.Modal.Hilbert.WeakerThan.K4_GL

namespace LO.Modal

namespace Hilbert.GL.Kripke

open Formula
open System System.FiniteContext
open Formula.Kripke
open ComplementaryClosedConsistentFormulae

variable {φ ψ : Formula ℕ}

abbrev miniCanonicalFrame (φ : Formula ℕ) : Kripke.FiniteFrame where
  World := CCF (Hilbert.GL ℕ) φ.subformulae
  Rel X Y :=
    (∀ ψ ∈ □''⁻¹φ.subformulae, □ψ ∈ X.formulae → (ψ ∈ Y.formulae ∧ □ψ ∈ Y.formulae)) ∧
    (∃ χ ∈ □''⁻¹φ.subformulae, □χ ∉ X.formulae ∧ □χ ∈ Y.formulae)

namespace miniCanonicalFrame

lemma is_irreflexive : Irreflexive (miniCanonicalFrame φ).Rel := by simp [Irreflexive];

lemma is_transitive : Transitive (miniCanonicalFrame φ).Rel := by
  rintro X Y Z ⟨RXY, ⟨χ, _, _, _⟩⟩ ⟨RYZ, _⟩;
  constructor;
  . rintro ψ hq₁ hq₂;
    exact RYZ ψ hq₁ $ RXY ψ hq₁ hq₂ |>.2;
  . use χ;
    refine ⟨by assumption, by assumption, ?_⟩;
    exact RYZ χ (by assumption) (by assumption) |>.2;

end miniCanonicalFrame


abbrev miniCanonicalModel (φ : Formula ℕ) : Kripke.Model where
  toFrame := miniCanonicalFrame φ |>.toFrame
  Val X a := (atom a) ∈ X.formulae


lemma truthlemma.lemma1
  {X : CCF (Hilbert.GL ℕ) φ.subformulae} (hq : □ψ ∈ φ.subformulae)
  : ((X.formulae.prebox ∪ X.formulae.prebox.box) ∪ {□ψ, -ψ}) ⊆ φ.subformulae⁻ := by
  intro χ hr;
  replace hr : χ = □ψ ∨ □χ ∈ X.formulae ∨ (∃ a, □a ∈ X.formulae ∧ □a = χ) ∨ χ = -ψ := by simpa using hr;
  rcases hr with (rfl | hp | ⟨χ, hr, rfl⟩ | rfl);
  . apply Finset.mem_union.mpr;
    tauto;
  . have := X.closed.subset hp;
    have := Formulae.complementary_mem_box (by apply subformulae.mem_imp₁) this;
    apply Finset.mem_union.mpr;
    left;
    exact subformulae.mem_box this;
  . exact X.closed.subset hr;
  . apply Finset.mem_union.mpr;
    right;
    apply Finset.mem_image.mpr;
    use ψ;
    constructor;
    . exact subformulae.mem_box hq;
    . tauto;

lemma truthlemma.lemma2
  {X : CCF (Hilbert.GL ℕ) φ.subformulae} (hq₁ : □ψ ∈ φ.subformulae) (hq₂ : □ψ ∉ X.formulae)
  : Formulae.Consistent (Hilbert.GL ℕ) ((X.formulae.prebox ∪ X.formulae.prebox.box) ∪ {□ψ, -ψ}) := by
  apply Formulae.intro_union_consistent;
  rintro Γ₁ Γ₂ ⟨hΓ₁, hΓ₂⟩;

  replace hΓ₂ : ∀ χ ∈ Γ₂, χ = □ψ ∨ χ = -ψ := by
    intro χ hr;
    simpa using hΓ₂ χ hr;

  by_contra hC;
  have : Γ₁ ⊢[_]! ⋀Γ₂ ➝ ⊥ := provable_iff.mpr $ and_imply_iff_imply_imply'!.mp hC;
  have : Γ₁ ⊢[_]! (□ψ ⋏ -ψ) ➝ ⊥ := imp_trans''! (by
    suffices Γ₁ ⊢[(Hilbert.GL ℕ)]! ⋀[□ψ, -ψ] ➝ ⋀Γ₂ by
      simpa only [ne_eq, List.cons_ne_self, not_false_eq_true, List.conj₂_cons_nonempty, List.conj₂_singleton];
    apply conjconj_subset!;
    simpa using hΓ₂;
  ) this;
  have : Γ₁ ⊢[_]! □ψ ➝ -ψ ➝ ⊥ := and_imply_iff_imply_imply'!.mp this;
  have : Γ₁ ⊢[(Hilbert.GL ℕ)]! □ψ ➝ ψ := by
    rcases Formula.complement.or (φ := ψ) with (hp | ⟨ψ, rfl⟩);
    . rw [hp] at this;
      exact imp_trans''! this dne!;
    . simpa only [complement] using this;
  have : (□'Γ₁) ⊢[_]! □(□ψ ➝ ψ) := contextual_nec! this;
  have : (□'Γ₁) ⊢[_]! □ψ := axiomL! ⨀ this;
  have : _ ⊢! ⋀□'Γ₁ ➝ □ψ := provable_iff.mp this;
  have : _ ⊢! ⋀□'(X.formulae.prebox ∪ X.formulae.prebox.box |>.toList) ➝ □ψ := imp_trans''! (conjconj_subset! (by
    suffices ∀ χ ∈ Γ₁, □χ ∈ X.formulae ∨ ∃ χ', □χ' ∈ X.formulae ∧ □χ' = χ by simpa;
    intro χ hr;
    simpa using hΓ₁ _ hr;
  )) this;
  have : _ ⊢! ⋀□'(X.formulae.prebox.toList) ➝ □ψ := imp_trans''! (conjconj_provable! (by
    suffices ∀ χ, (□χ ∈ X.formulae ∨ ∃ χ', □χ' ∈ X.formulae ∧ □χ' = χ) → (□'^[1](Finset.premultibox 1 X.formulae).toList) ⊢[Hilbert.GL ℕ]! □χ by simpa;
    rintro χ (hχ | ⟨χ, hχ, rfl⟩);
    . apply FiniteContext.by_axm!;
      simpa;
    . apply axiomFour'!;
      apply FiniteContext.by_axm!;
      simpa;
  )) this;
  have : X.formulae *⊢[(Hilbert.GL ℕ)]! □ψ := by
    apply Context.provable_iff.mpr;
    use □'X.formulae.prebox.toList;
    constructor;
    . simp;
    . assumption;
  have : □ψ ∈ X.formulae := membership_iff hq₁ |>.mpr this;
  contradiction;

lemma truthlemma {X : (miniCanonicalModel φ).World} (q_sub : ψ ∈ φ.subformulae) :
  Satisfies (miniCanonicalModel φ) X ψ ↔ ψ ∈ X.formulae := by
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
      . apply ihq (subformulae.mem_imp₁ q_sub) |>.mpr;
        exact iff_not_mem_imp q_sub (subformulae.mem_imp₁ q_sub) (subformulae.mem_imp₂ q_sub) |>.mp h |>.1;
      . apply ihr (subformulae.mem_imp₂ q_sub) |>.not.mpr;
        have := iff_not_mem_imp q_sub (subformulae.mem_imp₁ q_sub) (subformulae.mem_imp₂ q_sub) |>.mp h |>.2;
        exact iff_mem_compl (subformulae.mem_imp₂ q_sub) |>.not.mpr (by simpa using this);
    . contrapose;
      intro h;
      replace h := Satisfies.imp_def.not.mp h; push_neg at h;
      obtain ⟨hq, hr⟩ := h;
      replace hq : ψ ∈ X.formulae := ihq (subformulae.mem_imp₁ q_sub) |>.mp hq;
      replace hr : χ ∉ X.formulae := ihr (subformulae.mem_imp₂ q_sub) |>.not.mp hr;
      apply iff_not_mem_imp q_sub (subformulae.mem_imp₁ q_sub) (subformulae.mem_imp₂ q_sub) |>.mpr;
      constructor;
      . assumption;
      . simpa using iff_mem_compl (subformulae.mem_imp₂ q_sub) |>.not.mp (by simpa using hr);
  | hbox ψ ih =>
    constructor;
    . contrapose;
      intro h;
      obtain ⟨Y, hY₁⟩ := lindenbaum (S := φ.subformulae) (truthlemma.lemma1 q_sub) (truthlemma.lemma2 q_sub h);
      simp only [Finset.union_subset_iff] at hY₁;
      apply Satisfies.box_def.not.mpr;
      push_neg;
      use Y;
      constructor;
      . constructor;
        . aesop;
        . aesop;
      . apply ih ?_ |>.not.mpr;
        . apply iff_mem_compl (subformulae.mem_box q_sub) |>.not.mpr;
          push_neg;
          apply hY₁.2;
          simp;
        . exact subformulae.mem_box q_sub;
    . intro h Y RXY;
      apply ih (subformulae.mem_box q_sub) |>.mpr;
      refine RXY.1 ψ ?_ h |>.1;
      assumption;

open Modal.Kripke

instance complete : Complete (Hilbert.GL ℕ) TransitiveIrreflexiveFiniteFrameClass := ⟨by
  intro φ;
  contrapose;
  intro h;
  apply notValidOnFiniteFrameClass_of_exists_finite_frame;
  use (miniCanonicalFrame φ);
  constructor;
  . exact ⟨miniCanonicalFrame.is_transitive, miniCanonicalFrame.is_irreflexive⟩;
  . apply ValidOnFrame.not_valid_iff_exists_valuation_world.mpr;
    obtain ⟨X, hX₁⟩ := lindenbaum (S := φ.subformulae) (X := {-φ})
      (by
        simp only [Formulae.complementary, Finset.singleton_subset_iff, Finset.mem_union, Finset.mem_image];
        right;
        use φ;
        constructor <;> simp;
      )
      (Formulae.unprovable_iff_singleton_compl_consistent.mp h);
    use (miniCanonicalModel φ).Val, X;
    apply truthlemma (by simp) |>.not.mpr;
    exact iff_mem_compl (by simp) |>.not.mpr $ by
      push_neg;
      apply hX₁;
      tauto;
⟩

instance ffp : Kripke.FiniteFrameProperty (Hilbert.GL ℕ) TransitiveIrreflexiveFiniteFrameClass where
  complete := complete
  sound := finite_sound

end Hilbert.GL.Kripke

end LO.Modal
