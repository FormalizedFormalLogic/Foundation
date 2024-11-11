import Foundation.Modal.Complemental
import Foundation.Modal.Kripke.GL.Definability

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

namespace GLCompleteFrame

lemma irreflexive : Irreflexive (miniCanonicalFrame φ).Rel := by simp [Irreflexive];

lemma transitive : Transitive (miniCanonicalFrame φ).Rel := by
  simp;
  rintro X Y Z ⟨RXY, ⟨χ, _, _, _⟩⟩ ⟨RYZ, _⟩;
  constructor;
  . rintro ψ hq₁ hq₂;
    exact RYZ ψ hq₁ $ RXY ψ hq₁ hq₂ |>.2;
  . use χ;
    refine ⟨by assumption, by assumption, ?_⟩;
    exact RYZ χ (by assumption) (by assumption) |>.2;

end GLCompleteFrame


abbrev miniCanonicalModel (φ : Formula ℕ) : Kripke.Model where
  toFrame := miniCanonicalFrame φ |>.toFrame
  Val X a := (atom a) ∈ X.formulae


lemma truthlemma.lemma1
  {X : CCF (Hilbert.GL ℕ) φ.subformulae} (hq : □ψ ∈ φ.subformulae)
  : ((X.formulae.prebox ∪ X.formulae.prebox.box) ∪ {□ψ, -ψ}) ⊆ φ.subformulae⁻ := by
  simp only [Formulae.complementary];
  intro χ hr;
  simp [Finset.mem_union] at hr;
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
    right; simp;
    use ψ;
    constructor;
    . exact subformulae.mem_box hq;
    . rfl;

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
    simp;
    intro χ hr;
    have := hΓ₁ _ hr; simp at this;
    tauto;
  )) this;
  have : _ ⊢! ⋀□'(X.formulae.prebox.toList) ➝ □ψ := imp_trans''! (conjconj_provable! (by
    intro ψ hq;
    simp at hq;
    obtain ⟨χ, hr, rfl⟩ := hq;
    rcases hr with (hr | ⟨χ, hr, rfl⟩);
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
      simp [Satisfies];
      constructor;
      . apply ihq (subformulae.mem_imp₁ q_sub) |>.mpr;
        exact iff_not_mem_imp q_sub (subformulae.mem_imp₁ q_sub) (subformulae.mem_imp₂ q_sub) |>.mp h |>.1;
      . apply ihr (subformulae.mem_imp₂ q_sub) |>.not.mpr;
        have := iff_not_mem_imp q_sub (subformulae.mem_imp₁ q_sub) (subformulae.mem_imp₂ q_sub) |>.mp h |>.2;
        exact iff_mem_compl (subformulae.mem_imp₂ q_sub) |>.not.mpr (by simpa using this);
    . contrapose;
      intro h; simp [Satisfies] at h;
      obtain ⟨hq, hr⟩ := h;
      replace hq := ihq (subformulae.mem_imp₁ q_sub) |>.mp hq;
      replace hr := ihr (subformulae.mem_imp₂ q_sub) |>.not.mp hr;
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
      simp [Satisfies];
      use Y;
      constructor;
      . intro χ _ hr_sub;
        constructor;
        . apply hY₁.1.1; simpa;
        . apply hY₁.1.2; simpa;
      . use ψ;
        refine ⟨q_sub, h, ?_, ?_⟩;
        . apply hY₁.2; simp;
        . apply ih (subformulae.mem_box q_sub) |>.not.mpr;
          exact iff_mem_compl (subformulae.mem_box q_sub) |>.not.mpr $ by simp; apply hY₁.2; simp;
    . intro h Y RXY;
      apply ih (subformulae.mem_box q_sub) |>.mpr;
      simp at RXY;
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
  . exact ⟨GLCompleteFrame.transitive, GLCompleteFrame.irreflexive⟩;
  . simp [Formula.Kripke.ValidOnFrame, Formula.Kripke.ValidOnModel];
    obtain ⟨X, hX₁⟩ := lindenbaum (S := φ.subformulae) (X := {-φ})
      (by
        simp [Formulae.complementary];
        right; use φ; constructor <;> simp;
      )
      (Formulae.unprovable_iff_singleton_compl_consistent.mp h);
    use (miniCanonicalModel φ).Val, X;
    apply truthlemma (by simp) |>.not.mpr;
    exact iff_mem_compl (by simp) |>.not.mpr $ by
      simp;
      apply hX₁;
      tauto;
⟩

instance ffp : Kripke.FiniteFrameProperty (Hilbert.GL ℕ) TransitiveIrreflexiveFiniteFrameClass where
  complete := complete
  sound := finite_sound

end Hilbert.GL.Kripke

end LO.Modal
