import Foundation.Modal.Complemental
import Foundation.Modal.Kripke.Grz.Definability


namespace LO.Modal


namespace Formula

variable {α : Type u} [DecidableEq α]
variable {φ ψ : Formula ℕ}

noncomputable abbrev subformulaeGrz (φ : Formula α) := φ.subformulae ∪ (φ.subformulae.prebox.image (λ ψ => □(ψ ➝ □ψ)))

namespace subformulaeGrz

@[simp]
lemma mem_self : φ ∈ φ.subformulaeGrz := by simp [subformulaeGrz, subformulae.mem_self]

lemma mem_boximpbox (h : ψ ∈ φ.subformulae.prebox) : □(ψ ➝ □ψ) ∈ φ.subformulaeGrz := by simp_all [subformulaeGrz];

lemma mem_origin (h : ψ ∈ φ.subformulae) : ψ ∈ φ.subformulaeGrz := by simp_all [subformulaeGrz];

lemma mem_imp (h : (ψ ➝ χ) ∈ φ.subformulaeGrz) : ψ ∈ φ.subformulaeGrz ∧ χ ∈ φ.subformulaeGrz := by
  simp_all [subformulaeGrz];
  aesop;

lemma mem_imp₁ (h : (ψ ➝ χ) ∈ φ.subformulaeGrz) : ψ ∈ φ.subformulaeGrz := mem_imp h |>.1

lemma mem_imp₂ (h : (ψ ➝ χ) ∈ φ.subformulaeGrz) : χ ∈ φ.subformulaeGrz := mem_imp h |>.2

macro_rules | `(tactic| trivial) => `(tactic|
    first
    | apply mem_origin $ by assumption
    | apply mem_imp₁  $ by assumption
    | apply mem_imp₂  $ by assumption
  )

end subformulaeGrz

end Formula


namespace Hilbert.Grz.Kripke

open Formula
open System System.FiniteContext
open Formula.Kripke
open ComplementaryClosedConsistentFormulae

variable {φ ψ : Formula ℕ}

abbrev miniCanonicalFrame (φ : Formula ℕ) : Kripke.FiniteFrame where
  World := CCF (Hilbert.Grz ℕ) (φ.subformulaeGrz)
  Rel X Y :=
    (∀ ψ ∈ □''⁻¹(φ.subformulaeGrz), □ψ ∈ X.formulae → □ψ ∈ Y.formulae) ∧
    ((∀ ψ ∈ □''⁻¹(φ.subformulaeGrz), □ψ ∈ Y.formulae → □ψ ∈ X.formulae) → X = Y)

namespace miniCanonicalFrame

lemma reflexive : Reflexive (miniCanonicalFrame φ).Rel := by simp [Reflexive];

lemma transitive : Transitive (miniCanonicalFrame φ).Rel := by
  simp only [Transitive];
  rintro X Y Z ⟨RXY₁, RXY₂⟩ ⟨RYZ₁, RYZ₂⟩;
  constructor;
  . rintro ψ hq₁ hq₂;
    exact RYZ₁ ψ hq₁ $ RXY₁ ψ hq₁ hq₂;
  . intro h;
    have eXY : X = Y := RXY₂ $ by
      intro ψ hs hq;
      exact h ψ hs $ RYZ₁ ψ hs hq;
    have eYZ : Y = Z := RYZ₂ $ by
      intro ψ hs hq;
      exact RXY₁ ψ hs $ h ψ hs hq;
    subst_vars;
    tauto;

lemma antisymm : Antisymmetric (miniCanonicalFrame φ).Rel := by
  rintro X Y ⟨_, h₁⟩ ⟨h₂, _⟩;
  exact h₁ h₂;

end miniCanonicalFrame


abbrev miniCanonicalModel (φ : Formula ℕ) : Kripke.Model where
  toFrame := miniCanonicalFrame φ |>.toFrame
  Val X a := (atom a) ∈ X.formulae


lemma truthlemma.lemma1
  {X : CCF (Hilbert.Grz ℕ) (φ.subformulaeGrz)} (hq : □ψ ∈ φ.subformulae)
  : ((X.formulae.prebox.box) ∪ {□(ψ ➝ □ψ), -ψ}) ⊆ (φ.subformulaeGrz)⁻ := by
  simp only [Formulae.complementary];
  intro χ hr;
  simp [Finset.mem_union] at hr;
  apply Finset.mem_union.mpr;
  rcases hr with (rfl | ⟨χ, hr, rfl⟩ | rfl);
  . left;
    simp;
    tauto;
  . have := X.closed.subset hr;
    left;
    exact Formulae.complementary_mem_box subformulaeGrz.mem_imp₁ this;
  . right; simp;
    use ψ;
    constructor;
    . left;
      exact subformulae.mem_box hq;
    . rfl;

lemma truthlemma.lemma2
  {X : CCF (Hilbert.Grz ℕ) (φ.subformulaeGrz)} (hq₁ : □ψ ∈ φ.subformulae) (hq₂ : □ψ ∉ X.formulae)
  : Formulae.Consistent (Hilbert.Grz ℕ) ((X.formulae.prebox.box) ∪ {□(ψ ➝ □ψ), -ψ}) := by
    apply Formulae.intro_union_consistent;
    rintro Γ₁ Γ₂ ⟨hΓ₁, hΓ₂⟩;
    replace hΓ₂ : ∀ χ ∈ Γ₂, χ = □(ψ ➝ □ψ) ∨ χ = -ψ := by
      intro χ hr;
      simpa using hΓ₂ χ hr;

    by_contra hC;
    have : Γ₁ ⊢[(Hilbert.Grz ℕ)]! ⋀Γ₂ ➝ ⊥ := provable_iff.mpr $ and_imply_iff_imply_imply'!.mp hC;
    have : Γ₁ ⊢[(Hilbert.Grz ℕ)]! (□(ψ ➝ □ψ) ⋏ -ψ) ➝ ⊥ := imp_trans''! (by
      suffices Γ₁ ⊢[(Hilbert.Grz ℕ)]! ⋀[□(ψ ➝ □ψ), -ψ] ➝ ⋀Γ₂ by
        simpa only [ne_eq, List.cons_ne_self, not_false_eq_true, List.conj₂_cons_nonempty, List.conj₂_singleton];
      apply conjconj_subset!;
      simpa using hΓ₂;
    ) this;
    have : Γ₁ ⊢[(Hilbert.Grz ℕ)]! □(ψ ➝ □ψ) ➝ -ψ ➝ ⊥ := and_imply_iff_imply_imply'!.mp this;
    have : Γ₁ ⊢[(Hilbert.Grz ℕ)]! □(ψ ➝ □ψ) ➝ ψ := by
      rcases Formula.complement.or (φ := ψ) with (hp | ⟨ψ, rfl⟩);
      . rw [hp] at this;
        exact imp_trans''! this dne!;
      . simpa only [complement] using this;
    have : (□'Γ₁) ⊢[(Hilbert.Grz ℕ)]! □(□(ψ ➝ □ψ) ➝ ψ) := contextual_nec! this;
    have : (□'Γ₁) ⊢[(Hilbert.Grz ℕ)]! ψ := axiomGrz! ⨀ this;
    have : (□'□'Γ₁) ⊢[(Hilbert.Grz ℕ)]! □ψ := contextual_nec! this;
    -- TODO: `contextual_axiomFour`
    have : (Hilbert.Grz ℕ) ⊢! ⋀□'□'Γ₁ ➝ □ψ := provable_iff.mp this;
    have : (Hilbert.Grz ℕ) ⊢! □□⋀Γ₁ ➝ □ψ := imp_trans''! (imp_trans''! (distribute_multibox_conj! (n := 2)) $ conjconj_subset! (by simp)) this;
    have : (Hilbert.Grz ℕ) ⊢! □⋀Γ₁ ➝ □ψ := imp_trans''! axiomFour! this;
    have : (Hilbert.Grz ℕ) ⊢! ⋀□'Γ₁ ➝ □ψ := imp_trans''! collect_box_conj! this;
    have : (Hilbert.Grz ℕ) ⊢! ⋀□'(X.formulae.prebox.box |>.toList) ➝ □ψ := imp_trans''! (conjconj_subset! (by
      simp;
      intro χ hr;
      have := hΓ₁ _ hr; simp at this;
      tauto;
    )) this;
    have : (Hilbert.Grz ℕ) ⊢! ⋀□'(X.formulae.prebox.toList) ➝ □ψ := imp_trans''! (conjconj_provable! (by
      intro ψ hq;
      simp at hq;
      obtain ⟨χ, hr, rfl⟩ := hq;
      apply axiomFour'!;
      apply FiniteContext.by_axm!;
      simpa;
    )) this;
    have : X.formulae *⊢[(Hilbert.Grz ℕ)]! □ψ := by
      apply Context.provable_iff.mpr;
      use □'X.formulae.prebox.toList;
      constructor;
      . simp;
      . assumption;
    have : □ψ ∈ X.formulae := membership_iff (by trivial) |>.mpr this;
    contradiction;

-- TODO: syntactical proof
lemma truthlemma.lemma3 : (Hilbert.KT ℕ) ⊢! (φ ⋏ □(φ ➝ □φ)) ➝ □φ := by
  by_contra hC;
  have := (not_imp_not.mpr $ Hilbert.KT.Kripke.complete |>.complete) hC;
  simp at this;
  obtain ⟨F, F_refl, hF⟩ := this;
  simp [ValidOnFrame, ValidOnModel, Satisfies, Semantics.Realize] at hF;
  obtain ⟨V, x, h₁, h₂, ⟨y, Rxy, h₃⟩⟩ := hF;
  have := h₂ x (F_refl x);
  have := (this h₁) _ Rxy;
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
      . apply ihq (by aesop) |>.mpr;
        exact iff_not_mem_imp
          (hsub_qr := subformulaeGrz.mem_origin q_sub)
          (hsub_q := by simp [subformulaeGrz]; left; aesop)
          (hsub_r := by simp [subformulaeGrz]; left; aesop)
          |>.mp h |>.1;
      . apply ihr (by aesop) |>.not.mpr;
        have := iff_not_mem_imp
          (hsub_qr := subformulaeGrz.mem_origin q_sub)
          (hsub_q := by simp [subformulaeGrz]; left; aesop)
          (hsub_r := by simp [subformulaeGrz]; left; aesop)
          |>.mp h |>.2;
        exact iff_mem_compl (by simp [subformulaeGrz]; left; aesop) |>.not.mpr (by simpa using this);
    . contrapose;
      intro h; simp [Satisfies] at h;
      obtain ⟨hq, hr⟩ := h;
      replace hq := ihq (by aesop) |>.mp hq;
      replace hr := ihr (by aesop) |>.not.mp hr;
      apply iff_not_mem_imp
        (hsub_qr := subformulaeGrz.mem_origin q_sub)
        (hsub_q := by simp [subformulaeGrz]; left; aesop)
        (hsub_r := by simp [subformulaeGrz]; left; aesop) |>.mpr;
      constructor;
      . assumption;
      . simpa using iff_mem_compl (by simp [subformulaeGrz]; left; aesop) |>.not.mp (by simpa using hr);
  | hbox ψ ih =>
    constructor;
    . contrapose;
      by_cases w : ψ ∈ X.formulae;
      . intro h;
        obtain ⟨Y, hY⟩ := lindenbaum (S := φ.subformulaeGrz) (truthlemma.lemma1 q_sub) (truthlemma.lemma2 q_sub h);
        simp only [Finset.union_subset_iff] at hY;
        simp only [Satisfies]; push_neg;
        use Y;
        constructor;
        . constructor;
          . intro χ _ hr₂;
            apply hY.1;
            simpa;
          . apply imp_iff_not_or (b := X = Y) |>.mpr;
            left; push_neg;
            use (ψ ➝ □ψ);
            refine ⟨?_, ?_, ?_⟩;
            . simp_all;
            . apply hY.2; simp;
            . by_contra hC;
              have : ↑X.formulae *⊢[(Hilbert.Grz ℕ)]! ψ := membership_iff (by simp; left; aesop) |>.mp w;
              have : ↑X.formulae *⊢[(Hilbert.Grz ℕ)]! □(ψ ➝ □ψ) := membership_iff (by simp; right; assumption) |>.mp hC;
              have : ↑X.formulae *⊢[(Hilbert.Grz ℕ)]! (ψ ⋏ □(ψ ➝ □ψ)) ➝ □ψ := Context.of! $ Hilbert.KT_weakerThan_Grz truthlemma.lemma3;
              have : ↑X.formulae *⊢[(Hilbert.Grz ℕ)]! □ψ := this ⨀ and₃'! (by assumption) (by assumption);
              have : □ψ ∈ X.formulae := membership_iff (subformulaeGrz.mem_origin (by assumption)) |>.mpr this;
              contradiction;
        . apply ih (by aesop) |>.not.mpr;
          apply iff_mem_compl (subformulaeGrz.mem_origin (by aesop)) |>.not.mpr;
          simp;
          apply hY.2;
          simp;
      . intro _;
        simp only [Satisfies]; push_neg;
        use X;
        constructor;
        . exact miniCanonicalFrame.reflexive X;
        . exact ih (by aesop) |>.not.mpr w;
    . intro h Y RXY;
      apply ih (subformulae.mem_box q_sub) |>.mpr;
      have : ↑Y.formulae *⊢[(Hilbert.Grz ℕ)]! □ψ ➝ ψ := Context.of! $ axiomT!;
      have : ↑Y.formulae *⊢[(Hilbert.Grz ℕ)]! ψ := this ⨀ (membership_iff (by simp; left; trivial) |>.mp (RXY.1 ψ (by simp; tauto) h));
      exact membership_iff (by simp; left; exact subformulae.mem_box q_sub) |>.mpr this;

open Modal.Kripke

instance complete : Complete (Hilbert.Grz ℕ) (ReflexiveTransitiveAntisymmetricFiniteFrameClass) := ⟨by
  intro φ;
  contrapose;
  intro h;
  apply notValidOnFiniteFrameClass_of_exists_finite_frame;
  use (miniCanonicalFrame φ);
  constructor;
  . refine ⟨miniCanonicalFrame.reflexive, miniCanonicalFrame.transitive, miniCanonicalFrame.antisymm⟩;
  . simp only [ValidOnFrame.models_iff, ValidOnFrame, ValidOnModel.iff_models, ValidOnModel, Satisfies.iff_models];
    push_neg;
    obtain ⟨X, hX₁⟩ := lindenbaum (S := φ.subformulaeGrz) (X := {-φ})
      (by simp; apply Formulae.complementary_comp; simp)
      (Formulae.unprovable_iff_singleton_compl_consistent.mp h);
    use (miniCanonicalModel φ).Val, X;
    apply truthlemma (by simp) |>.not.mpr;
    exact iff_mem_compl (by simp) |>.not.mpr $ by
      simp;
      apply hX₁;
      tauto;
⟩

instance ffp : Kripke.FiniteFrameProperty (Hilbert.Grz ℕ) ReflexiveTransitiveAntisymmetricFiniteFrameClass where
  complete := complete
  sound := finite_sound

end Hilbert.Grz.Kripke

end LO.Modal
