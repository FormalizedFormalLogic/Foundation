import Foundation.Modal.Kripke.Hilbert.Grz.Soundness

namespace LO.Modal

namespace Formula

variable {α : Type u} [DecidableEq α]
variable {φ ψ : Formula ℕ}

noncomputable abbrev subformulasGrz (φ : Formula α) := φ.subformulas ∪ (φ.subformulas.prebox.image (λ ψ => □(ψ ➝ □ψ)))

namespace subformulasGrz

@[simp]
lemma mem_self : φ ∈ φ.subformulasGrz := by simp [subformulasGrz, subformulas.mem_self]

lemma mem_boximpbox (h : ψ ∈ φ.subformulas.prebox) : □(ψ ➝ □ψ) ∈ φ.subformulasGrz := by simp_all [subformulasGrz];

lemma mem_origin (h : ψ ∈ φ.subformulas) : ψ ∈ φ.subformulasGrz := by simp_all [subformulasGrz];

lemma mem_imp (h : (ψ ➝ χ) ∈ φ.subformulasGrz) : ψ ∈ φ.subformulasGrz ∧ χ ∈ φ.subformulasGrz := by
  simp_all [subformulasGrz];
  aesop;

lemma mem_imp₁ (h : (ψ ➝ χ) ∈ φ.subformulasGrz) : ψ ∈ φ.subformulasGrz := mem_imp h |>.1

lemma mem_imp₂ (h : (ψ ➝ χ) ∈ φ.subformulasGrz) : χ ∈ φ.subformulasGrz := mem_imp h |>.2

macro_rules | `(tactic| trivial) => `(tactic|
    first
    | apply mem_origin $ by assumption
    | apply mem_imp₁  $ by assumption
    | apply mem_imp₂  $ by assumption
  )

lemma mem_left (h : ψ ∈ φ.subformulas) : ψ ∈ φ.subformulasGrz := by
  unfold subformulasGrz;
  simp only [Finset.mem_union];
  left;
  tauto;



end subformulasGrz

end Formula



namespace Hilbert.Grz.Kripke

open Formula
open Formula.Kripke
open System
open System.Context
open ComplementClosedConsistentFinset

variable {φ ψ : Formula ℕ}

abbrev miniCanonicalFrame (φ : Formula ℕ) : Kripke.FiniteFrame where
  World := ComplementClosedConsistentFinset (Hilbert.Grz) (φ.subformulasGrz)
  Rel X Y :=
    (∀ ψ ∈ □''⁻¹(φ.subformulasGrz), □ψ ∈ X → □ψ ∈ Y) ∧
    ((∀ ψ ∈ □''⁻¹(φ.subformulasGrz), □ψ ∈ Y → □ψ ∈ X) → X = Y)

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

lemma antisymm : AntiSymmetric (miniCanonicalFrame φ).Rel := by
  rintro X Y ⟨_, h₁⟩ ⟨h₂, _⟩;
  exact h₁ h₂;

end miniCanonicalFrame


abbrev miniCanonicalModel (φ : Formula ℕ) : Kripke.Model where
  toFrame := miniCanonicalFrame φ |>.toFrame
  Val X a := (atom a) ∈ X


lemma truthlemma_lemma1
  {X : ComplementClosedConsistentFinset (Hilbert.Grz) (φ.subformulasGrz)} (hq : □ψ ∈ φ.subformulas)
  : ((X.1.prebox.box) ∪ {□(ψ ➝ □ψ), -ψ}) ⊆ (φ.subformulasGrz)⁻ := by
  simp only [FormulaFinset.complementary];
  intro χ hr;
  replace hr : χ = □(ψ ➝ □ψ) ∨ (∃ a, □a ∈ X ∧ □a = χ) ∨ χ = -ψ := by
    simpa [Finset.mem_union] using hr;
  apply Finset.mem_union.mpr;
  rcases hr with (rfl | ⟨χ, hr, rfl⟩ | rfl);
  . left;
    simp;
    tauto;
  . have := X.closed.subset hr;
    left;
    exact FormulaFinset.complementary_mem_box subformulasGrz.mem_imp₁ this;
  . right;
    simp;
    use ψ;
    constructor;
    . left;
      exact subformulas.mem_box hq;
    . rfl;

lemma truthlemma_lemma2
  {X : ComplementClosedConsistentFinset (Hilbert.Grz) (φ.subformulasGrz)} (hq₁ : □ψ ∈ φ.subformulas) (hq₂ : □ψ ∉ X)
  : FormulaFinset.Consistent (Hilbert.Grz) ((X.1.prebox.box) ∪ {□(ψ ➝ □ψ), -ψ}) := by
    apply FormulaFinset.intro_union_consistent;
    rintro Γ₁ Γ₂ ⟨hΓ₁, hΓ₂⟩;
    replace hΓ₂ : ∀ χ ∈ Γ₂, χ = □(ψ ➝ □ψ) ∨ χ = -ψ := by
      intro χ hr;
      simpa using hΓ₂ χ hr;

    by_contra hC;
    have : Γ₁ ⊢[(Hilbert.Grz)]! ⋀Γ₂ ➝ ⊥ := and_imply_iff_imply_imply'!.mp hC;
    have : Γ₁ ⊢[(Hilbert.Grz)]! (□(ψ ➝ □ψ) ⋏ -ψ) ➝ ⊥ := imp_trans''! (by
      suffices Γ₁ ⊢[(Hilbert.Grz)]! ⋀[□(ψ ➝ □ψ), -ψ] ➝ ⋀Γ₂ by
        simpa only [ne_eq, List.cons_ne_self, not_false_eq_true, List.conj₂_cons_nonempty, List.conj₂_singleton];
      apply conjconj_subset!;
      simpa using hΓ₂;
    ) this;
    have : Γ₁ ⊢[(Hilbert.Grz)]! □(ψ ➝ □ψ) ➝ -ψ ➝ ⊥ := and_imply_iff_imply_imply'!.mp this;
    have : Γ₁ ⊢[(Hilbert.Grz)]! □(ψ ➝ □ψ) ➝ ψ := by
      rcases Formula.complement.or (φ := ψ) with (hp | ⟨ψ, rfl⟩);
      . rw [hp] at this;
        exact imp_trans''! this dne!;
      . simpa only [complement] using this;
    have : (□'Γ₁) ⊢[(Hilbert.Grz)]! □(□(ψ ➝ □ψ) ➝ ψ) := contextual_nec! this;
    have : (□'Γ₁) ⊢[(Hilbert.Grz)]! ψ := axiomGrz! ⨀ this;
    have : (Hilbert.Grz) ⊢! ⋀□'□'Γ₁ ➝ □ψ := contextual_nec! this;
    have : (Hilbert.Grz) ⊢! □□⋀Γ₁ ➝ □ψ := imp_trans''! (imp_trans''! (distribute_multibox_conj! (n := 2)) $ conjconj_subset! (by simp)) this;
    have : (Hilbert.Grz) ⊢! □⋀Γ₁ ➝ □ψ := imp_trans''! axiomFour! this;
    have : (Hilbert.Grz) ⊢! ⋀□'Γ₁ ➝ □ψ := imp_trans''! collect_box_conj! this;
    have : (Hilbert.Grz) ⊢! ⋀□'(X.1.prebox.box |>.toList) ➝ □ψ := imp_trans''! (conjconj_subset! (by
      simp;
      intro χ hr;
      have := hΓ₁ _ hr;
      simp at this;
      tauto;
    )) this;
    have : (Hilbert.Grz) ⊢! ⋀□'(X.1.prebox.toList) ➝ □ψ := imp_trans''! (conjconj_provable! (by
      intro ψ hq;
      simp at hq;
      obtain ⟨χ, hr, rfl⟩ := hq;
      apply axiomFour'!;
      apply FiniteContext.by_axm!;
      simpa;
    )) this;
    have : X *⊢[(Hilbert.Grz)]! □ψ := by
      apply Context.provable_iff.mpr;
      use □'X.1.prebox.toList;
      constructor;
      . simp;
      . assumption;
    have : □ψ ∈ X := membership_iff (by trivial) |>.mpr this;
    contradiction;

-- TODO: syntactical proof
lemma truthlemma_lemma3 : (Hilbert.Grz) ⊢! (φ ⋏ □(φ ➝ □φ)) ➝ □φ := by
  apply KT_weakerThan_Grz.pbl;
  by_contra hC;
  have := (not_imp_not.mpr $ Hilbert.KT.Kripke.complete |>.complete) hC;
  simp at this;
  obtain ⟨F, F_refl, hF⟩ := ValidOnFrameClass.exists_frame_of_not this;
  simp [ValidOnFrame, ValidOnModel, Satisfies, Semantics.Realize] at hF;
  obtain ⟨V, x, h₁, h₂, ⟨y, Rxy, h₃⟩⟩ := hF;
  have := h₂ x (F_refl x);
  have := (this h₁) _ Rxy;
  contradiction;

lemma truthlemma {X : (miniCanonicalModel φ).World} (q_sub : ψ ∈ φ.subformulas) :
  Satisfies (miniCanonicalModel φ) X ψ ↔ ψ ∈ X := by
  induction ψ using Formula.rec' generalizing X with
  | hatom => simp [Satisfies];
  | hfalsum => simp [Satisfies];
  | himp ψ χ ihq ihr =>
    have := subformulas.mem_imp₁ q_sub;
    have := subformulas.mem_imp₂ q_sub;
    constructor;
    . contrapose;
      intro h;
      apply Satisfies.not_imp.mpr;
      apply Satisfies.and_def.mpr;
      constructor;
      . apply ihq (subformulas.mem_imp₁ q_sub) |>.mpr;
        exact iff_not_mem_imp
          (hsub_qr := subformulasGrz.mem_origin q_sub)
          (hsub_q := subformulasGrz.mem_left (by assumption))
          (hsub_r := subformulasGrz.mem_left (by assumption))
          |>.mp h |>.1;
      . apply ihr (subformulas.mem_imp₂ q_sub) |>.not.mpr;
        have := iff_not_mem_imp
          (hsub_qr := subformulasGrz.mem_origin q_sub)
          (hsub_q := subformulasGrz.mem_left (by assumption))
          (hsub_r := subformulasGrz.mem_left (by assumption))
          |>.mp h |>.2;
        exact iff_mem_compl (subformulasGrz.mem_left (by assumption)) |>.not.mpr (by simpa using this);
    . contrapose;
      intro h;
      replace h := Satisfies.and_def.mp $ Satisfies.not_imp.mp h;
      obtain ⟨hq, hr⟩ := h;
      replace hq := ihq (by assumption) |>.mp hq;
      replace hr := ihr (by assumption) |>.not.mp hr;
      apply iff_not_mem_imp
        (hsub_qr := subformulasGrz.mem_origin q_sub)
        (hsub_q := subformulasGrz.mem_left (by assumption))
        (hsub_r := subformulasGrz.mem_left (by assumption))
        |>.mpr;
      constructor;
      . assumption;
      . simpa using iff_mem_compl (subformulasGrz.mem_left (by assumption)) |>.not.mp (by assumption);
  | hbox ψ ih =>
    have := subformulas.mem_box q_sub;
    constructor;
    . contrapose;
      by_cases w : ψ ∈ X;
      . intro h;
        obtain ⟨Y, hY⟩ := lindenbaum (𝓢 := Hilbert.Grz) (Ψ := φ.subformulasGrz) (truthlemma_lemma1 q_sub) (truthlemma_lemma2 q_sub h);
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
              have : ↑X *⊢[Hilbert.Grz]! ψ := membership_iff (subformulasGrz.mem_left (by assumption)) |>.mp w;
              have : ↑X *⊢[(Hilbert.Grz)]! □(ψ ➝ □ψ) := membership_iff (by simp; right; assumption) |>.mp hC;
              have : ↑X *⊢[(Hilbert.Grz)]! (ψ ⋏ □(ψ ➝ □ψ)) ➝ □ψ := Context.of! $ truthlemma_lemma3;
              have : ↑X *⊢[(Hilbert.Grz)]! □ψ := this ⨀ and₃'! (by assumption) (by assumption);
              have : □ψ ∈ X := membership_iff (subformulasGrz.mem_origin (by assumption)) |>.mpr this;
              contradiction;
        . apply ih (by aesop) |>.not.mpr;
          apply iff_mem_compl (subformulasGrz.mem_origin (by aesop)) |>.not.mpr;
          push_neg;
          apply hY.2;
          simp;
      . intro _;
        simp only [Satisfies]; push_neg;
        use X;
        constructor;
        . exact miniCanonicalFrame.reflexive X;
        . exact ih (by aesop) |>.not.mpr w;
    . intro h Y RXY;
      apply ih (subformulas.mem_box q_sub) |>.mpr;
      have : ↑Y *⊢[(Hilbert.Grz)]! □ψ ➝ ψ := Context.of! $ axiomT!;
      have : ↑Y *⊢[(Hilbert.Grz)]! ψ := this ⨀
        (membership_iff (by apply subformulasGrz.mem_left; assumption) |>.mp (RXY.1 ψ (by apply subformulasGrz.mem_left; tauto) h));
      exact membership_iff (by apply subformulasGrz.mem_left; exact subformulas.mem_box q_sub) |>.mpr this;

instance complete : Complete (Hilbert.Grz) (Kripke.ReflexiveTransitiveAntiSymmetricFiniteFrameClass) := ⟨by
  intro φ;
  contrapose;
  intro h;
  apply ValidOnFiniteFrameClass.not_of_exists_frame;
  use (miniCanonicalFrame φ);
  constructor;
  . refine ⟨miniCanonicalFrame.reflexive, miniCanonicalFrame.transitive, miniCanonicalFrame.antisymm⟩;
  . apply ValidOnFiniteFrame.not_of_exists_valuation_world;
    obtain ⟨X, hX₁⟩ := lindenbaum (𝓢 := Hilbert.Grz) (Φ := {-φ}) (Ψ := φ.subformulasGrz)
      (by
        simp only [Finset.singleton_subset_iff];
        apply FormulaFinset.complementary_comp;
        exact subformulasGrz.mem_self
      )
      (FormulaFinset.unprovable_iff_singleton_compl_consistent.mpr h);
    use (miniCanonicalModel φ).Val, X;
    apply truthlemma (by simp) |>.not.mpr;
    exact iff_mem_compl (by simp) |>.not.mpr $ by
      push_neg;
      apply hX₁;
      tauto;
⟩

end Hilbert.Grz.Kripke

end LO.Modal
