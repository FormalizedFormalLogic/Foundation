import Logic.Modal.Standard.Kripke.Grz
import Logic.Modal.Standard.Kripke.GL.Completeness

namespace LO.Modal.Standard

namespace Formula

variable [DecidableEq α]

abbrev GrzSubformulas (p : Formula α) := (𝒮 p) ∪ ((𝒮 p).image (λ q => □(q ⟶ □q)))
prefix:70 "𝒮ᴳ " => Formula.GrzSubformulas

end Formula

namespace Kripke

open System
open Kripke
open Formula (atom)
open Formula.Kripke

variable {α : Type u} [Inhabited α] [DecidableEq α]
variable {F : Kripke.Frame}


abbrev GrzCanonicalFrame := CanonicalFrame (α := α) 𝐆𝐫𝐳
abbrev GrzCanonicalModel := CanonicalModel (α := α) 𝐆𝐫𝐳

-- TODO: Too slow
set_option maxHeartbeats 1000000 in
abbrev GrzFilteredFrame (p : Formula α) : Kripke.FiniteFrame where
  World := FilterEqvQuotient GrzCanonicalModel ((𝒮 p).toSet)
  World_finite := by apply FilterEqvQuotient.finite; simp;
  Rel := Quotient.lift₂
    (λ X Y =>
      (∀ q ∈ □''⁻¹(𝒮ᴳ p), □q ∈ X.theory → □q ∈ Y.theory) ∧
      ((∀ q ∈ □''⁻¹(𝒮ᴳ p), □q ∈ Y.theory → □q ∈ X.theory) → X = Y)
    )
    (by
      intro X₁ Y₁ X₂ Y₂ hX hY;
      simp only [Formula.GrzSubformulas, Finset.coe_union, Finset.coe_image, Set.preimage_union,
        Function.iterate_one, Set.mem_union, Set.mem_preimage, Finset.mem_coe, Set.mem_image,
        Box.box_injective', eq_iff_iff];
      constructor;
      . rintro ⟨h₁, h₂⟩;
        constructor;
        . rintro q (h_sub | ⟨q, h_sub, rfl⟩) hq
          . have : □q ∈ X₁.theory := filter_truthlemma (by simpa only) |>.mpr hq;
            have : □q ∈ Y₁.theory := h₁ q (by left; assumption) this;
            exact filter_truthlemma (by simpa only) |>.mp this;
          . sorry;
            -- have : □(q ⟶ □q) ∈ X₁.theory := filter_truthlemma (by sorry) |>.mpr hq;
          -- have : □q ∈ X₁.theory := filter_truthlemma (by simpa only) |>.mpr hq;
          -- have : □q ∈ Y₁.theory := h₁ q (by assumption) this;
          -- exact filter_truthlemma (by simpa only) |>.mp this;
        . sorry;
          /-
          intro h q _;
          constructor;
          . intro hq;
            have : q ∈ X₁.theory := filter_truthlemma (by simpa only) |>.mpr hq;
            have : q ∈ Y₁.theory := h₂ ?_ q (by assumption) |>.mp this;
            exact filter_truthlemma (by simpa only) |>.mp this;
            intro q _ hq;
            have : □q ∈ Y₂.theory := filter_truthlemma (by simpa only) |>.mp hq;
            have : □q ∈ X₂.theory := h q (by assumption) this;
            exact filter_truthlemma (by simpa only) |>.mpr this;
          . intro hq;
            have : q ∈ Y₁.theory := filter_truthlemma (by simpa only) |>.mpr hq;
            have : q ∈ X₁.theory := h₂ ?_ q (by assumption) |>.mpr this;
            exact filter_truthlemma (by simpa only) |>.mp this;
            intro q _ hq;
            have : □q ∈ Y₂.theory := filter_truthlemma (by simpa only) |>.mp hq;
            have : □q ∈ X₂.theory := h q (by assumption) this;
            exact filter_truthlemma (by simpa only) |>.mpr this;
          -/
      . rintro ⟨h₁, h₂⟩;
        constructor;
        . sorry;
          /-
          intro q _ hq;
          have : □q ∈ X₂.theory := filter_truthlemma (by simpa only) |>.mp hq;
          have : □q ∈ Y₂.theory := h₁ q (by assumption) this;
          exact filter_truthlemma (by simpa only) |>.mpr this;
          -/
        . sorry;
          /-
          intro h q _;
          constructor;
          . intro hq;
            have : q ∈ X₂.theory := filter_truthlemma (by simpa only) |>.mp hq;
            have : q ∈ Y₂.theory := h₂ ?_ q (by assumption) |>.mp this;
            exact filter_truthlemma (by simpa only) |>.mpr this;
            intro q _ hq;
            have : □q ∈ Y₁.theory := filter_truthlemma (by simpa only) |>.mpr hq;
            have : □q ∈ X₁.theory := h q (by assumption) this;
            exact filter_truthlemma (by simpa only) |>.mp this;
          . intro hq;
            have : q ∈ Y₂.theory := filter_truthlemma (by simpa only) |>.mp hq;
            have : q ∈ X₂.theory := h₂ ?_ q (by assumption) |>.mpr this;
            exact filter_truthlemma (by simpa only) |>.mpr this;
            intro q _ hq;
            have : □q ∈ Y₁.theory := filter_truthlemma (by simpa only) |>.mpr hq;
            have : □q ∈ X₁.theory := h q (by assumption) this;
            exact filter_truthlemma (by simpa only) |>.mp this;
          -/
    )

lemma GrzFilteredFrame.def_rel {p : Formula α} {X Y : GrzCanonicalFrame.World} :
  ((GrzFilteredFrame p).Rel ⟦X⟧ ⟦Y⟧) ↔
  (
    (∀ q ∈ □''⁻¹(𝒮ᴳ p), □q ∈ X.theory → □q ∈ Y.theory) ∧
    ((∀ q ∈ □''⁻¹(𝒮ᴳ p), □q ∈ Y.theory → □q ∈ X.theory) → X = Y)
  )
  := by simp;

lemma GrzFilteredFrame.reflexive {p : Formula α} : Reflexive (GrzFilteredFrame p).Rel := by
  intro QX;
  obtain ⟨X, hX⟩ := Quotient.exists_rep QX; subst hX;
  simp_all;

lemma GrzFilteredFrame.transitive {p : Formula α} : Transitive (GrzFilteredFrame p).Rel := by
  intro QX QY QZ RXY RYZ;
  obtain ⟨X, hX⟩ := Quotient.exists_rep QX; subst hX;
  obtain ⟨Y, hY⟩ := Quotient.exists_rep QY; subst hY;
  obtain ⟨Z, hZ⟩ := Quotient.exists_rep QZ; subst hZ;
  replace ⟨hXY₁, hXY₂⟩ := RXY;
  replace ⟨hYZ₁, hYZ₂⟩ := RYZ;
  constructor;
  . intro q hs hq;
    exact hYZ₁ q hs $ hXY₁ q hs hq
  . intro h;
    have eXY := hXY₂ $ by
      intro q hs hq;
      exact h q hs $ hYZ₁ q hs hq;
    have eYZ := hYZ₂ $ by
      intro q hs hq;
      exact hXY₁ q hs $ h q hs hq
    subst_vars;
    tauto;

lemma GrzFilteredFrame.antisymm {p : Formula α} : Antisymmetric (GrzFilteredFrame p).Rel := by
  intro QX QY RXY RYX;
  obtain ⟨X, hX⟩ := Quotient.exists_rep QX; subst hX;
  obtain ⟨Y, hY⟩ := Quotient.exists_rep QY; subst hY;
  have := RXY.2 RYX.1;
  tauto;

abbrev GrzFilteredModel (p : Formula α) : Kripke.Model α where
  Frame := GrzFilteredFrame p
  Valuation := StandardFilterationValuation GrzCanonicalModel ((𝒮 p).toSet)

-- TODO: syntactical proof
private lemma K4_lemma1 {q : Formula α} : 𝐊𝟒 ⊢! (□q ⟶ □(q ⟶ □q)) := by
  by_contra hC;
  have := (not_imp_not.mpr $ K4_complete (α := α) |>.complete) hC;
  simp only [ValidOnFrameClass.models_iff, ValidOnFrameClass, Set.mem_setOf_eq, Transitive,
    ValidOnFrame.models_iff, ValidOnFrame, ValidOnModel.iff_models, ValidOnModel,
    Satisfies.iff_models, Satisfies, not_forall, Classical.not_imp] at this;
  obtain ⟨F, F_trans, V, x, h, y, Rxy, _, z, Ryz, j⟩ := this;
  have := h (F_trans Rxy Ryz);
  contradiction;

-- TODO: syntactical proof
private lemma KT_lemma1 {q : Formula α} : 𝐊𝐓 ⊢! (q ⋏ □(q ⟶ □q)) ⟶ □q := by
  by_contra hC;
  have := (not_imp_not.mpr $ KT_complete (α := α) |>.complete) hC;
  simp at this;
  obtain ⟨F, F_refl, hF⟩ := this;
  simp [ValidOnFrame, ValidOnModel, Satisfies] at hF;
  obtain ⟨V, x, h₁, h₂, ⟨y, Rxy, h₃⟩⟩ := hF;
  have := h₂ (F_refl x);
  have := (this h₁) Rxy;
  contradiction;

open System System.FiniteContext MaximalConsistentTheory in
private lemma Grz_truthlemma.lemma
  {q : Formula α}
  {X : (CanonicalModel 𝐆𝐫𝐳).World} (h : □q ∉ X.theory) : (𝐆𝐫𝐳)-Consistent ({□(q ⟶ □q), ~q} ∪ (□''□''⁻¹X.theory)) := by
  by_contra hC;
  obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp hC;
  have := toₛ! hΓ₂;
  have : 𝐆𝐫𝐳 ⊢! ⋀(Γ.remove (~q)) ⋏ ~q ⟶ ⊥ := imply_left_remove_conj! (p := ~q) this;
  have : 𝐆𝐫𝐳 ⊢! ⋀(Γ.remove (~q)) ⟶ ~q ⟶ ⊥ := and_imply_iff_imply_imply'!.mp this;
  have : 𝐆𝐫𝐳 ⊢! ⋀(Γ.remove (~q)) ⟶ q := imp_trans''! this $ imp_trans''! (and₂'! neg_equiv!) dne!
  have : 𝐆𝐫𝐳 ⊢! ⋀((Γ.remove (~q)).remove (□(q ⟶ □q))) ⋏ (□(q ⟶ □q)) ⟶ q := imply_left_remove_conj! (p := □(q ⟶ □q)) this;
  have : 𝐆𝐫𝐳 ⊢! ⋀((Γ.remove (~q)).remove (□(q ⟶ □q))) ⟶ (□(q ⟶ □q) ⟶ q)  := and_imply_iff_imply_imply'!.mp this;
  have : 𝐆𝐫𝐳 ⊢! □⋀((Γ.remove (~q)).remove (□(q ⟶ □q))) ⟶ □(□(q ⟶ □q) ⟶ q) := imply_box_distribute'! this;
  have : 𝐆𝐫𝐳 ⊢! □⋀((Γ.remove (~q)).remove (□(q ⟶ □q))) ⟶ q := imp_trans''! this axiomGrz!;
  have : 𝐆𝐫𝐳 ⊢! □□⋀((Γ.remove (~q)).remove (□(q ⟶ □q))) ⟶ □q := imply_box_distribute'! this;
  have : 𝐆𝐫𝐳 ⊢! □⋀((Γ.remove (~q)).remove (□(q ⟶ □q))) ⟶ □q := imp_trans''! axiomFour! this;
  have : 𝐆𝐫𝐳 ⊢! ⋀□'((Γ.remove (~q)).remove (□(q ⟶ □q))) ⟶ □q := imp_trans''! collect_box_conj! this;

  have : X.theory *⊢[𝐆𝐫𝐳]! (□q) := by
    apply Context.provable_iff.mpr;
    use (□'List.remove (□(q ⟶ □q)) (List.remove (~q) Γ));
    constructor;
    . intro r hr; simp at hr;
      obtain ⟨s, hs, rfl⟩ := hr;
      have ⟨s_mem', hs₁⟩ := List.mem_remove_iff.mp hs;
      have ⟨s_mem, hs₂⟩ := List.mem_remove_iff.mp s_mem';
      clear hs s_mem';
      have := hΓ₁ s s_mem;
      simp at this;
      rcases this with ((rfl | rfl) | ⟨s, hs, rfl⟩);
      . contradiction;
      . contradiction;
      . apply membership_iff.mpr;
        apply axiomFour'!;
        apply membership_iff.mp;
        assumption;
    . assumption;

  have : □q ∈ X.theory := membership_iff.mpr this;
  contradiction;

open Formula MaximalConsistentTheory

lemma Grz_truthlemma
  {p : Formula α} {X : (CanonicalModel 𝐆𝐫𝐳).World} {q : Formula α} (hq : q ∈ 𝒮 p) :
  Satisfies (GrzFilteredModel p) ⟦X⟧ q ↔ q ∈ X.theory := by
  induction q using Formula.rec' generalizing X with
  | hbox q ih =>
    by_cases bq_mem_X : □q ∈ X.theory;
    . simp [bq_mem_X];
      intro QY RXY;
      obtain ⟨Y, hY⟩ := Quotient.exists_rep QY; subst hY;
      have : □q ∈ Y.theory := GrzFilteredFrame.def_rel.mp RXY |>.1 q (by simp; left; assumption) bq_mem_X;
      have : q ∈ Y.theory := iff_mem_imp (Ω := Y) |>.mp (membership_iff.mpr (axiomT!)) this;
      exact @ih Y (Subformulas.mem_box hq) |>.mpr this;
    . simp [bq_mem_X]
      wlog q_mem_X : q ∈ X.theory;
      . have : ¬Satisfies (GrzFilteredModel p) ⟦X⟧ q := @ih X (Subformulas.mem_box hq) |>.not.mpr q_mem_X;
        have : ¬Satisfies (GrzFilteredModel p) ⟦X⟧ (□q) := by
          simp [Satisfies];
          use ⟦X⟧;
          constructor;
          . apply GrzFilteredFrame.reflexive;
          . assumption;
        tauto;
      simp [Satisfies];
      obtain ⟨Y, hY⟩ := lindenbaum (Λ := 𝐆𝐫𝐳) (T := ({□(q ⟶ □q), ~q} ∪ (□''□''⁻¹X.theory))) $ Grz_truthlemma.lemma bq_mem_X;
      simp [Set.insert_subset_iff] at hY;
      obtain ⟨⟨mem_q₁_Y, nmem_q_Y⟩, hY₂⟩ := hY;
      use ⟦Y⟧;
      constructor;
      . apply GrzFilteredFrame.def_rel.mpr;
        constructor;
        . intro r hr;
          simp [GrzSubformulas] at hr;
          rcases hr with (_ | ⟨r, _, rfl⟩) <;> apply hY₂;
        . apply imp_iff_not_or (a := (∀ q ∈ □''⁻¹↑(𝒮ᴳ p), □q ∈ Y.theory → □q ∈ X.theory)) (b := X = Y) |>.mpr;
          left; push_neg;
          use (q ⟶ □q);
          refine ⟨?_, ?_, ?_⟩;
          . simp; right; exact Subformulas.mem_box hq;
          . assumption;
          . by_contra hC;
            have : 𝐆𝐫𝐳 ⊢! (q ⋏ □(q ⟶ □q)) ⟶ □q := reducible_KT_Grz KT_lemma1;
            have : (q ⋏ □(q ⟶ □q) ⟶ □q) ∈ X.theory := membership_iff.mpr $ Context.of! this;
            have : □q ∈ X.theory := iff_mem_imp.mp this ?_;
            contradiction;
            apply iff_mem_and.mpr;
            constructor;
            . assumption;
            . assumption;
      . apply @ih Y (Subformulas.mem_box hq) |>.not.mpr;
        assumption
  | _ =>
    simp_all [Satisfies, StandardFilterationValuation];
    try aesop;

private lemma Grz_completeAux {p : Formula α} : ReflexiveTransitiveAntisymmetricFrameClass.{u}ꟳ# ⊧ p → 𝐆𝐫𝐳 ⊢! p := by
  contrapose;
  intro h;
  apply exists_finite_frame.mpr;
  use (GrzFilteredFrame p);
  constructor;
  . refine ⟨GrzFilteredFrame.reflexive, GrzFilteredFrame.transitive, GrzFilteredFrame.antisymm⟩;
  . simp [Formula.Kripke.ValidOnFrame, Formula.Kripke.ValidOnModel];
    obtain ⟨X, hX⟩ := lindenbaum (Λ := 𝐆𝐫𝐳) (T := {~p}) (Theory.unprovable_iff_singleton_neg_consistent.mp h);
    use (GrzFilteredModel p).Valuation, ⟦X⟧;
    apply Grz_truthlemma (by simp) |>.not.mpr;
    apply MaximalConsistentTheory.iff_mem_neg.mp;
    simpa using hX;

instance Grz_complete : Complete (𝐆𝐫𝐳 : DeductionParameter α) ReflexiveTransitiveAntisymmetricFrameClass.{u}ꟳ# := ⟨Grz_completeAux⟩

instance : FiniteFrameProperty (α := α) 𝐆𝐫𝐳 ReflexiveTransitiveAntisymmetricFrameClass where


end Kripke

end LO.Modal.Standard
