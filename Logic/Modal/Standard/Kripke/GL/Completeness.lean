import Logic.Modal.Standard.Kripke.GL.Definability
import Logic.Modal.Standard.Kripke.Filteration
import Logic.Modal.Standard.Kripke.Preservation

namespace LO.Modal.Standard

namespace Kripke

open System
open Kripke
open Formula

variable {α : Type u} [Inhabited α]

section Completeness

open Formula (atom)
open Formula.Kripke
open MaximalConsistentTheory

variable [DecidableEq α]

noncomputable abbrev GLCanonicalFrame := CanonicalFrame (α := α) 𝐆𝐋

noncomputable abbrev GLCanonicalModel := CanonicalModel (α := α) 𝐆𝐋

lemma filter_truthlemma
  [Inhabited (Λ)-MCT] [Λ.IsNormal]
  {T : Theory α} [T.SubformulaClosed]
  {X Y : (CanonicalModel Λ).World} (hXY : filterEquiv _ T X Y := by aesop)
  {p : Formula α} (hp : p ∈ T := by aesop) : p ∈ X.theory ↔ p ∈ Y.theory := by
  constructor;
  . intro h; exact truthlemma.mp $ hXY p hp |>.mp $ truthlemma.mpr h;
  . intro h; exact truthlemma.mp $ hXY p hp |>.mpr $ truthlemma.mpr h;

noncomputable abbrev GLFilteredFrame (p : Formula α) : Kripke.FiniteFrame where
  World := FilterEqvQuotient GLCanonicalModel ((𝒮 p).toSet)
  World_finite := by apply FilterEqvQuotient.finite; simp;
  Rel := Quotient.lift₂
    (λ X Y =>
      (∀ q ∈ □''⁻¹(𝒮 p), □q ∈ X.theory → q ⋏ □q ∈ Y.theory) ∧
      (∃ r ∈ □''⁻¹(𝒮 p), □r ∉ X.theory ∧ □r ∈ Y.theory)
    )
    (by
      intro X₁ Y₁ X₂ Y₂ hX hY; simp;
      constructor;
      . rintro ⟨h₁, ⟨r, br_mem_sub, br_nmem_X₁, br_mem_Y₁⟩⟩;
        constructor;
        . intro q bq_mem_sub bq_mem_X₂;
          have bq_mem_X₁ : □q ∈ X₁.theory := filter_truthlemma (by simpa) |>.mpr bq_mem_X₂;
          have ⟨q_mem_Y₁, bq_mem_Y₁⟩ := h₁ q bq_mem_sub bq_mem_X₁;
          constructor;
          . exact filter_truthlemma (by simpa) |>.mp q_mem_Y₁;
          . exact filter_truthlemma (by simpa) |>.mp bq_mem_Y₁;
        . use r;
          refine ⟨br_mem_sub, ?br_nmem_X₂, ?br_mem_Y₂⟩;
          . exact filter_truthlemma (by simpa) |>.not.mp br_nmem_X₁;
          . exact filter_truthlemma (by simpa) |>.mp br_mem_Y₁;
      . rintro ⟨h₁, ⟨r, br_mem_sub, br_nmem_X₂, br_mem_Y₂⟩⟩;
        constructor;
        . intro q bq_mem_sub bq_mem_X₂;
          have bq_mem_X₂ : □q ∈ X₂.theory := filter_truthlemma (by simpa) |>.mp bq_mem_X₂;
          have ⟨q_mem_Y₂, bq_mem_Y₂⟩ := h₁ q bq_mem_sub bq_mem_X₂;
          constructor;
          . exact filter_truthlemma (by simpa) |>.mpr q_mem_Y₂;
          . exact filter_truthlemma (by simpa) |>.mpr bq_mem_Y₂;
        . use r;
          refine ⟨br_mem_sub, ?m, ?me⟩;
          . exact filter_truthlemma (by simpa) |>.not.mpr br_nmem_X₂;
          . exact filter_truthlemma (by simpa) |>.mpr br_mem_Y₂;
    )

lemma GLFilteredFrame.def_rel {p : Formula α} {X Y : GLCanonicalFrame.World} :
  ((GLFilteredFrame p).Rel ⟦X⟧ ⟦Y⟧) ↔
  (∀ q ∈ □''⁻¹(𝒮 p), □q ∈ X.theory → q ⋏ □q ∈ Y.theory) ∧
  (∃ r ∈ □''⁻¹(𝒮 p), □r ∉ X.theory ∧ □r ∈ Y.theory) := by
  simp;

noncomputable abbrev GLFilteredModel (p : Formula α) : Kripke.Model α where
  Frame := GLFilteredFrame p
  Valuation := StandardFilterationValuation GLCanonicalModel ((𝒮 p).toSet)

variable {T : Theory α} [T.SubformulaClosed]
variable {p : Formula α}

lemma irreflexive_GLFilteredFrame : Irreflexive (GLFilteredFrame p).Rel := by
  intro QX;
  obtain ⟨X, hX⟩ := Quotient.exists_rep QX; subst hX;
  simp_all;

lemma transitive_GLFilteredFrame : Transitive (GLFilteredFrame p).Rel := by
  intro QX QY QZ hXY hYZ;
  obtain ⟨X, hX⟩ := Quotient.exists_rep QX; subst hX;
  obtain ⟨Y, hY⟩ := Quotient.exists_rep QY; subst hY;
  obtain ⟨Z, hZ⟩ := Quotient.exists_rep QZ; subst hZ;
  have ⟨hXY₁, hXY₂⟩ := hXY;
  have ⟨hYZ₁, _⟩ := hYZ;
  constructor;
  . intro q hq bq_mem_X;
    have ⟨_, bq_mem_Y⟩ := MaximalConsistentTheory.iff_mem_and.mp $ hXY₁ q hq bq_mem_X;
    exact hYZ₁ q hq bq_mem_Y;
  . obtain ⟨r, hr, br_nmem_X, br_mem_Y⟩ := hXY₂;
    use r;
    constructor;
    . assumption;
    . constructor;
      . assumption;
      . have ⟨_, bq_mem_Y⟩ := MaximalConsistentTheory.iff_mem_and.mp $ hYZ₁ r hr br_mem_Y;
        assumption;

open System System.FiniteContext in
private lemma GL_truthlemma.lemma1
  {q : Formula α}
  {X : (CanonicalModel 𝐆𝐋).World} (h : □q ∉ X.theory) : (𝐆𝐋)-Consistent ({□q, ~q} ∪ (□''⁻¹X.theory ∪ □''□''⁻¹X.theory)) := by
  by_contra hC;
  obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp hC;
  have := toₛ! hΓ₂;
  have : 𝐆𝐋 ⊢! ⋀(Γ.remove (~q)) ⋏ ~q ⟶ ⊥ := imply_left_remove_conj! (p := ~q) this;
  have : 𝐆𝐋 ⊢! ⋀(Γ.remove (~q)) ⟶ ~q ⟶ ⊥ := and_imply_iff_imply_imply'!.mp this;
  have : 𝐆𝐋 ⊢! ⋀(Γ.remove (~q)) ⟶ q := imp_trans''! this $ imp_trans''! (and₂'! neg_equiv!) dne!
  have : 𝐆𝐋 ⊢! ⋀((Γ.remove (~q)).remove (□q)) ⋏ □q ⟶ q := imply_left_remove_conj! (p := □q) this;
  have : 𝐆𝐋 ⊢! ⋀((Γ.remove (~q)).remove (□q)) ⟶ (□q ⟶ q) := and_imply_iff_imply_imply'!.mp this;
  have : 𝐆𝐋 ⊢! □(⋀(Γ.remove (~q)).remove (□q)) ⟶ □(□q ⟶ q) := imply_box_distribute'! this;
  have : 𝐆𝐋 ⊢! □(⋀(Γ.remove (~q)).remove (□q)) ⟶ □q := imp_trans''! this axiomL!;
  have : 𝐆𝐋 ⊢! ⋀□'(Γ.remove (~q)).remove (□q) ⟶ □q := imp_trans''! collect_box_conj! this;
  have : (□'(Γ.remove (~q)).remove (□q)) ⊢[𝐆𝐋]! □q := provable_iff.mpr this;
  have : X.theory *⊢[𝐆𝐋]! □q := by
    apply Context.provable_iff.mpr;
    use (□'List.remove (□q) (List.remove (~q) Γ));
    constructor;
    . intro r hr; simp at hr;
      obtain ⟨s, hs, es⟩ := hr; subst es;
      have ⟨s_mem', hs₁⟩ := List.mem_remove_iff.mp hs;
      have ⟨s_mem, hs₂⟩ := List.mem_remove_iff.mp s_mem';
      clear hs s_mem';
      have := hΓ₁ s s_mem;
      simp at this;
      rcases this with ((ns₁ | hs₂) | bs_mem | b);
      . contradiction;
      . contradiction;
      . assumption;
      . obtain ⟨t, ht, et⟩ := b; subst et;
        apply membership_iff.mpr;
        apply axiomFour'!;
        apply membership_iff.mp;
        assumption;
    . assumption;
  have : □q ∈ X.theory := membership_iff.mpr this;
  contradiction;

open Formula MaximalConsistentTheory in
lemma GL_truthlemma
  {p : Formula α} {X : (CanonicalModel 𝐆𝐋).World} {q : Formula α} (hq : q ∈ 𝒮 p) :
  Satisfies (GLFilteredModel p) ⟦X⟧ q ↔ q ∈ X.theory := by
  induction q using Formula.rec' generalizing X with
  | hbox q ih =>
    constructor;
    . contrapose;
      intro h;
      obtain ⟨Y, hY⟩ := lindenbaum (Λ := 𝐆𝐋) (T := {□q, ~q} ∪ (□''⁻¹X.theory ∪ □''□''⁻¹X.theory)) $ GL_truthlemma.lemma1 h;
      simp [Satisfies];
      use ⟦Y⟧;
      constructor;
      . apply GLFilteredFrame.def_rel.mpr;
        simp at hY;
        have ⟨hY₁, ⟨hY₂, hY₃⟩⟩ := hY;
        simp_all;
        constructor;
        . intro q _ bq_mem_X;
          constructor;
          . apply hY₂; simpa;
          . apply hY₃; simpa;
        . use q;
          simp_all;
          tauto;
      . apply ih (by aesop) |>.not.mpr;
        apply iff_mem_neg.mp;
        apply hY;
        simp;
    . intro bq_mem_X QY RXY;
      obtain ⟨Y, hY⟩ := Quotient.exists_rep QY; subst hY;
      have ⟨h₁, _⟩ := GLFilteredFrame.def_rel.mp RXY; simp at h₁;
      have ⟨q_mem_Y, _⟩ := h₁ q hq bq_mem_X;
      exact ih (by aesop) |>.mpr q_mem_Y;
  | _ =>
    simp_all [Satisfies, StandardFilterationValuation];
    try aesop;

lemma exists_finite_frame : ¬𝔽ꟳ# ⊧ p ↔ ∃ F ∈ 𝔽.toFiniteFrameClass, ¬F# ⊧ p := by
  constructor;
  . simp;
  . rintro ⟨F, hF₁, hF₂⟩;
    simp; use F;
    constructor;
    . simp_all;
    . assumption;

private lemma GL_completeAux {p : Formula α} : TransitiveIrreflexiveFrameClass.{u}ꟳ# ⊧ p → 𝐆𝐋 ⊢! p := by
  contrapose;
  intro h;
  apply exists_finite_frame.mpr;
  use (GLFilteredFrame p);
  constructor;
  . exact ⟨transitive_GLFilteredFrame, irreflexive_GLFilteredFrame⟩;
  . simp [Formula.Kripke.ValidOnFrame, Formula.Kripke.ValidOnModel];
    obtain ⟨X, hX⟩ := lindenbaum (Λ := 𝐆𝐋) (T := {~p}) (Theory.unprovable_iff_singleton_neg_consistent.mp h);
    use (GLFilteredModel p).Valuation, ⟦X⟧;
    apply GL_truthlemma (by simp) |>.not.mpr;
    apply MaximalConsistentTheory.iff_mem_neg.mp;
    simpa using hX;

instance GL_complete : Complete (𝐆𝐋 : DeductionParameter α) TransitiveIrreflexiveFrameClass.{u}ꟳ# := ⟨GL_completeAux⟩

instance : FiniteFrameProperty (α := α) 𝐆𝐋 TransitiveIrreflexiveFrameClass where

end Completeness

end Kripke

end LO.Modal.Standard
