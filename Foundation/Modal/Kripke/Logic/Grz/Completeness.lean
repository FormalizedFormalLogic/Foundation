import Foundation.Modal.Kripke.Logic.Grz.Soundness
import Foundation.Modal.Kripke.Logic.KT
import Foundation.Modal.Entailment.K4
import Foundation.Modal.ComplementClosedConsistentFinset
import Foundation.Modal.Kripke.Hilbert
import Foundation.Modal.Kripke.Logic.S4

namespace LO.Modal

namespace Formula

variable {α : Type u} [DecidableEq α]
variable {φ ψ χ : Formula ℕ}

noncomputable abbrev subformulasGrz (φ : Formula α) := φ.subformulas ∪ (φ.subformulas.prebox.image (λ ψ => □(ψ ➝ □ψ)))

namespace subformulasGrz

@[simp] lemma mem_self : φ ∈ φ.subformulasGrz := by simp [subformulasGrz, subformulas.mem_self]

lemma mem_boximpbox (h : ψ ∈ φ.subformulas.prebox) : □(ψ ➝ □ψ) ∈ φ.subformulasGrz := by simp_all [subformulasGrz];

protected lemma mem_of_mem_subformula (h : ψ ∈ φ.subformulas) : ψ ∈ φ.subformulasGrz := by simp_all [subformulasGrz];
add_subformula_rules safe 10 tactic [
  (by exact subformulasGrz.mem_of_mem_subformula (by subformula)),
]

@[subformula]
protected lemma mem_imp (h : (ψ ➝ χ) ∈ φ.subformulasGrz) : ψ ∈ φ.subformulasGrz ∧ χ ∈ φ.subformulasGrz := by subformula;

end subformulasGrz

end Formula


open Formula Formula.Kripke
open LO.Entailment LO.Entailment.FiniteContext LO.Modal.Entailment
open ComplementClosedConsistentFinset
open Kripke

namespace Kripke.Grz

variable {S} [Entailment (Formula ℕ) S]
variable {𝓢 : S} [Entailment.Consistent 𝓢] [Entailment.Grz 𝓢]

variable {φ ψ : Formula ℕ}

abbrev miniCanonicalFrame (𝓢 : S) [Entailment.Grz 𝓢] [Entailment.Consistent 𝓢] (φ : Formula ℕ) : Kripke.Frame where
  World := ComplementClosedConsistentFinset 𝓢 (φ.subformulasGrz)
  Rel X Y :=
    (∀ ψ ∈ (φ.subformulasGrz).prebox, □ψ ∈ X → □ψ ∈ Y) ∧
    ((∀ ψ ∈ (φ.subformulasGrz).prebox, □ψ ∈ Y → □ψ ∈ X) → X = Y)

namespace miniCanonicalFrame

instance : (miniCanonicalFrame 𝓢 φ).IsFinite := inferInstance

instance : IsRefl _ (miniCanonicalFrame 𝓢 φ).Rel := ⟨by tauto_set⟩

instance : IsTrans _ (miniCanonicalFrame 𝓢 φ).Rel := ⟨by
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
⟩

instance : IsAntisymm _ (miniCanonicalFrame 𝓢 φ).Rel := ⟨by
  rintro X Y ⟨_, h₁⟩ ⟨h₂, _⟩;
  exact h₁ h₂;
⟩

instance : IsPartialOrder _ (miniCanonicalFrame 𝓢 φ).Rel where

end miniCanonicalFrame


abbrev miniCanonicalModel (𝓢 : S) [Entailment.Grz 𝓢] [Entailment.Consistent 𝓢] (φ : Formula ℕ) : Kripke.Model where
  toFrame := miniCanonicalFrame 𝓢 φ
  Val X a := (atom a) ∈ X

omit [Consistent 𝓢] [Entailment.Grz 𝓢] in
lemma truthlemma_lemma1
  {X : ComplementClosedConsistentFinset 𝓢 (φ.subformulasGrz)} (hq : □ψ ∈ φ.subformulas)
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
    exact FormulaFinset.complementary_mem_box (by subformula) this;
  . right;
    simp;
    use ψ;
    constructor;
    . left;
      exact subformulas.mem_box hq;
    . rfl;

omit [Consistent 𝓢] in
lemma truthlemma_lemma2
  {X : ComplementClosedConsistentFinset 𝓢 (φ.subformulasGrz)}
  (hψ₁ : □ψ ∈ φ.subformulas)
  (hψ₂ : □ψ ∉ X)
  : FormulaFinset.Consistent 𝓢 ((X.1.prebox.box) ∪ {□(ψ ➝ □ψ), -ψ}) := by
    apply FormulaFinset.intro_union_consistent;
    rintro Γ₁ Γ₂ hΓ₁ hΓ₂;
    by_contra! hC;
    apply hψ₂;
    have := Context.weakening! (Γ := Γ₁ ∪ Γ₂) (Δ := insert (-ψ) (insert (□(ψ ➝ □ψ)) Γ₁)) ?_ hC;
    . replace := Context.deduct! this;
      replace := of_imply_complement_bot this;
      replace := Context.deduct! this;
      replace := Context.nec! this;
      replace := axiomGrz! ⨀ this;
      replace := Context.nec! this;
      replace := Context.boxbox_in_context_to_box this;
      replace : X.1.toSet.prebox.box.box *⊢[𝓢]! □ψ := Context.weakening! ?_ this;
      . replace := Context.boxbox_in_context_to_box this;
        replace : X *⊢[𝓢]! □ψ := Context.weakening! ?_ this;
        . exact membership_iff (subformulasGrz.mem_of_mem_subformula hψ₁) |>.mpr this;
        . intro ξ hξ;
          simp at hξ;
          obtain ⟨ξ, hξ, rfl⟩ := hξ;
          tauto;
      . intro ξ hξ;
        simp at hξ;
        obtain ⟨ξ, hξ, rfl⟩ := hξ;
        have := hΓ₁ hξ;
        simp at this ⊢;
        obtain ⟨χ, hχ, rfl⟩ := this;
        use χ;
    . intro ξ;
      simp only [Set.mem_union, Finset.mem_coe, Set.mem_insert_iff];
      rintro (hξ₁ | hξ₂);
      . have := hΓ₁ hξ₁; tauto;
      . have := hΓ₂ hξ₂;
        simp at this;
        tauto;

omit [Consistent 𝓢] in
lemma truthlemma_lemma3 : 𝓢 ⊢! (φ ⋏ □(φ ➝ □φ)) ➝ □φ := by
  refine C!_trans ?_ $ inner_mdp! (𝓢 := 𝓢) (φ := φ) (ψ := □φ);
  apply CKK!_of_C!';
  exact axiomT!;

lemma truthlemma {X : (miniCanonicalModel 𝓢 φ).World} (q_sub : ψ ∈ φ.subformulas) :
  Satisfies (miniCanonicalModel 𝓢 φ) X ψ ↔ ψ ∈ X := by
  induction ψ generalizing X with
  | hatom => simp [Satisfies];
  | hfalsum => simp [Satisfies];
  | himp ψ χ ihq ihr =>
    have : ψ ∈ φ.subformulas := subformulas.mem_imp q_sub |>.1;
    have : χ ∈ φ.subformulas := subformulas.mem_imp q_sub |>.2;
    constructor;
    . contrapose;
      intro h;
      apply Satisfies.not_imp.mpr;
      apply Satisfies.and_def.mpr;
      constructor;
      . apply ihq (by subformula) |>.mpr;
        exact iff_not_mem_imp (ψ := ψ) (χ := χ) |>.mp h |>.1;
      . apply ihr (by subformula) |>.not.mpr;
        exact iff_mem_compl (by subformula) |>.not.mpr $ by
          push_neg;
          exact iff_not_mem_imp (ψ := ψ) (χ := χ) |>.mp h |>.2;
    . contrapose;
      intro h;
      replace h := Satisfies.and_def.mp $ Satisfies.not_imp.mp h;
      obtain ⟨hq, hr⟩ := h;
      replace hq := ihq (by subformula) |>.mp hq;
      replace hr := ihr (by subformula) |>.not.mp hr;
      apply iff_not_mem_imp (ψ := ψ) (χ := χ) |>.mpr;
      constructor;
      . assumption;
      . simpa using iff_mem_compl (by subformula) |>.not.mp hr;
  | hbox ψ ih =>
    have := subformulas.mem_box q_sub;
    constructor;
    . contrapose;
      by_cases w : ψ ∈ X;
      . intro h;
        obtain ⟨Y, hY⟩ := lindenbaum (𝓢 := 𝓢) (truthlemma_lemma1 q_sub) (truthlemma_lemma2 q_sub h);
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
            . apply hY.2;
              simp;
            . by_contra hC;
              have : ↑X *⊢[𝓢]! ψ := membership_iff (by subformula) |>.mp w;
              have : ↑X *⊢[𝓢]! □(ψ ➝ □ψ) := membership_iff (by simp; right; assumption) |>.mp hC;
              have : ↑X *⊢[𝓢]! (ψ ⋏ □(ψ ➝ □ψ)) ➝ □ψ := Context.of! $ truthlemma_lemma3;
              have : ↑X *⊢[𝓢]! □ψ := this ⨀ K!_intro (by assumption) (by assumption);
              have : □ψ ∈ X := membership_iff (by subformula) |>.mpr this;
              contradiction;
        . apply ih (by subformula) |>.not.mpr;
          apply iff_mem_compl (by subformula) |>.not.mpr;
          push_neg;
          apply hY.2;
          simp;
      . intro _;
        simp only [Satisfies]; push_neg;
        use X;
        constructor;
        . exact IsRefl.refl X;
        . exact ih (by subformula) |>.not.mpr w;
    . intro h Y RXY;
      apply ih (subformulas.mem_box q_sub) |>.mpr;
      have : ↑Y *⊢[𝓢]! □ψ ➝ ψ := Context.of! $ axiomT!;
      have : ↑Y *⊢[𝓢]! ψ := this ⨀ (membership_iff (by subformula) |>.mp (RXY.1 ψ (by subformula) h));
      exact membership_iff (by subformula) |>.mpr this;

lemma complete_of_mem_miniCanonicalFrame
  (C : Kripke.FrameClass)
  (hC : ∀ {φ}, miniCanonicalFrame 𝓢 φ ∈ C)
  : Complete 𝓢 C := ⟨by
  intro φ;
  contrapose;
  intro h;
  apply Semantics.set_models_iff.not.mpr;
  push_neg;
  use (miniCanonicalFrame 𝓢 φ);
  constructor;
  . apply hC;
  . apply ValidOnFrame.not_of_exists_valuation_world;
    obtain ⟨X, hX₁⟩ := lindenbaum (𝓢 := 𝓢) (Φ := {-φ}) (Ψ := φ.subformulasGrz)
      (by
        simp only [Finset.singleton_subset_iff];
        apply FormulaFinset.complementary_comp;
        subformula;
      )
      (FormulaFinset.unprovable_iff_singleton_compl_consistent.mpr h);
    use (miniCanonicalModel _ φ).Val, X;
    apply truthlemma (by subformula) |>.not.mpr;
    exact iff_mem_compl (by subformula) |>.not.mpr $ by
      push_neg;
      apply hX₁;
      tauto;
⟩

end Kripke.Grz


namespace Hilbert.Grz.Kripke

open Kripke.Grz

instance complete : Complete (Hilbert.Grz) FrameClass.finite_partial_order :=
  complete_of_mem_miniCanonicalFrame FrameClass.finite_partial_order $ by
    refine ⟨inferInstance, inferInstance⟩;

end Hilbert.Grz.Kripke


namespace Logic

open Formula
open Entailment
open Kripke

lemma Grz.Kripke.finite_partial_order : Logic.Grz = FrameClass.finite_partial_order.logic := eq_hilbert_logic_frameClass_logic

theorem Grz.proper_extension_of_S4 : Logic.S4 ⊂ Logic.Grz := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.Grz ⊢! φ ∧ ¬Kripke.FrameClass.preorder ⊧ φ by
      rw [S4.Kripke.preorder];
      tauto;
    use Axioms.Grz (.atom 0)
    constructor;
    . exact axiomGrz!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 2, λ x y => True⟩, λ w _ => w = 1⟩, 0;
      constructor;
      . refine {refl := by tauto, trans := by tauto};
      . simp [Reflexive, Transitive, Semantics.Realize, Satisfies];


end Logic

end LO.Modal
