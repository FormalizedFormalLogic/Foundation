module

public import Foundation.Modal.ComplementClosedConsistentFinset
public import Foundation.Modal.Kripke.Logic.Grz.Soundness

@[expose] public section

namespace LO.Modal

namespace Formula

variable {α : Type u} [DecidableEq α]
variable {φ ψ χ : Formula ℕ}

@[grind] noncomputable abbrev subformulasGrz (φ : Formula α) := φ.subformulas ∪ ((□⁻¹'φ.subformulas).image (λ ψ => □(ψ 🡒 □ψ)))

namespace subformulasGrz

@[simp, grind .] lemma mem_self : φ ∈ φ.subformulasGrz := by simp [subformulasGrz, subformulas.mem_self]

@[grind ⇒] protected lemma mem_of_mem_subformula (h : ψ ∈ φ.subformulas) : ψ ∈ φ.subformulasGrz := by grind;
@[grind ⇒] lemma mem_boximpbox (h : ψ ∈ (□⁻¹'φ.subformulas)) : □(ψ 🡒 □ψ) ∈ φ.subformulasGrz := by grind;

@[grind ⇒]
protected lemma mem_imp (h : (ψ 🡒 χ) ∈ φ.subformulasGrz) : ψ ∈ φ.subformulasGrz ∧ χ ∈ φ.subformulasGrz := by
  simp_all only [
    Finset.mem_union, Finset.mem_image, Finset.mem_preimage, Function.iterate_one,
    reduceCtorEq, and_false, exists_const, or_false
  ];
  grind;

example {_ : φ ∈ φ.subformulasGrz} : φ ∈ φ.subformulasGrz := by grind;
example {_ : ψ 🡒 χ ∈ φ.subformulasGrz} : ψ ∈ φ.subformulasGrz := by grind
example {_ : ψ 🡒 χ ∈ φ.subformulasGrz} : χ ∈ φ.subformulasGrz := by grind

end subformulasGrz

end Formula


open Formula Formula.Kripke
open LO.Entailment LO.Entailment.FiniteContext LO.Modal.Entailment
open ComplementClosedConsistentFinset
open Kripke

namespace Grz.Kripke

variable {S} [Entailment S (Formula ℕ)]
variable {𝓢 : S} [Entailment.Consistent 𝓢] [Entailment.Grz 𝓢]

variable {φ ψ : Formula ℕ}

abbrev miniCanonicalFrame (𝓢 : S) [Entailment.Grz 𝓢] [Entailment.Consistent 𝓢] (φ : Formula ℕ) : Kripke.Frame where
  World := ComplementClosedConsistentFinset 𝓢 (φ.subformulasGrz)
  Rel X Y :=
    (∀ ψ ∈ □⁻¹'(φ.subformulasGrz), □ψ ∈ X → □ψ ∈ Y) ∧
    ((∀ ψ ∈ □⁻¹'(φ.subformulasGrz), □ψ ∈ Y → □ψ ∈ X) → X = Y)

instance : (miniCanonicalFrame 𝓢 φ).IsReflexive where
  refl := by tauto_set;

instance : (miniCanonicalFrame 𝓢 φ).IsAntisymmetric where
  antisymm := by
    rintro X Y ⟨_, h₁⟩ ⟨h₂, _⟩;
    exact h₁ h₂;

instance : (miniCanonicalFrame 𝓢 φ).IsTransitive where
  trans := by
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

instance : (miniCanonicalFrame 𝓢 φ).IsFiniteGrz where


abbrev miniCanonicalModel (𝓢 : S) [Entailment.Grz 𝓢] [Entailment.Consistent 𝓢] (φ : Formula ℕ) : Kripke.Model where
  toFrame := miniCanonicalFrame 𝓢 φ
  Val a X := (atom a) ∈ X

omit [Consistent 𝓢] [Entailment.Grz 𝓢] in
lemma truthlemma_lemma1
  {X : ComplementClosedConsistentFinset 𝓢 (φ.subformulasGrz)} (hq : □ψ ∈ φ.subformulas)
  : ((□'□⁻¹'X.1) ∪ {□(ψ 🡒 □ψ), -ψ}) ⊆ (φ.subformulasGrz)⁻ := by
  simp only [FormulaFinset.complementary];
  intro χ hr;
  apply Finset.mem_union.mpr;
  replace hr : χ = □(ψ 🡒 □ψ) ∨ χ = -ψ ∨ (∃ a, □a ∈ X ∧ □a = χ)  := by
    simpa [Finset.mem_union, Finset.LO.preboxItr, Finset.LO.boxItr] using hr;
  rcases hr with (rfl | rfl | ⟨χ, hr, rfl⟩);
  . left;
    simp [Finset.LO.preboxItr];
    tauto;
  . right;
    simp only [Finset.mem_image, Finset.mem_union, Finset.mem_preimage, Function.iterate_one];
    use ψ;
    grind;
  . have := X.closed.subset hr;
    left;
    exact FormulaFinset.complementary_mem_box (by grind) this;

set_option linter.style.multiGoal false in
omit [Consistent 𝓢] in
lemma truthlemma_lemma2
  {X : ComplementClosedConsistentFinset 𝓢 (φ.subformulasGrz)}
  (hψ₁ : □ψ ∈ φ.subformulas)
  (hψ₂ : □ψ ∉ X)
  : FormulaFinset.Consistent 𝓢 ((□'□⁻¹'X.1) ∪ {□(ψ 🡒 □ψ), -ψ}) := by
    apply FormulaFinset.intro_union_consistent;
    rintro Γ₁ Γ₂ hΓ₁ hΓ₂;
    by_contra! hC;
    apply hψ₂;
    have    : insert (-ψ) (insert (□(ψ 🡒 □ψ)) ↑Γ₁) *⊢[𝓢] ⊥ := Context.weakening! ?h₁ hC;
    replace : (insert (□(ψ 🡒 □ψ)) ↑Γ₁) *⊢[𝓢] -ψ 🡒 ⊥ := Context.deduct! this;
    replace : (insert (□(ψ 🡒 □ψ)) ↑Γ₁) *⊢[𝓢] ψ := of_imply_complement_bot this;
    replace : ↑Γ₁ *⊢[𝓢] □(ψ 🡒 □ψ) 🡒 ψ := Context.deduct! this;
    replace : (□'↑Γ₁) *⊢[𝓢] □(□(ψ 🡒 □ψ) 🡒 ψ) := Context.nec! this;
    replace : (□'↑Γ₁) *⊢[𝓢] ψ := axiomGrz! ⨀ this;
    replace : (□'□'↑Γ₁) *⊢[𝓢] □ψ := Context.nec! this;
    replace : (□'↑Γ₁) *⊢[𝓢] □ψ := Context.boxbox_in_context_to_box this;
    replace : (□'□'□⁻¹'X.1) *⊢[𝓢] □ψ := Context.weakening! ?h₂ this;
    replace : (□'□⁻¹'X) *⊢[𝓢] □ψ := Context.boxbox_in_context_to_box this;
    replace : X *⊢[𝓢] □ψ := Context.weakening! ?h₃ this;
    exact membership_iff (by grind) |>.mpr this;
    case h₁ =>
      intro ξ;
      simp only [Set.mem_union, Finset.mem_coe, Set.mem_insert_iff];
      rintro (hξ₁ | hξ₂);
      . have := hΓ₁ hξ₁; tauto;
      . have := hΓ₂ hξ₂;
        simp at this;
        tauto;
    case h₂ =>
      intro ξ hξ;
      obtain ⟨ξ, hξ, rfl⟩ := hξ;
      have : ξ ∈ □'□⁻¹'X.1 := hΓ₁ hξ;
      obtain ⟨χ, hχ, rfl⟩ := Finset.LO.exists_of_mem_box this;
      use □χ;
      grind;
    case h₃ =>
      intro ξ hξ;
      obtain ⟨ξ, hξ, rfl⟩ := hξ;
      tauto;

omit [Consistent 𝓢] in
lemma truthlemma_lemma3 : 𝓢 ⊢ (φ ⋏ □(φ 🡒 □φ)) 🡒 □φ := by
  refine C!_trans ?_ $ inner_mdp! (𝓢 := 𝓢) (φ := φ) (ψ := □φ);
  apply CKK!_of_C!';
  exact axiomT!;

lemma truthlemma {X : (miniCanonicalModel 𝓢 φ).World} (q_sub : ψ ∈ φ.subformulas) :
  Satisfies (miniCanonicalModel 𝓢 φ) X ψ ↔ ψ ∈ X := by
  induction ψ generalizing X with
  | hatom => simp [Satisfies];
  | hfalsum => simp [Satisfies];
  | himp ψ χ ihq ihr =>
    constructor;
    . contrapose;
      intro h;
      apply Satisfies.not_imp.mpr;
      apply Satisfies.and_def.mpr;
      constructor;
      . apply ihq (by grind) |>.mpr;
        exact iff_not_mem_imp (ψ := ψ) (χ := χ) |>.mp h |>.1;
      . apply ihr (by grind) |>.not.mpr;
        exact iff_not_mem_compl (by grind) |>.not.mpr $ by
          push Not;
          exact iff_not_mem_imp (ψ := ψ) (χ := χ) |>.mp h |>.2;
    . contrapose;
      intro h;
      replace h := Satisfies.and_def.mp $ Satisfies.not_imp.mp h;
      obtain ⟨hq, hr⟩ := h;
      replace hq := ihq (by grind) |>.mp hq;
      replace hr := ihr (by grind) |>.not.mp hr;
      apply iff_not_mem_imp (ψ := ψ) (χ := χ) |>.mpr;
      constructor;
      . assumption;
      . simpa using iff_not_mem_compl (by grind) |>.not.mp hr;
  | hbox ψ ih =>
    constructor;
    . contrapose;
      by_cases w : ψ ∈ X;
      . intro h;
        obtain ⟨Y, hY⟩ := lindenbaum (𝓢 := 𝓢) (truthlemma_lemma1 q_sub) (truthlemma_lemma2 q_sub h);
        simp only [Finset.union_subset_iff] at hY;
        simp only [Satisfies]; push Not;
        use Y;
        constructor;
        . constructor;
          . intro χ _ hr₂;
            apply hY.1;
            apply Finset.LO.mem_box_prebox_of_mem_of_mem_box;
            simpa;
          . apply imp_iff_not_or (b := X = Y) |>.mpr;
            left; push Not;
            use (ψ 🡒 □ψ);
            refine ⟨?_, ?_, ?_⟩;
            . simp [Formula.subformulasGrz, Finset.LO.preboxItr];
              grind;
            . apply hY.2;
              simp;
            . by_contra hC;
              have : ↑X *⊢[𝓢] ψ := membership_iff (by grind) |>.mp w;
              have : ↑X *⊢[𝓢] □(ψ 🡒 □ψ) := membership_iff (by simp [Finset.LO.preboxItr]; grind) |>.mp hC;
              have : ↑X *⊢[𝓢] (ψ ⋏ □(ψ 🡒 □ψ)) 🡒 □ψ := Context.of! $ truthlemma_lemma3;
              have : ↑X *⊢[𝓢] □ψ := this ⨀ K!_intro (by assumption) (by assumption);
              have : □ψ ∈ X := membership_iff (by grind) |>.mpr this;
              contradiction;
        . apply ih (by grind) |>.not.mpr;
          apply iff_not_mem_compl (by grind) |>.not.mpr;
          push Not;
          apply hY.2;
          simp;
      . intro _;
        simp only [Satisfies]; push Not;
        use X;
        constructor;
        . apply Frame.refl;
        . exact ih (by grind) |>.not.mpr w;
    . intro h Y RXY;
      apply ih (by grind) |>.mpr;
      have : ↑Y *⊢[𝓢] □ψ 🡒 ψ := Context.of! $ axiomT!;
      have : ↑Y *⊢[𝓢] ψ := this ⨀ (membership_iff (by grind) |>.mp (RXY.1 ψ (by simp [Finset.LO.preboxItr]; grind) h));
      exact membership_iff (by grind) |>.mpr this;

lemma complete_of_mem_miniCanonicalFrame
  (C : Kripke.FrameClass)
  (hC : ∀ {φ}, miniCanonicalFrame 𝓢 φ ∈ C)
  : Complete 𝓢 C := ⟨by
  intro φ;
  contrapose;
  intro h;
  apply Semantics.set_models_iff.not.mpr;
  push Not;
  use (miniCanonicalFrame 𝓢 φ);
  constructor;
  . apply hC;
  . apply ValidOnFrame.not_of_exists_valuation_world;
    obtain ⟨X, hX₁⟩ := lindenbaum (𝓢 := 𝓢) (Φ := {-φ}) (Ψ := φ.subformulasGrz)
      (by
        simp only [Finset.singleton_subset_iff];
        apply FormulaFinset.complementary_comp;
        grind;
      )
      (FormulaFinset.unprovable_iff_singleton_compl_consistent.mpr h);
    use (miniCanonicalModel _ φ).Val, X;
    apply truthlemma (by grind) |>.not.mpr;
    exact iff_not_mem_compl (by grind) |>.not.mpr $ by
      push Not;
      apply hX₁;
      tauto;
⟩

instance : Complete Modal.Grz FrameClass.finite_Grz := complete_of_mem_miniCanonicalFrame FrameClass.finite_Grz $ by
  simp only [Set.mem_setOf_eq];
  intro φ;
  infer_instance;


instance : Modal.S4McK ⪱ Modal.Grz := by
  constructor;
  . apply Modal.Kripke.weakerThan_of_subset_frameClass FrameClass.S4McK FrameClass.finite_Grz
    intro F hF;
    simp_all only [Set.mem_setOf_eq];
    infer_instance;
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.Grz (.atom 0)
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.S4McK)
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 3, λ x y => y = 2 ∨ x = 0 ∨ x = 1⟩, λ _ w => w = 1 ∨ w = 2⟩, 0;
      constructor;
      . exact {
          refl := by omega,
          trans := by omega,
          mckinsey := by simp;
        }
      . suffices (∀ x : Fin 3, (∀ (y : Fin 3), x = 0 ∨ x = 1 → y = 1 ∨ y = 2 → ∀ z : Fin 3, y = 0 ∨ y = 1 → z = 1 ∨ z = 2) → x ≠ 1 → x = 2) by
          simpa [Semantics.Models, Satisfies];
        by_contra! hC;
        obtain ⟨x, hx, _, _⟩ := hC;
        have := hx 1 (by grind) (by grind) 0 (by grind);
        grind;

instance : Modal.S4 ⪱ Modal.Grz := calc
  Modal.S4 ⪱ Modal.S4McK := by infer_instance
  _        ⪱ Modal.Grz   := by infer_instance

end Grz.Kripke


end LO.Modal
end
