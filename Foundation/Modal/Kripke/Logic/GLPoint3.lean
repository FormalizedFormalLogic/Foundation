import Foundation.Modal.Kripke.Logic.GL.Completeness
import Foundation.Modal.Kripke.Logic.K4Point3
import Foundation.Modal.Logic.Global

namespace LO.Modal

open Entailment
open Entailment.Context
open Formula
open Formula.Kripke
open Hilbert.Kripke
open Kripke

namespace Kripke

protected class Frame.IsFiniteGLPoint3 (F : Frame) extends F.IsFiniteGL, F.IsPiecewiseConnected
protected class Frame.IsFiniteGLPoint3₂ (F : Frame) extends F.IsFiniteGL, F.IsConnected

abbrev FrameClass.finite_GLPoint3 : FrameClass := { F | F.IsFiniteGLPoint3 }
abbrev FrameClass.finite_GLPoint3₂ : FrameClass := { F | F.IsFiniteGLPoint3₂ }

instance : blackpoint.IsFiniteGLPoint3 where
  p_connected := by tauto;

end Kripke


namespace Hilbert.GLPoint3.Kripke

instance : Sound Hilbert.GLPoint3 FrameClass.finite_GLPoint3 := instSound_of_validates_axioms $ by
  apply FrameClass.validates_with_AxiomK_of_validates;
  constructor;
  rintro _ (rfl | rfl | rfl) F ⟨_, _⟩;
  . exact validate_AxiomL_of_finite_trans_irrefl;
  . exact validate_WeakPoint3_of_weakConnected;

instance : Entailment.Consistent Hilbert.GLPoint3 :=
  consistent_of_sound_frameclass FrameClass.finite_GLPoint3 $ by
    use blackpoint;
    constructor;


section

open MaximalConsistentTableau

instance : Hilbert.K ⪯ Hilbert.GLPoint3 := Hilbert.Normal.weakerThan_of_subset_axioms (by simp)

open LO.Entailment Modal.Entailment in
open Formula.Kripke in
private lemma complete_lemma₁ : Hilbert.GLPoint3 ⊢! ∼□φ ➝ ◇(□φ ⋏ ∼φ) := by
  apply CN!_of_CN!_left;
  apply C!_trans ?_ axiomL!;
  apply WeakerThan.pbl (𝓢 := Hilbert.K);
  -- TODO: `K_prover`
  apply Complete.complete (𝓜 := Kripke.FrameClass.K);
  intro F _ V x h₁ y Rxy h₂;
  have := (Satisfies.not_dia_def.mp h₁) y Rxy;
  have := Satisfies.and_def.not.mp this;
  push_neg at this;
  have := this h₂;
  simpa using Satisfies.not_def.not.mp this;

private lemma complete_lemma₂ {v : (canonicalModel Hilbert.GLPoint3).World } (h : ∼□φ ∈ v.1.1) :
  ∃! u, v ≺ u ∧ □φ ∈ u.1.1 ∧ ∼φ ∈ u.1.1 := by
  obtain ⟨u, Rvu, hu⟩ := iff_mem₁_dia.mp $ mdp_mem₁_provable complete_lemma₁ h;
  use u;
  constructor;
  . refine ⟨Rvu, iff_mem₁_and.mp hu⟩;
  . rintro y ⟨Rvy, h₁, h₂⟩;
    rcases Frame.p_connected Rvu Rvy with (Ruy | _ | Ryu);
    . exfalso;
      apply neither ⟨Ruy $ iff_mem₁_and.mp hu |>.1, iff_mem₁_neg.mp h₂⟩;
    . tauto;
    . exfalso;
      apply neither ⟨Ryu h₁, iff_mem₁_neg.mp $ iff_mem₁_and.mp hu |>.2⟩;

open Classical in
instance : Complete Hilbert.GLPoint3 FrameClass.finite_GLPoint3₂ := ⟨by
  intro φ;
  contrapose!;
  intro hφ;
  obtain ⟨u, hu⟩ := ValidOnModel.exists_world_of_not $ iff_valid_on_canonicalModel_deducible.not.mpr hφ;
  replace hu : φ ∈ u.1.2 := truthlemma₂.mpr hu;

  let v : (canonicalModel Hilbert.GLPoint3).World := if h : □φ ∈ u.1.1 then u else
    (complete_lemma₂ $ iff_mem₁_neg'.mpr h) |>.choose;
  have hv₁ : □φ ∈ v.1.1 := by
    dsimp [v];
    split;
    . assumption;
    . rename_i h;
      exact (complete_lemma₂ $ iff_mem₁_neg'.mpr h) |>.choose_spec.1.2.1;
  have hv₂ : φ ∈ v.1.2 := by
    dsimp [v];
    split;
    . assumption;
    . apply iff_mem₁_neg.mp;
      rename_i h;
      exact (complete_lemma₂ $ iff_mem₁_neg'.mpr h) |>.choose_spec.1.2.2;

  apply Kripke.not_validOnFrameClass_of_exists_model_world;

  let M : Kripke.Model := {
    World := {
      x // x = v ∨ (v ≺ x ∧ ∃ ψ ∈ φ.subformulas.prebox, □ψ ∈ v.1.2 ∧ □ψ ∈ x.1.1 ∧ ψ ∈ x.1.2)
    }
    world_nonempty := ⟨v, by simp⟩,
    Rel := λ x y => (canonicalModel Hilbert.GLPoint3).Rel x.1 y.1
    Val := λ x => (canonicalModel Hilbert.GLPoint3).Val x
  }
  use M, ⟨v, by simp⟩;
  have : M.IsTransitive := ⟨by
    suffices ∀ (x y z : M.World), (canonicalModel Hilbert.GLPoint3).Rel x y → (canonicalModel Hilbert.GLPoint3).Rel y z → (canonicalModel Hilbert.GLPoint3).Rel x z by tauto;
    intro _ _ _;
    apply Frame.trans;
  ⟩
  have : M.IsIrreflexive := ⟨by
    rintro ⟨x, rfl | ⟨Rrx, ψ, _, hψ₂, hψ₃, hψ₄⟩⟩;
    . by_contra hC; apply neither ⟨hC hv₁, hv₂⟩;
    . by_contra hC; apply neither ⟨hC hψ₃, hψ₄⟩;
  ⟩
  have : M.IsConnected := ⟨by
    suffices ∀ x y : M.World, x ≠ y → (M.Rel x y ∨ M.Rel y x) by
      intro x y;
      have := this x y;
      tauto;
    rintro ⟨x, rfl | ⟨Rvx, _⟩⟩ ⟨y, rfl | ⟨Rvy, _⟩⟩ hxy;
    . simp at hxy;
    . tauto;
    . tauto;
    . apply Frame.p_connected' Rvx Rvy ?_;
      simp_all [M];
  ⟩
  constructor;
  . exact {
      world_finite := by
        dsimp [M];
        sorry;
    }
  . have : ∀ x : M.World, ∀ ψ ∈ φ.subformulas, (Satisfies _ x ψ ↔ ψ ∈ x.1.1.1) := by
      intro x ψ hψ;
      induction ψ generalizing x with
      | hatom => simp [Satisfies, M];
      | hfalsum => simp [Satisfies];
      | himp ψ ξ ihψ ihξ =>
        replace ihψ := ihψ x (by grind);
        replace ihξ := ihξ x (by grind);
        simp [
          Satisfies, ihψ, ihξ,
          iff_mem₂_imp,
          ←iff_not_mem₂_mem₁
        ];
      | hbox ψ ihψ =>
        constructor;
        . contrapose!;
          intro h;
          apply Satisfies.not_box_def.mpr;
          have : □ψ ∉ v.1.1 := by
            rcases M.connected ⟨v, by simp⟩ x with (Rvx | rfl | Rxv);
            . contrapose! h;
              apply Rvx;
              apply mdp_mem₁_provable ?_ $ h;
              simp;
            . exact h;
            . rcases x.2 with (exv | ⟨Rvx, _⟩);
              . exact exv ▸ h;
              . exfalso;
                apply M.irrefl _ $ M.trans Rxv Rvx;
          obtain ⟨y, ⟨Rvy, hy₁, hy₂⟩, _⟩ := complete_lemma₂ $ iff_mem₁_neg'.mpr this;
          use ⟨y, by
            right;
            constructor;
            . exact Rvy;
            . use ψ;
              refine ⟨?_, ?_, ?_, ?_⟩;
              . simpa;
              . apply iff_not_mem₁_mem₂.mp; simpa;
              . simpa;
              . exact iff_mem₁_neg.mp $ hy₂;
          ⟩;
          constructor;
          . apply (or_iff_not_imp_right.mp $ M.connected' x _ ?_) ?_;
            . contrapose! h;
              subst h;
              apply hy₁;
            . by_contra Ryx;
              apply h;
              apply Ryx;
              apply mdp_mem₁_provable ?_ $ hy₁;
              simp;
          . apply ihψ _ (by grind) |>.not.mpr;
            apply iff_mem₁_neg'.mp hy₂;
        . intro h y Rxy;
          apply ihψ y (by grind) |>.mpr;
          apply canonicalModel.def_rel_box_mem₁.mp Rxy;
          simpa using h;
    apply this _ _ (by simp) |>.not.mpr;
    apply iff_not_mem₁_mem₂.mpr;
    exact hv₂;
⟩

end


instance : Hilbert.GL ⪱ Hilbert.GLPoint3 := by
  constructor;
  . apply Hilbert.Normal.weakerThan_of_provable_axioms;
    rintro _ (rfl | rfl | rfl) <;> simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.WeakPoint3 (.atom 0) (.atom 1));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := Kripke.FrameClass.finite_GL);
      let M : Model := ⟨⟨Fin 3, λ x y => (x = 0 ∧ y = 1) ∨ (x = 0 ∧ y = 2)⟩, (λ w a => match a with | 0 => w = 1 | 1 => w = 2 | _ => False)⟩;
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use M, 0;
      constructor;
      . apply Set.mem_setOf_eq.mpr;
        exact {
          trans := by omega,
          irrefl := by omega
        };
      . suffices (0 : M.World) ≺ 1 ∧ (∀ x, (1 : M.World) ≺ x → x = 1) ∧ (0 : M.World) ≺ 2 ∧ ∀ x, (2 : M.World) ≺ x → x = 2 by
          simpa [Semantics.Realize, Satisfies, ValidOnFrame, M];
        refine ⟨?_, ?_, ?_, ?_⟩;
        all_goals omega;

instance : Hilbert.K4Point3 ⪱ Hilbert.GLPoint3 := by
  constructor;
  . apply Hilbert.Normal.weakerThan_of_provable_axioms;
    rintro _ (rfl | rfl | rfl) <;> simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.L (.atom 0));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := Kripke.FrameClass.K4Point3);
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 2, λ x y => x ≤ y⟩, (λ w a => False)⟩, 0;
      constructor;
      . apply Set.mem_setOf_eq.mpr;
        constructor;
      . simp [Semantics.Realize, Satisfies];
        constructor;
        . intro y Rxy;
          use y;
        . use 1;
          omega;

end Hilbert.GLPoint3.Kripke

instance : Modal.GL ⪱ Modal.GLPoint3 := inferInstance

instance : Modal.K4Point3 ⪱ Modal.GLPoint3 := inferInstance

end LO.Modal
