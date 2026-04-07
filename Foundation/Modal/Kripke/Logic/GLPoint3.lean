module

public import Foundation.Modal.Kripke.Logic.GL.Completeness
public import Foundation.Modal.Kripke.Logic.K4Point3
public import Foundation.Modal.Logic.Global
public import Mathlib.Data.Finite.Sum


@[expose] public section

lemma Finite.of_scoped_subtype {P Q : α → Prop} (h : ∀ x : α, Q x → P x) [Finite { x // P x }] : Finite { x // Q x } := by
  apply Finite.of_injective (β := { x // P x }) (λ x => ⟨x.1, h _ x.2⟩);
  simp [Function.Injective];


namespace LO.Modal

open Entailment
open Entailment.Context
open Formula
open Formula.Kripke
open Modal.Kripke
open Kripke

namespace Kripke

protected class Frame.IsFiniteGLPoint3 (F : Frame) extends F.IsFiniteGL, F.IsConnected
protected class Frame.IsFiniteGLPoint3' (F : Frame) extends F.IsFiniteGL, F.IsPiecewiseConnected

abbrev FrameClass.finite_GLPoint3 : FrameClass := { F | F.IsFiniteGLPoint3 }

instance : blackpoint.IsFiniteGLPoint3 where
  trichotomous := by tauto

end Kripke


namespace GLPoint3.Kripke

instance : Sound Modal.GLPoint3 FrameClass.finite_GLPoint3 := instSound_of_validates_axioms $ by
  apply FrameClass.validates_with_AxiomK_of_validates;
  constructor;
  rintro _ (rfl | rfl | rfl) F ⟨_, _⟩;
  . exact validate_AxiomL_of_finite_trans_irrefl;
  . exact validate_WeakPoint3_of_weakConnected;

instance : Sound Modal.GLPoint3 { F : Frame | F.IsFiniteGLPoint3' } := instSound_of_validates_axioms $ by
  apply FrameClass.validates_with_AxiomK_of_validates;
  constructor;
  rintro _ (rfl | rfl | rfl) F ⟨_, _⟩;
  . exact validate_AxiomL_of_finite_trans_irrefl;
  . exact validate_WeakPoint3_of_weakConnected;

instance : Entailment.Consistent Modal.GLPoint3 :=
  consistent_of_sound_frameclass FrameClass.finite_GLPoint3 $ by
    use blackpoint;
    constructor;


section

open MaximalConsistentTableau

instance : Modal.K ⪯ Modal.GLPoint3 := Hilbert.Normal.weakerThan_of_subset_axioms (by simp)

open LO.Entailment Modal.Entailment in
open Formula.Kripke in
private lemma complete.lemma₁ : Modal.GLPoint3 ⊢ ∼□φ 🡒 ◇(□φ ⋏ ∼φ) := by
  apply CN!_of_CN!_left;
  apply C!_trans ?_ axiomL!;
  apply WeakerThan.pbl (𝓢 := Modal.K);
  -- TODO: `K_prover`
  apply Complete.complete (𝓜 := Kripke.FrameClass.K);
  intro F _ V x h₁ y Rxy h₂;
  have := (Satisfies.not_dia_def.mp h₁) y Rxy;
  have := Satisfies.and_def.not.mp this;
  push Not at this;
  have := this h₂;
  simpa using Satisfies.not_def.not.mp this;

private lemma complete.lemma₂ {v : (canonicalModel Modal.GLPoint3).World } (h : ∼□φ ∈ v.1.1) :
  ∃! u, v ≺ u ∧ □φ ∈ u.1.1 ∧ φ ∈ u.1.2 := by
  obtain ⟨u, Rvu, hu⟩ := iff_mem₁_dia.mp $ mdp_mem₁_provable lemma₁ h;
  use u;
  constructor;
  . refine ⟨Rvu, by grind⟩;
  . rintro y ⟨Rvy, h₁, h₂⟩;
    rcases Frame.p_connected Rvu Rvy with (Ruy | _ | Ryu);
    . exfalso;
      apply neither ⟨Ruy $ (show □φ ∈ u.1.1 by grind), h₂⟩;
    . tauto;
    . exfalso;
      apply neither ⟨Ryu h₁, by grind⟩;

private def complete.filteredModel
  (v : (canonicalModel Modal.GLPoint3).World)
  (φ : Formula ℕ)
  (_ : □φ ∈ v.1.1) (_ : φ ∈ v.1.2)
  : Kripke.Model where
  World := { x // x = v ∨ (v ≺ x ∧ ∃ ψ ∈ (□⁻¹'φ.subformulas), □ψ ∈ v.1.2 ∧ □ψ ∈ x.1.1 ∧ ψ ∈ x.1.2) }
  world_nonempty := ⟨v, by grind⟩
  Rel := λ x y => x.1 ≺ y.1
  Val := λ a x => (canonicalModel Modal.GLPoint3).Val a x

private instance complete.filteredModel.isFiniteGLPoint3 : Frame.IsFiniteGLPoint3 (complete.filteredModel v φ hv₁ hv₂).toFrame where
  trans := by
    suffices ∀ (x y z : (filteredModel v φ _ _)), (canonicalModel Modal.GLPoint3).Rel x.1 y.1 → (canonicalModel Modal.GLPoint3).Rel y.1 z.1 → (canonicalModel Modal.GLPoint3).Rel x.1 z.1 by tauto;
    intro _ _ _;
    apply Frame.trans;
  irrefl := by
    rintro ⟨x, rfl | ⟨Rrx, ψ, _, hψ₂, hψ₃, hψ₄⟩⟩;
    . by_contra hC; apply neither ⟨hC hv₁, hv₂⟩;
    . by_contra hC; apply neither ⟨hC hψ₃, hψ₄⟩;
  trichotomous := by
    suffices ∀ x y : (filteredModel v φ _ _), x ≠ y → (x ≺ y ∨ y ≺ x) by
      intro x y;
      have := this x y;
      tauto;
    rintro ⟨x, rfl | ⟨Rvx, _⟩⟩ ⟨y, rfl | ⟨Rvy, _⟩⟩ hxy;
    . simp at hxy;
    . tauto;
    . tauto;
    . apply Frame.p_connected' Rvx Rvy ?_;
      simpa [filteredModel] using hxy;
  world_finite := by
    dsimp [complete.filteredModel];
    have : Finite { ψ // ψ ∈ (□⁻¹'φ.subformulas) ∧ ∼□ψ ∈ v.1.1 } := Finite.of_scoped_subtype (P := λ ψ => ψ ∈ (□⁻¹'φ.subformulas)) $ by tauto;
    apply Finite.of_surjective (α := Unit ⊕ { ψ // ψ ∈ (□⁻¹'φ.subformulas : Finset (Formula ℕ)) ∧ ∼□ψ ∈ v.1.1 })
      (f := λ x => match x with
        | .inl _ => ⟨v, by grind⟩
        | .inr ψ =>
          letI u := lemma₂ (v := v) ψ.2.2;
          ⟨u.choose, by
            right;
            refine ⟨?_, ψ, ?_, ?_, ?_, ?_⟩;
            . exact u.choose_spec.1.1;
            . simpa using ψ.2.1;
            . grind;
            . exact u.choose_spec.1.2.1;
            . exact u.choose_spec.1.2.2;
          ⟩
      );
    simp only [
      Function.Surjective, and_imp, Sum.exists, exists_const, Subtype.exists,
      Subtype.forall, Finset.mem_preimage, Function.iterate_one, Subtype.mk.injEq, forall_eq_or_imp,
      true_or, forall_exists_index, true_and
    ];
    intro x Rvx ψ hψ hv₁ hv₂ hv₃;
    right;
    use ψ, ⟨hψ, by grind⟩;
    simp [(lemma₂ (iff_mem₁_neg.mpr $ hv₁) |>.choose_spec.2 x $ by simp_all)];

private lemma complete.filteredModel.truthlemma : ∀ x : (complete.filteredModel v φ hv₁ hv₂), ∀ ψ ∈ φ.subformulas, (Satisfies _ x ψ ↔ ψ ∈ x.1.1.1) := by
  intro x ψ hψ;
  induction ψ generalizing x with
  | hatom => simp [Satisfies, filteredModel];
  | hfalsum => simp [Satisfies];
  | himp ψ ξ ihψ ihξ =>
    suffices ψ ∈ x.1.1.1 → ξ ∈ x.1.1.1 ↔ ψ 🡒 ξ ∈ x.1.1.1 by simpa [Satisfies, (ihψ x (by grind)), (ihξ x (by grind))];
    grind;
  | hbox ψ ihψ =>
    constructor;
    . contrapose!;
      intro h;
      apply Satisfies.not_box_def.mpr;
      have : □ψ ∉ v.1.1 := by
        rcases (filteredModel v φ _ _).connected ⟨v, by grind⟩ x with (Rvx | rfl | Rxv);
        . contrapose! h;
          apply Rvx;
          apply mdp_mem₁_provable ?_ $ h;
          simp;
        . exact h;
        . rcases x.2 with (exv | ⟨Rvx, _⟩);
          . exact exv ▸ h;
          . exfalso;
            apply (filteredModel v φ _ _).irrefl _ $ (filteredModel v φ _ _).trans Rxv Rvx;
      obtain ⟨y, ⟨Rvy, hy₁, hy₂⟩, _⟩ := lemma₂ $ iff_mem₁_neg'.mpr this;
      use ⟨y, by
        right;
        constructor;
        . exact Rvy;
        . use ψ;
          refine ⟨?_, ?_, ?_, ?_⟩;
          . simpa [Finset.LO.preboxItr]
          . apply iff_not_mem₁_mem₂.mp; simpa;
          . simpa;
          . simpa;
      ⟩;
      constructor;
      . apply (or_iff_not_imp_right.mp $ (filteredModel v φ _ _).connected' x _ ?_) ?_;
        . contrapose! h;
          subst h;
          apply hy₁;
        . by_contra Ryx;
          apply h;
          apply Ryx;
          apply mdp_mem₁_provable ?_ $ hy₁;
          simp;
      . apply ihψ _ (by grind) |>.not.mpr;
        grind;
    . intro h y Rxy;
      apply ihψ y (by grind) |>.mpr;
      apply Rxy;
      simpa using h;

open Classical in
open complete in
instance complete : Complete Modal.GLPoint3 FrameClass.finite_GLPoint3 := ⟨by
  intro φ;
  contrapose!;
  intro hφ;
  obtain ⟨u, hu⟩ := ValidOnModel.exists_world_of_not $ iff_valid_on_canonicalModel_deducible.not.mpr hφ;
  replace hu : φ ∈ u.1.2 := truthlemma₂.mpr hu;

  let v : (canonicalModel Modal.GLPoint3).World := if h : □φ ∈ u.1.1 then u else (lemma₂ $ iff_mem₁_neg'.mpr h) |>.choose;
  have hv₁ : □φ ∈ v.1.1 := by
    unfold v;
    split;
    . assumption;
    . rename_i h;
      exact (lemma₂ $ iff_mem₁_neg'.mpr h) |>.choose_spec.1.2.1;
  have hv₂ : φ ∈ v.1.2 := by
    unfold v;
    split;
    . assumption;
    . rename_i h;
      exact (lemma₂ $ (iff_mem₁_neg'.mpr h)) |>.choose_spec.1.2.2;

  apply Kripke.not_validOnFrameClass_of_exists_model_world;
  use (complete.filteredModel v φ hv₁ hv₂), ⟨v, by grind⟩;
  constructor;
  . apply Set.mem_setOf_eq.mpr; infer_instance;
  . apply filteredModel.truthlemma _ _ (by grind) |>.not.mpr;
    grind;
⟩

end


instance : Modal.GL ⪱ Modal.GLPoint3 := by
  constructor;
  . apply Hilbert.Normal.weakerThan_of_provable_axioms;
    rintro _ (rfl | rfl | rfl) <;> simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.WeakPoint3 (.atom 0) (.atom 1));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := Kripke.FrameClass.finite_GL);
      let M : Model := ⟨⟨Fin 3, λ x y => (x = 0 ∧ y = 1) ∨ (x = 0 ∧ y = 2)⟩, (λ a w => match a with | 0 => w = 1 | 1 => w = 2 | _ => False)⟩;
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use M, 0;
      constructor;
      . apply Set.mem_setOf_eq.mpr;
        exact {
          trans := by omega,
          irrefl := by omega
        };
      . suffices (0 : M.World) ≺ 1 ∧ (∀ x, (1 : M.World) ≺ x → x = 1) ∧ (0 : M.World) ≺ 2 ∧ ∀ x, (2 : M.World) ≺ x → x = 2 by
          simp [Semantics.Models, Satisfies, ValidOnFrame, M];
          grind;
        refine ⟨?_, ?_, ?_, ?_⟩;
        all_goals omega;

instance : Modal.K4Point3 ⪱ Modal.GLPoint3 := by
  constructor;
  . apply Hilbert.Normal.weakerThan_of_provable_axioms;
    rintro _ (rfl | rfl | rfl) <;> simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.L (.atom 0));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := Kripke.FrameClass.K4Point3);
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 2, λ x y => x ≤ y⟩, (λ a w => False)⟩, 0;
      constructor;
      . apply Set.mem_setOf_eq.mpr;
        constructor;
      . simp [Semantics.Models, Satisfies];
        tauto;

end GLPoint3.Kripke

end LO.Modal
end
