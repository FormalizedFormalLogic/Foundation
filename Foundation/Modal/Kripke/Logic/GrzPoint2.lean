module

public import Foundation.Modal.Kripke.Logic.Grz.Completeness
public import Foundation.Modal.Kripke.Logic.S4Point2McK
public import Mathlib.Data.Finite.Sum

@[expose] public section

namespace LO.Modal

open Entailment
open Entailment.Context
open Formula
open Formula.Kripke
open Modal.Kripke
open Kripke

section

namespace Kripke

variable {F : Frame}

def Frame.terminals (F : Frame) : Set F.World := { t | ∀ {y}, t ≺ y → t = y }
def Frame.terminals_of (F : Frame) (x : F.World) : Set F.World := { t | x ≺^+ t ∧ ∀ {y}, t ≺ y → t = y }

lemma Frame.exists_card [IsFinite F] : ∃ n : ℕ+, Nonempty (F.World ≃ Fin n) := by
  obtain ⟨n, ⟨hn⟩⟩ := Finite.exists_equiv_fin F.World;
  refine ⟨⟨n, ?_⟩, ⟨hn⟩⟩
  . by_contra hn0;
    replace hn0 : n = 0 := by simpa [gt_iff_lt, not_lt, nonpos_iff_eq_zero] using hn0;
    subst hn0;
    apply Fin.elim0 $ hn.toFun (F.world_nonempty.some);

lemma Frame.exists_terminal [F.SatisfiesMcKinseyCondition] : ∃ t ∈ F.terminals, s ≺ t := by
  obtain ⟨t, ht₁, ht₂⟩ := F.mckinsey s;
  use t;
  constructor;
  . apply ht₂;
  . assumption;

end Kripke


namespace Formula.Kripke.Satisfies

variable {F V} {φ : Formula ℕ}

lemma box_at_terminal {x : F.World} (hx : x ∈ F.terminals) (h : Satisfies ⟨F, V⟩ x φ) : Satisfies ⟨F, V⟩ x (□φ) := by
  intro y Rxy;
  have := hx Rxy;
  subst this;
  exact h;

lemma dia_at_terminal {x : F.World} (hx : x ∈ F.terminals) (h : ¬Satisfies ⟨F, V⟩ x φ) : ¬Satisfies ⟨F, V⟩ x (◇φ) := by
  apply Satisfies.dia_def.not.mpr;
  push_neg;
  intro y Rxy;
  have := hx Rxy;
  subst this;
  exact h;

end Formula.Kripke.Satisfies

end


section

open LO.Entailment LO.Entailment.FiniteContext LO.Modal.Entailment

instance : Modal.Grz ⪯ Modal.GrzPoint2 := Hilbert.Normal.weakerThan_of_subset_axioms $ by grind;

lemma GrzPoint2_of_Grz (h : (φ.atoms.image (λ a => Axioms.Point2 (.atom a))).toSet *⊢[Modal.Grz] φ) : Modal.GrzPoint2 ⊢ φ := by
  obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp h;
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hΓ₁;
  replace hΓ₂ : Modal.GrzPoint2 ⊢ ⋀Γ 🡒 φ := WeakerThan.pbl $ FiniteContext.provable_iff.mp hΓ₂;
  exact hΓ₂ ⨀ by
    apply Conj₂!_intro;
    intro γ hγ;
    obtain ⟨a, ha, rfl⟩ := hΓ₁ _ hγ;
    exact axiomPoint2!;

lemma not_Grz_of_not_GrzPoint2 (h : Modal.GrzPoint2 ⊬ φ) : (φ.atoms.image (λ a => Axioms.Point2 (.atom a))).toList ⊬[Modal.Grz] φ := by
  have := Context.provable_iff.not.mp $ not_imp_not.mpr GrzPoint2_of_Grz h;
  push_neg at this;
  convert this ((φ.atoms.image (λ a => Axioms.Point2 (.atom a))).toList) $ by simp;

end


namespace Kripke

variable {F : Frame}

protected class Frame.IsFiniteGrzPoint2 (F : Frame) extends F.IsFinite, F.IsPartialOrder, F.IsPiecewiseStronglyConvergent where

protected abbrev FrameClass.finite_GrzPoint2 : FrameClass := { F | F.IsFiniteGrzPoint2 }

instance [F.IsFiniteGrzPoint2] : F.IsS4Point2McK where

end Kripke

instance : Sound Modal.GrzPoint2 FrameClass.finite_GrzPoint2 := instSound_of_validates_axioms $ by
  apply FrameClass.validates_with_AxiomK_of_validates;
  constructor;
  rintro _ (rfl | rfl | rfl) F ⟨_, _⟩;
  . exact validate_AxiomGrz_of_finite_strict_preorder;
  . exact validate_AxiomPoint2_of_confluent;

instance : Entailment.Consistent Modal.GrzPoint2 :=
  consistent_of_sound_frameclass FrameClass.finite_GrzPoint2 $ by
    use whitepoint;
    constructor;


section

open Relation

instance : Complete Modal.GrzPoint2 FrameClass.finite_GrzPoint2 := ⟨by
  intro φ;
  contrapose;
  intro hφ;

  replace hφ : Modal.Grz ⊬ ⋀((φ.atoms.image (λ a => Axioms.Point2 (atom a))).toList) 🡒 φ := not_Grz_of_not_GrzPoint2 hφ;
  generalize eΓ : (φ.atoms.image (λ a => Axioms.Point2 (atom a))).toList = Γ at hφ;
  obtain ⟨M, r, hM, hΓφ⟩ := exists_model_world_of_not_validOnFrameClass $ not_imp_not.mpr (Complete.complete (𝓢 := Modal.Grz) (𝓜 := FrameClass.finite_Grz)) hφ;
  replace hM := Set.mem_setOf_eq.mp hM;
  have : M.IsPartialOrder := inferInstance;

  let RM := M↾r;
  let r' : RM.Root := ⟨⟨r, by tauto⟩, by grind⟩;
  have : RM.IsPartialOrder := inferInstance;

  replace hΓφ : ¬(Satisfies RM r'.1 (⋀Γ) → Satisfies RM r'.1 φ) := Satisfies.imp_def.not.mp $ Model.pointGenerate.modal_equivalent_at_root (r := r) |>.not.mpr hΓφ;
  push_neg at hΓφ;
  obtain ⟨hΓ, hφ⟩ := hΓφ;

  let M' : Kripke.Model := {
    World := RM.World ⊕ Unit
    Rel x y :=
      match x, y with
      | _, (Sum.inr _) => True
      | (Sum.inl x), (Sum.inl y) => RM.Rel x y
      | _, _ => False
    Val a x :=
      match x with
      | Sum.inl x => RM.Val a x
      | _ => ∀ y ∈ RM.toFrame.terminals, RM.Val a y
  };
  apply not_validOnFrameClass_of_exists_model_world;
  use M', (Sum.inl r');
  constructor;
  . apply Set.mem_setOf_eq.mpr;
    exact {
      refl := by grind;
      trans := by grind;
      antisymm := by grind;
      ps_convergent := by
        rintro x y z Rxy Ryz;
        use (Sum.inr ());
    }
  . have H₁ : ∀ a ∈ φ.atoms, ∀ t ∈ RM.toFrame.terminals, ∀ t' ∈ RM.toFrame.terminals, RM a t → RM a t' := by
      intro a ha t t_terminal t' t'_terminal hy;
      by_contra hy';
      have : ¬Satisfies _ t' (◇atom a) := Kripke.Satisfies.dia_at_terminal t'_terminal hy';
      have : ¬Satisfies _ r'.1 (□(◇atom a)) := by
        apply Satisfies.box_def.not.mpr;
        push_neg;
        use t';
        constructor;
        . grind;
        . assumption;
      have : ¬Satisfies _ r'.1 (◇(□atom a)) := by
        contrapose! this;
        apply Satisfies.conj_def.mp hΓ $ Axioms.Point2 (atom a);
        . subst eΓ;
          simp only [Finset.mem_toList, Finset.mem_image];
          use a;
        . assumption;
      have := Satisfies.dia_def.not.mp this;
      push_neg at this;
      have : ¬Satisfies _ t (□atom a) := this t (by grind);
      have : Satisfies _ t (□atom a) := Kripke.Satisfies.box_at_terminal t_terminal hy;
      contradiction;
    have H₂ : ∀ t ∈ RM.terminals, ∀ ψ ∈ φ.subformulas, (Satisfies _ t ψ) ↔ (Satisfies M' (Sum.inr ()) ψ) := by
      intro t t_terminal ψ ψ_sub;
      induction ψ with
      | hatom a =>
        simp only [Satisfies.iff_models, Satisfies, RM, M']
        constructor;
        . intro ha t' t'_terminal;
          exact H₁ a (iff_mem_atoms_mem_subformula.mpr ψ_sub) t t_terminal t' t'_terminal ha;
        . intro h;
          apply h;
          exact t_terminal;
      | hfalsum => tauto;
      | himp χ ξ ihχ ihξ =>
        constructor;
        . intro h hχ;
          apply ihξ (by grind) |>.mp;
          apply h;
          apply ihχ (by grind) |>.mpr;
          assumption;
        . intro h hχ;
          apply ihξ (by grind) |>.mpr;
          apply h;
          apply ihχ (by grind) |>.mp;
          assumption;
      | hbox ψ ihψ =>
        constructor;
        . intro ht u Ru;
          match u with
          | Sum.inl x => simp [M', Frame.Rel'] at Ru;
          | Sum.inr _ =>
            apply ihψ (by grind) |>.mp;
            apply ht;
            apply Frame.refl;
        . intro ht u Rtu;
          have := t_terminal Rtu; subst this;
          apply ihψ (by grind) |>.mpr;
          apply ht;
          tauto;
    have : ∀ y : RM.World, ∀ ψ ∈ φ.subformulas, (Satisfies _ y ψ) ↔ (Satisfies M' (Sum.inl y) ψ) := by
      intro y ψ ψ_sub;
      induction ψ generalizing y with
      | hbox ψ ihψ =>
        constructor;
        . intro hψ v Ruv;
          match v with
          | Sum.inl x =>
            simp only [Frame.Rel', M', RM] at Ruv;
            exact ihψ x (by grind) |>.mp $ hψ _ Ruv;
          | Sum.inr x =>
            obtain ⟨t, t_terminal, Rut⟩ : ∃ t ∈ RM.terminals, y ≺ t := Frame.exists_terminal;
            apply H₂ t t_terminal ψ (by grind) |>.mp;
            apply hψ;
            exact Rut;
        . intro h v Ruv;
          exact ihψ v (by grind) |>.mpr $ @h (Sum.inl v) Ruv;
      | himp _ _ ihχ ihξ =>
        have := ihχ y (by grind);
        have := ihξ y (by grind);
        tauto;
      | _ => tauto;
    exact this r' φ (by simp) |>.not.mp hφ;
⟩

end


instance : Modal.Grz ⪱ Modal.GrzPoint2 := by
  constructor;
  . infer_instance;
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.Point2 (.atom 0);
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := Kripke.FrameClass.finite_Grz);
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨
        ⟨Fin 3, λ x y => x = 0 ∨ x = y⟩,
        λ a x => x = 1
      ⟩;
      use M, 0;
      constructor;
      . refine {
          refl := by omega
          trans := by omega
          antisymm := by simp [M]; omega;
        };
      . apply Satisfies.imp_def₂.not.mpr;
        push_neg;
        constructor;
        . apply Satisfies.dia_def.mpr;
          use 1;
          constructor;
          . omega;
          . intro y Rxy;
            simp [Satisfies, M];
            grind;
        . apply Satisfies.box_def.not.mpr;
          push_neg;
          use 2;
          constructor;
          . omega;
          . apply Satisfies.dia_def.not.mpr;
            push_neg;
            simp [M, Semantics.Models, Satisfies, Frame.Rel'];

instance : Modal.S4Point2McK ⪱ Modal.GrzPoint2 := by
  constructor;
  . apply Modal.Kripke.weakerThan_of_subset_frameClass FrameClass.S4Point2McK FrameClass.finite_GrzPoint2;
    intro F hF;
    simp_all only [Set.mem_setOf_eq];
    infer_instance;
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.Grz (.atom 0);
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := Kripke.FrameClass.S4Point2McK);
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 3, λ x y => y = 2 ∨ x = 0 ∨ x = 1⟩, λ _ w => w = 1 ∨ w = 2⟩, 0;
      constructor;
      . apply Set.mem_setOf_eq.mpr;
        exact {
          trans := by omega,
          refl := by omega,
          mckinsey := by simp;
          ps_convergent := by
            intro x y z Rxy Rxz;
            use 2;
            omega;
        };
      . suffices (∀ x : Fin 3, (∀ (y : Fin 3), x = 0 ∨ x = 1 → y = 1 ∨ y = 2 → ∀ z : Fin 3, y = 0 ∨ y = 1 → z = 1 ∨ z = 2) → x ≠ 1 → x = 2) by
          simpa [Semantics.Models, Satisfies];
        by_contra! hC;
        obtain ⟨x, hx, _, _⟩ := hC;
        have := hx 1 (by grind) (by grind) 0 (by grind);
        grind;

instance : Modal.S4Point2 ⪱ Modal.GrzPoint2 := calc
  Modal.S4Point2 ⪱ Modal.S4Point2McK := by infer_instance
  _              ⪱ Modal.GrzPoint2 := by infer_instance

end LO.Modal
end
