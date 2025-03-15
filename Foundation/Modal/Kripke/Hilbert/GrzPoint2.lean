import Foundation.Modal.Kripke.Hilbert.Grz.Completeness
import Foundation.Modal.Kripke.Hilbert.S4Point2
import Mathlib.Data.Finite.Sum

namespace LO.Modal

open Entailment
open Entailment.Context
open Formula
open Formula.Kripke
open Hilbert.Kripke
open Kripke

namespace Formula

variable {α} [DecidableEq α]
variable {φ : Formula α} {a : α}

def atoms : Formula α → Finset α
  | ⊥ => ∅
  | .atom v => {v}
  | □φ => φ.atoms
  | φ ➝ ψ => φ.atoms ∪ ψ.atoms

lemma iff_mem_atoms_mem_subformula : (a ∈ φ.atoms) ↔ (atom a ∈ φ.subformulas) := by
  induction φ using Formula.rec' <;> simp_all [atoms, subformulas];

end Formula


section

namespace Kripke

def Frame.terminals (F : Frame) : Set F.World := { t | ∀ {y}, t ≺ y → y = t }
def Frame.terminals_of (F : Frame) (x : F.World) : Set F.World := { t | x ≺^+ t ∧ ∀ {y}, t ≺ y → y = t }

end Kripke

namespace Formula.Kripke.Satisfies

variable {F V} {φ : Formula ℕ}

lemma box_at_terminal {x : F.World} (hx : x ∈ F.terminals) (h : Satisfies ⟨F, V⟩ x φ) : Satisfies ⟨F, V⟩ x (□φ) := by
  intro y Rxy;
  have := hx Rxy;
  subst this;
  exact h;

lemma dia_at_terminal {x : F.World} (hx : x ∈ F.terminals) (h :  ¬Satisfies ⟨F, V⟩ x φ) : ¬Satisfies ⟨F, V⟩ x (◇φ) := by
  simp [Satisfies, Frame.terminals, not_exists, Set.mem_setOf_eq, Satisfies] at hx ⊢;
  intro y Rxy;
  have := hx Rxy;
  subst this;
  exact h;

end Formula.Kripke.Satisfies

end


section

namespace Hilbert

open Entailment

lemma Grz_weakerThan_GrzPoint2 : Hilbert.Grz ⪯ Hilbert.GrzPoint2 := weakerThan_of_dominate_axioms $ by simp;

lemma GrzPoint2_of_Grz (h : (φ.atoms.image (λ a => Axioms.Point2 (.atom a))).toSet *⊢[Hilbert.Grz]! φ) : Hilbert.GrzPoint2 ⊢! φ := by
  obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp h;
  simp at hΓ₁;
  replace hΓ₂ := Grz_weakerThan_GrzPoint2.pbl $ FiniteContext.provable_iff.mp hΓ₂;
  exact hΓ₂ ⨀ by
    apply conj_intro'!;
    intro γ hγ;
    obtain ⟨a, ha, rfl⟩ := hΓ₁ _ hγ;
    exact axiomPoint2!;

lemma not_Grz_of_not_GrzPoint2 (h : Hilbert.GrzPoint2 ⊬ φ) : (φ.atoms.image (λ a => Axioms.Point2 (.atom a))).toList ⊬[Hilbert.Grz] φ := by
  have := provable_iff.not.mp $ not_imp_not.mpr GrzPoint2_of_Grz h;
  push_neg at this;
  convert this ((φ.atoms.image (λ a => Axioms.Point2 (.atom a))).toList) $ by simp;

end Hilbert

end


namespace Kripke

abbrev FrameClass.finite_confluent_partial_order : FrameClass := { F | F.IsFinite ∧ IsPartialOrder _ F.Rel ∧ IsConfluent _ F.Rel }

end Kripke


namespace Hilbert.GrzPoint2.Kripke

instance finite_sound : Sound (Hilbert.GrzPoint2) FrameClass.finite_confluent_partial_order := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _, _⟩ _ (rfl | rfl);
  . exact validate_AxiomGrz_of_finite_strict_preorder;
  . exact validate_AxiomPoint2_of_confluent;

instance consistent : Entailment.Consistent (Hilbert.GrzPoint2) :=
  consistent_of_sound_frameclass FrameClass.finite_confluent_partial_order $ by
    use whitepoint;
    refine ⟨inferInstance, inferInstance, inferInstance⟩;


section

open Relation

instance finite_complete : Complete (Hilbert.GrzPoint2) FrameClass.finite_confluent_partial_order := ⟨by
  intro φ;
  contrapose;
  intro hφ;

  replace hφ : Hilbert.Grz ⊬ ⋀((φ.atoms.image (λ a => Axioms.Point2 (atom a))).toList) ➝ φ := not_Grz_of_not_GrzPoint2 hφ;
  generalize eΓ : (φ.atoms.image (λ a => Axioms.Point2 (atom a))).toList = Γ at hφ;
  obtain ⟨M, r, ⟨_, M_refl, M_trans, M_antisymm⟩, hΓφ⟩ := exists_model_world_of_not_validOnFrameClass $ not_imp_not.mpr (@Hilbert.Grz.Kripke.complete.complete _) hφ;

  clear hφ;

  let RM := M↾r;
  let r' : RM.World := ⟨r, by tauto⟩;
  have RM_rooted : ∀ (w : RM.World), r' ≺ w := by
    intro w;
    by_cases e : r' = w;
    . subst e; apply Frame.pointGenerate.rel_refl M_refl;
    . exact TransGen.unwrap (Frame.pointGenerate.rel_trans M_trans) (Frame.IsRooted.root_generates w (by tauto));

  replace hΓφ : ¬(r' ⊧ ⋀Γ → r' ⊧ φ) := Satisfies.imp_def.not.mp $ Model.pointGenerate.modal_equivalent_at_root (r := r) |>.not.mpr hΓφ;
  push_neg at hΓφ;
  obtain ⟨hΓ, hφ⟩ := hΓφ;

  let M' : Kripke.Model := {
    World := RM.World ⊕ Unit
    Rel x y :=
      match x, y with
      | _, (Sum.inr _) => True
      | (Sum.inl x), (Sum.inl y) => RM.Rel x y
      | _, _ => False
    Val x a :=
      match x with
      | Sum.inl x => RM.Val x a
      | _ => ∀ y ∈ RM.toFrame.terminals, RM.Val y a
  };
  apply not_validOnFrameClass_of_exists_model_world;
  use M', (Sum.inl r');
  constructor;
  . refine ⟨?_, ?_, ?_, ?_, ?_⟩;
    . apply Frame.isFinite_iff _ |>.mpr;
      infer_instance;
    . intro x;
      match x with
      | Sum.inl x => apply M_refl;
      | Sum.inr x => simp_all [M'];
    . intro x y z Rxy Ryz;
      match x, y, z with
      | Sum.inl x, Sum.inl y, Sum.inl z => exact Frame.pointGenerate.rel_trans M_trans Rxy Ryz;
      | _, _, Sum.inr z => simp_all [M'];
      | _, Sum.inr y, Sum.inl z => simp_all [M'];
    . intro x y Rxy Ryz;
      match x, y with
      | Sum.inl x, Sum.inl y =>
        simp only [Sum.inl.injEq, M'];
        exact Frame.pointGenerate.rel_antisymm M_antisymm Rxy Ryz;
      | Sum.inl x, Sum.inr y => simp_all [M'];
      | Sum.inr x, Sum.inr y => simp_all [M'];
      | Sum.inr x, Sum.inl y => simp_all [M'];
    . rintro x y z ⟨Rxy, Ryz⟩;
      use (Sum.inr ());
      simp [M'];
  . have H₁ : ∀ a ∈ φ.atoms, ∀ t ∈ RM.toFrame.terminals, ∀ t' ∈ RM.toFrame.terminals, RM t a → RM t' a := by
      intro a ha t t_terminal t' t'_terminal hy;
      by_contra hy';
      have : ¬t' ⊧ (◇atom a) := Kripke.Satisfies.dia_at_terminal t'_terminal hy';
      have : ¬r' ⊧ □(◇atom a) := by
        apply Satisfies.box_def.not.mpr;
        push_neg;
        use t';
        constructor;
        . apply RM_rooted;
        . assumption;
      have : ¬r' ⊧ ◇(□atom a) := by
        revert this;
        apply not_imp_not.mpr
        exact Satisfies.conj_def.mp hΓ (Axioms.Point2 (atom a)) (by simpa [←eΓ]);
      have := Satisfies.dia_def.not.mp this;
      push_neg at this;
      have : ¬t ⊧ □atom a := this t (RM_rooted t);
      have : t ⊧ □atom a := Kripke.Satisfies.box_at_terminal t_terminal hy;
      contradiction;
    have H₂ : ∀ t ∈ RM.terminals, ∀ ψ ∈ φ.subformulas, t ⊧ ψ ↔ (Satisfies M' (Sum.inr ()) ψ) := by
      intro t t_terminal ψ ψ_sub;
      induction ψ using Formula.rec' with
      | hatom a =>
        simp [Satisfies, M']
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
          apply ihξ (Formula.subformulas.mem_imp₂ ψ_sub) |>.mp;
          apply h;
          apply ihχ (Formula.subformulas.mem_imp₁ ψ_sub) |>.mpr;
          assumption;
        . intro h hχ;
          apply ihξ (Formula.subformulas.mem_imp₂ ψ_sub) |>.mpr;
          apply h;
          apply ihχ (Formula.subformulas.mem_imp₁ ψ_sub) |>.mp;
          assumption;
      | hbox ψ ihψ =>
        constructor;
        . intro ht u Ru;
          match u with
          | Sum.inl x => simp [M', Frame.Rel'] at Ru;
          | Sum.inr _ =>
            apply ihψ (Formula.subformulas.mem_box ψ_sub) |>.mp;
            apply ht;
            apply Frame.pointGenerate.rel_refl M_refl;
        . intro ht u Rtu;
          have := t_terminal Rtu; subst this;
          apply ihψ (Formula.subformulas.mem_box ψ_sub) |>.mpr;
          apply ht;
          tauto;
    have : ∀ y : RM.World, ∀ ψ ∈ φ.subformulas, y ⊧ ψ ↔ (Satisfies M' (Sum.inl y) ψ) := by
      intro y ψ ψ_sub;
      induction ψ using Formula.rec' generalizing y with
      | hbox ψ ihψ =>
        constructor;
        . intro hψ v Ruv;
          match v with
          | Sum.inl x =>
            simp [M', Frame.Rel'] at Ruv;
            exact ihψ x (Formula.subformulas.mem_box ψ_sub) |>.mp $ hψ _ Ruv;
          | Sum.inr x =>
            obtain ⟨t, t_terminal, Rut⟩ : ∃ t ∈ RM.terminals, y ≺ t := by sorry
              /-
              by_contra hC;
              push_neg at hC;
              simp [Frame.terminals] at hC;
              by_cases y_terminal : y ∈ RM.terminals;
              . exact hC y y_terminal $ Frame.pointGenerate.rel_refl M_refl y;
              . simp [Frame.terminals] at y_terminal;
                obtain ⟨z, Ryz, eyz⟩ := y_terminal;
                by_cases z_terminal : z ∈ RM.terminals;
                . exact hC z z_terminal Ryz;
                . simp [Frame.terminals] at z_terminal;
                  obtain ⟨w, Rzw, ewz⟩ := z_terminal;
                  have ewy : w ≠ y := by
                    by_contra ewy; subst ewy;
                    have := Frame.pointGenerate.rel_antisymm M_antisymm Rzw Ryz;
                    contradiction;
                  -- by similar arguments, arbitary n-poinst in RM, but FM is finite. it contradicts.
              -/
            apply H₂ t t_terminal ψ (Formula.subformulas.mem_box ψ_sub) |>.mp;
            apply hψ;
            exact Rut;
        . intro h v Ruv;
          exact ihψ v (Formula.subformulas.mem_box ψ_sub) |>.mpr $ @h (Sum.inl v) Ruv;
      | himp _ _ ihχ ihξ =>
        have := ihχ y (Formula.subformulas.mem_imp₁ ψ_sub);
        have := ihξ y (Formula.subformulas.mem_imp₂ ψ_sub);
        tauto;
      | _ => tauto;
    exact this r' φ (by simp) |>.not.mp hφ;
⟩

end

end Hilbert.GrzPoint2.Kripke

end LO.Modal
