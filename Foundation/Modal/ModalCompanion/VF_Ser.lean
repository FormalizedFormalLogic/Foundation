import Foundation.Modal.ModalCompanion.VF

namespace LO.Modal

open Entailment
open Propositional.Formula (gödelWeakTranslate)

section

namespace PLoN

protected class Frame.NP (F : Frame) where
  P_serial : ∀ x : F, ∃ y, x ≺[⊥] y

protected abbrev FrameClass.NP : PLoN.FrameClass := { F | Frame.NP F }

end PLoN

namespace NP.PLoN

axiom sound : Sound (Modal.NP) PLoN.FrameClass.NP
axiom complete : Complete (Modal.NP) PLoN.FrameClass.NP

end NP.PLoN

end




variable {φ : Propositional.Formula ℕ}

protected abbrev provable_gödelWeakTranslated_of_provable_VF_Ser.lemma.translate (M : PLoN.Model) : Propositional.FMT.Model where
  World := Unit ⊕ M.World
  Rel φ x y :=
    match x, y, φ with
    | .inr x, .inr y, φ ➝ ψ => M.Rel (φᵍʷ ➝ ψᵍʷ) x y
    | .inr _, .inl (), _ => False
    | _, _, _ => True
  root := .inl ()
  rooted := by grind
  Val x a :=
    match x with
    | .inl () => True
    | .inr x => M.Valuation x a

lemma provable_gödelWeakTranslated_of_provable_VF_Ser.lemma {M : PLoN.Model} {w : M.World} {φ : Propositional.Formula ℕ} :
  Propositional.Formula.FMT.Forces (M := lemma.translate M) (Sum.inr w) φ ↔ Modal.Formula.PLoN.Forces w (φᵍʷ)  := by
  induction φ using Propositional.Formula.rec' generalizing w with
  | himp φ ψ ihφ ihψ =>
    dsimp [Formula.PLoN.Forces];
    constructor;
    . grind;
    . intro h x Rwx hxφ;
      match x with
      | .inl () => grind;
      | .inr x => grind;
  | _ => dsimp [Formula.PLoN.Forces]; grind;

open provable_gödelWeakTranslated_of_provable_VF_Ser in
lemma provable_gödelWeakTranslated_of_provable_VF_Ser : Propositional.VF_Ser ⊢ φ → Modal.NP ⊢ φᵍʷ := by
  contrapose!;
  intro h;
  apply Propositional.VF_Ser.FMT.sound.not_provable_of_countermodel;
  apply Propositional.FMT.not_validOnFrameClass_of_exists_model_world;
  obtain ⟨M, w, _, hφ⟩ := Modal.PLoN.exists_model_world_of_not_validOnFrameClass $ Modal.NP.PLoN.complete.exists_countermodel_of_not_provable h;
  use lemma.translate M, .inr w;
  constructor;
  . simp only [Set.mem_setOf_eq];
    exact {
      dnf_serial := by
        intro x;
        use x;
        match x with
        | .inl () => simp [Propositional.FMT.Frame.Rel'];
        | .inr x =>
          simp [Propositional.FMT.Frame.Rel', Propositional.Formula.gödelWeakTranslate];
          sorry;
    }
  . apply lemma.not.mpr hφ;


protected abbrev provable_VF_Ser_of_provable_gödelWeakTranslated.lemma.translate (M : Propositional.FMT.Model) : PLoN.Model where
  World := M.World
  Rel φ x y :=
    match φ with
    | ψ ➝ χ => ∃ ψ' χ', ψ'ᵍʷ = ψ ∧ χ'ᵍʷ = χ ∧ M.Rel' (ψ' ➝ χ') x y
    | _     => True
  Valuation x a := M.Val x a

lemma provable_VF_Ser_of_provable_gödelWeakTranslated.lemma {M : Propositional.FMT.Model} {w : M.World} {φ : Propositional.Formula ℕ} :
  Formula.PLoN.Forces (M := lemma.translate M) w (φᵍʷ) ↔ Propositional.Formula.FMT.Forces (M := M) w φ := by
  induction φ using Propositional.Formula.rec' generalizing w with
  | himp φ ψ ihφ ihψ =>
    dsimp [Formula.PLoN.Forces];
    constructor;
    . intro H x Rwx h;
      apply ihψ.mp;
      apply H;
      . use φ, ψ;
      . apply ihφ.mpr;
        assumption;
    . intro H x Rwx h;
      apply ihψ.mpr;
      apply H;
      . obtain ⟨φ', ψ', heqφ, heqψ, Rwx⟩ := Rwx;
        replace heqφ := Propositional.Formula.gödelWeakTranslate.injective heqφ;
        replace heqψ := Propositional.Formula.gödelWeakTranslate.injective heqψ;
        grind;
      . apply ihφ.mp;
        assumption;
  | _ => dsimp [Formula.PLoN.Forces]; grind;

open provable_VF_Ser_of_provable_gödelWeakTranslated in
lemma provable_VF_Ser_of_provable_gödelWeakTranslated : Modal.NP ⊢ φᵍʷ → Propositional.VF_Ser ⊢ φ := by
  contrapose!;
  intro h;
  obtain ⟨M, x, _, H⟩ := Propositional.FMT.exists_model_world_of_not_validOnFrameClass $ Propositional.VF_Ser.FMT.complete.exists_countermodel_of_not_provable h;
  apply Modal.NP.PLoN.sound.not_provable_of_countermodel;
  apply Modal.PLoN.not_validOnFrameClass_of_exists_model_world;
  use lemma.translate M, x;
  constructor;
  . tauto;
  . apply lemma.not.mpr H;


theorem iff_provable_VF_Ser_provable_gödelWeakTranslated : Propositional.VF_Ser ⊢ φ ↔ Modal.NP ⊢ φᵍʷ := by
  constructor;
  . apply provable_gödelWeakTranslated_of_provable_VF_Ser;
  . apply provable_VF_Ser_of_provable_gödelWeakTranslated;

end LO.Modal
