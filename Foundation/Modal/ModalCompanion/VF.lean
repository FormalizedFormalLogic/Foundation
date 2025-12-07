import Foundation.Modal.PLoN.Logic.N
import Foundation.Modal.Logic.SumNormal
import Foundation.Propositional.FMT.Logic
import Foundation.Propositional.Kripke.Logic.Cl

namespace LO

open LO.Entailment LO.Entailment.FiniteContext LO.Modal.Entailment
open Propositional

namespace Modal.Formula

@[grind .] lemma neq_and_or {φ ψ χ ξ : Formula α} : φ ⋏ ψ ≠ χ ⋎ ξ := by rw [←Formula.or_eq, ←Formula.and_eq]; simp;
@[grind .] lemma neq_or_and {φ ψ χ ξ : Formula α} : φ ⋎ ψ ≠ χ ⋏ ξ := by rw [←Formula.and_eq, ←Formula.or_eq]; simp;

end Modal.Formula


namespace Propositional.Formula

/--
  `gödelTranslate` but atom formulas are not boxed.
-/
@[grind, match_pattern]
def gödelWeakTranslate : Propositional.Formula α → Modal.Formula α
  | #a  => (.atom a)
  | ⊥ => ⊥
  | φ ⋏ ψ => (φ.gödelWeakTranslate) ⋏ (ψ.gödelWeakTranslate)
  | φ ⋎ ψ => (φ.gödelWeakTranslate) ⋎ (ψ.gödelWeakTranslate)
  | φ ➝ ψ => □((φ.gödelWeakTranslate) ➝ (ψ.gödelWeakTranslate))
postfix:90 "ᵍʷ" => Propositional.Formula.gödelWeakTranslate

@[grind .]
lemma gödelWeakTranslate.injective : Function.Injective (gödelWeakTranslate (α := α)) := by
  intro φ ψ h;
  match φ, ψ with
  | #a, #b => grind
  | ⊥, ⊥ => rfl
  | φ₁ ⋏ φ₂, ψ₁ ⋏ ψ₂ | φ₁ ⋎ φ₂, ψ₁ ⋎ ψ₂ | φ₁ ➝ φ₂, ψ₁ ➝ ψ₂ =>
    suffices φ₁ = ψ₁ ∧ φ₂ = ψ₂ by simpa;
    have ⟨h₁, h₂⟩ : φ₁ᵍʷ = ψ₁ᵍʷ ∧ φ₂ᵍʷ = ψ₂ᵍʷ := by simpa [gödelWeakTranslate] using h;
    constructor;
    . apply gödelWeakTranslate.injective h₁;
    . apply gödelWeakTranslate.injective h₂;
  | #a, ⊥ | #a, φ₁ ⋏ φ₂ | #a, φ₁ ⋎ φ₂ | #a, φ₁ ➝ φ₂
  | ⊥, #a | ⊥, φ₁ ⋏ φ₂ | ⊥, φ₁ ⋎ φ₂ | ⊥, φ₁ ➝ φ₂
  | φ₁ ⋏ φ₂, #a | φ₁ ⋏ φ₂, ⊥
  | φ₁ ⋎ φ₂, #a | φ₁ ⋎ φ₂, ⊥
  | φ₁ ➝ φ₂, #a | φ₁ ➝ φ₂, ⊥ => contradiction;
  | φ₁ ⋏ φ₂, ψ₁ ⋎ ψ₂ => exfalso; apply Modal.Formula.neq_and_or h;
  | φ₁ ⋎ φ₂, ψ₁ ⋏ ψ₂ => exfalso; apply Modal.Formula.neq_or_and h;

end Propositional.Formula


namespace Modal

open Entailment
open Propositional.Formula (gödelWeakTranslate)

abbrev PLoN.FMT_bridge.translate (M : PLoN.Model) : FMT.Model where
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

lemma PLoN.FMT_bridge {M : PLoN.Model} {w : M.World} {φ : Propositional.Formula ℕ} :
  Propositional.Formula.FMT.Forces (M := FMT_bridge.translate M) (Sum.inr w) φ ↔ Formula.PLoN.Satisfies M w (φᵍʷ)  := by
  induction φ using Propositional.Formula.rec' generalizing w with
  | himp φ ψ ihφ ihψ =>
    dsimp [Formula.PLoN.Satisfies];
    constructor;
    . grind;
    . intro h x Rwx hxφ;
      match x with
      | .inl () => grind;
      | .inr x => grind;
  | _ => dsimp [Formula.PLoN.Satisfies]; grind;

lemma provable_gödelWeakTranslated_of_provable_VF : Propositional.VF ⊢ φ → Modal.N ⊢ φᵍʷ := by
  contrapose!;
  intro h;
  apply Propositional.VF.FMT.sound.not_provable_of_countermodel;
  apply Propositional.FMT.not_validOnFrameClass_of_exists_model_world;

  obtain ⟨M, _, hφ⟩ := Modal.Formula.PLoN.ValidOnFrameClass.iff_not_exists_model.mp $ Modal.N.PLoN.complete.exists_countermodel_of_not_provable h;
  simp only [Formula.PLoN.ValidOnModel.iff_models, Formula.PLoN.ValidOnModel, Formula.PLoN.Satisfies.iff_models, not_forall] at hφ;
  obtain ⟨w, hφ⟩ := hφ;

  clear h;

  use PLoN.FMT_bridge.translate M, .inr w;
  constructor;
  . tauto;
  . apply PLoN.FMT_bridge.not.mpr hφ;


abbrev provable_VF_of_provable_gödelWeakTranslated.lemma1.translate (M : FMT.Model) : PLoN.Model where
  World := M.World
  Rel φ x y :=
    match φ with
    | ψ ➝ χ => ∃ ψ' χ', ψ'ᵍʷ = ψ ∧ χ'ᵍʷ = χ ∧ M.Rel' (ψ' ➝ χ') x y
    | _     => True
  Valuation x a := M.Val x a


lemma provable_VF_of_provable_gödelWeakTranslated.lemma1 {M : FMT.Model} {w : M.World} {φ : Propositional.Formula ℕ} :
  Formula.PLoN.Satisfies (M := lemma1.translate M) w (φᵍʷ) ↔ Propositional.Formula.FMT.Forces (M := M) w φ := by
  induction φ using Propositional.Formula.rec' generalizing w with
  | himp φ ψ ihφ ihψ =>
    dsimp [Formula.PLoN.Satisfies];
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
  | _ => dsimp [Formula.PLoN.Satisfies]; grind;

open provable_VF_of_provable_gödelWeakTranslated in
lemma provable_VF_of_provable_gödelWeakTranslated : Modal.N ⊢ φᵍʷ → Propositional.VF ⊢ φ := by
  contrapose!;
  intro h;
  apply Modal.N.PLoN.sound.not_provable_of_countermodel;
  apply Modal.Formula.PLoN.ValidOnFrameClass.not_of_exists_model_world;
  obtain ⟨M, x, _, H⟩ := Propositional.FMT.exists_model_world_of_not_validOnFrameClass $ Propositional.VF.FMT.complete.exists_countermodel_of_not_provable h;
  clear h;
  use lemma1.translate M;
  constructor;
  . tauto;
  . use x;
    apply lemma1.not.mpr H;

end Modal


end LO
