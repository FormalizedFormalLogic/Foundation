import Foundation.Modal.PLoN.Logic.N
import Foundation.Modal.Logic.SumNormal
import Foundation.Propositional.FMT.Logic
import Foundation.Propositional.Kripke.Logic.Cl

namespace LO

open LO.Entailment LO.Entailment.FiniteContext LO.Modal.Entailment
open Propositional

/--
  `gödelTranslate` but atom formulas are not boxed.
-/
@[match_pattern]
def Propositional.Formula.gödelWeakTranslate : Propositional.Formula α → Modal.Formula α
  | .atom a  => (.atom a)
  | ⊥ => ⊥
  | φ ⋏ ψ => (gödelWeakTranslate φ) ⋏ (gödelWeakTranslate ψ)
  | φ ⋎ ψ => (gödelWeakTranslate φ) ⋎ (gödelWeakTranslate ψ)
  | φ ➝ ψ => □((gödelWeakTranslate φ) ➝ (gödelWeakTranslate ψ))
postfix:90 "ᵍʷ" => Propositional.Formula.gödelWeakTranslate


namespace Modal

open Entailment
open Propositional.Formula (gödelWeakTranslate)

abbrev modelmodel.translate (M : PLoN.Model) : FMT.Model where
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

lemma modelmodel {M : PLoN.Model} {w : M.World} {φ : Propositional.Formula ℕ} :
  Propositional.Formula.FMT.Forces (M := modelmodel.translate M) (Sum.inr w) φ ↔ Formula.PLoN.Satisfies M w (φᵍʷ)  := by
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

  use modelmodel.translate M, .inr w;
  constructor;
  . tauto;
  . apply modelmodel.not.mpr hφ;

end Modal


end LO
