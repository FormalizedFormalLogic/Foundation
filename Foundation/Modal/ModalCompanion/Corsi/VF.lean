module

public import Foundation.Modal.PLoN.Logic.N
public import Foundation.Modal.Logic.SumNormal
public import Foundation.Propositional.FMT.Logic
public import Foundation.Propositional.Kripke.Logic.Cl

@[expose] public section

namespace LO

open LO.Entailment LO.Entailment.FiniteContext LO.Modal.Entailment
open Propositional


namespace Modal.Formula

@[grind .] lemma neq_and_or {φ ψ χ ξ : Formula α} : φ ⋏ ψ ≠ χ ⋎ ξ := by rw [Formula.or_eq, Formula.and_eq]; simp;
@[grind .] lemma neq_or_and {φ ψ χ ξ : Formula α} : φ ⋎ ψ ≠ χ ⋏ ξ := by rw [Formula.and_eq, Formula.or_eq]; simp;

end Modal.Formula


namespace Modal

namespace PLoN

protected class Frame.NP (F : Frame) where
  P_serial : ∀ x : F, ∃ y, x ≺[⊥] y

protected abbrev FrameClass.NP : PLoN.FrameClass := { F | Frame.NP F }

end PLoN


namespace NP.PLoN

axiom sound : Sound Modal.NP PLoN.FrameClass.NP
axiom complete : Complete Modal.NP PLoN.FrameClass.NP

end NP.PLoN


end Modal


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
postfix:90 "ᶜ" => Propositional.Formula.gödelWeakTranslate

@[grind .]
lemma gödelWeakTranslate.injective : Function.Injective (gödelWeakTranslate (α := α)) := by
  intro φ ψ h;
  match φ, ψ with
  | #a, #b => grind
  | ⊥, ⊥ => rfl
  | φ₁ ⋏ φ₂, ψ₁ ⋏ ψ₂ =>
    obtain ⟨h₁, h₂⟩ := Modal.Formula.inj_and.mp h;
    simp [gödelWeakTranslate.injective h₁, gödelWeakTranslate.injective h₂];
  | φ₁ ⋎ φ₂, ψ₁ ⋎ ψ₂ =>
    obtain ⟨h₁, h₂⟩ := Modal.Formula.inj_or.mp h;
    simp [gödelWeakTranslate.injective h₁, gödelWeakTranslate.injective h₂];
  | φ₁ ➝ φ₂, ψ₁ ➝ ψ₂ =>
    dsimp [gödelWeakTranslate] at h;
    obtain ⟨h₁, h₂⟩ := Modal.Formula.inj_imp.mp $ Modal.Formula.inj_box.mp h;
    simp [gödelWeakTranslate.injective h₁, gödelWeakTranslate.injective h₂];
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

protected abbrev provable_gödelWeakTranslated_of_provable_VF.lemma.translate (M : PLoN.Model) : FMT.Model where
  World := Unit ⊕ M.World
  Rel φ x y :=
    match x, y, φ with
    | .inr x, .inr y, φ ➝ ψ => M.Rel (φᶜ ➝ ψᶜ) x y
    | .inr _, .inl (), _ => False
    | _, _, _ => True
  root := .inl ()
  rooted := by grind
  Val x a :=
    match x with
    | .inl () => True
    | .inr x => M.Valuation x a

lemma provable_gödelWeakTranslated_of_provable_VF.lemma {M : PLoN.Model} {w : M.World} {φ : Propositional.Formula ℕ} :
  Propositional.Formula.FMT.Forces (M := lemma.translate M) (Sum.inr w) φ ↔ Modal.Formula.PLoN.Forces w (φᶜ)  := by
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

open provable_gödelWeakTranslated_of_provable_VF in
lemma provable_gödelWeakTranslated_of_provable_VF : Propositional.VF ⊢ φ → Modal.N ⊢ φᶜ := by
  contrapose!;
  intro h;
  apply Propositional.VF.FMT.sound.not_provable_of_countermodel;
  apply Propositional.FMT.not_validOnFrameClass_of_exists_model_world;
  obtain ⟨M, w, _, hφ⟩ := Modal.PLoN.exists_model_world_of_not_validOnFrameClass $ Modal.N.PLoN.complete.exists_countermodel_of_not_provable h;
  use lemma.translate M, .inr w;
  constructor;
  . tauto;
  . apply lemma.not.mpr hφ;


protected abbrev provable_VF_of_provable_gödelWeakTranslated.lemma.translate (M : FMT.Model) : PLoN.Model where
  World := M.World
  Rel φ x y :=
    match φ with
    | ψ ➝ χ => ∃ ψ' χ', ψ'ᶜ = ψ ∧ χ'ᶜ = χ ∧ M.Rel' (ψ' ➝ χ') x y
    | _     => True
  Valuation x a := M.Val x a

lemma provable_VF_of_provable_gödelWeakTranslated.lemma {M : FMT.Model} {w : M.World} {φ : Propositional.Formula ℕ} :
  Formula.PLoN.Forces (M := lemma.translate M) w (φᶜ) ↔ Propositional.Formula.FMT.Forces (M := M) w φ := by
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

open provable_VF_of_provable_gödelWeakTranslated in
lemma provable_VF_Ser_of_provable_gödelWeakTranslated : Modal.NP ⊢ φᶜ → Propositional.VF ⊢ φ := by
  contrapose!;
  intro h;
  obtain ⟨M, x, _, H⟩ := Propositional.FMT.exists_model_world_of_not_validOnFrameClass $ Propositional.VF.FMT.complete.exists_countermodel_of_not_provable h;
  apply Modal.NP.PLoN.sound.not_provable_of_countermodel;
  apply Modal.PLoN.not_validOnFrameClass_of_exists_model_world;
  use lemma.translate M, x;
  constructor;
  . tauto;
  . apply lemma.not.mpr H;

lemma VF_modal_companion_TFAE : [
  Propositional.VF ⊢ φ,
  Modal.N ⊢ φᶜ,
  Modal.NP ⊢ φᶜ
].TFAE := by
  tfae_have 1 → 2 := provable_gödelWeakTranslated_of_provable_VF
  tfae_have 2 → 3 := Hilbert.Normal.weakerThan_of_subset_axioms (by tauto) |>.wk
  tfae_have 3 → 1 := provable_VF_Ser_of_provable_gödelWeakTranslated
  tfae_finish

end Modal

end LO
end
