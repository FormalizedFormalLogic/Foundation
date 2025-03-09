import Foundation.Modal.ModalCompanion.Int
import Foundation.Modal.Logic.Sublogic.S4
import Foundation.Modal.Kripke.Hilbert.S4Point2

namespace LO.Propositional

def Substitution.toModal (s : Propositional.Substitution α) : Modal.Substitution (α) := λ x => (s x).toModalFormula
instance : Coe (Propositional.Substitution α) (Modal.Substitution α) := ⟨Substitution.toModal⟩

end LO.Propositional


namespace LO.Modal

open Entailment FiniteContext
open Propositional
open Propositional.Formula (goedelTranslate)
open Propositional.Formula (atom)
open Modal
open Modal.Kripke


open Formula.Kripke in
lemma Hilbert.S4Point2.goedelTranslated_axiomWLEM : Hilbert.S4Point2 ⊢! □(∼φᵍ) ⋎ □(∼□(∼φᵍ)) := by
  suffices Hilbert.S4Point2 ⊢! □(∼(□φᵍ)) ⋎ □(∼□(∼□(φᵍ))) by
    apply or_replace'! this;
    . apply axiomK'!;
      apply nec!;
      apply contra₀'!;
      exact Hilbert.goedelTranslated_axiomTc;
    . apply axiomK'!;
      apply nec!;
      apply contra₀'!;
      apply axiomK'!;
      apply nec!;
      apply contra₀'!;
      exact axiomT!
  apply Hilbert.S4Point2.Kripke.complete.complete;
  intro F ⟨F_refl, F_trans, F_conn⟩ V x;
  apply Formula.Kripke.Satisfies.or_def.mpr;
  by_contra hC;
  push_neg at hC;
  rcases hC with ⟨h₁, h₂⟩;

  replace h₁ := Formula.Kripke.Satisfies.dia_def.mp h₁;
  obtain ⟨y, Rxy, h₁⟩ := h₁;

  replace h₂ := Formula.Kripke.Satisfies.dia_def.mp h₂;
  obtain ⟨z, Rxz, h₂⟩ := h₂;

  obtain ⟨u, Ryu, Rzu⟩ := F_conn ⟨Rxy, Rxz⟩;

  have := Formula.Kripke.Satisfies.box_def.not.mp $ h₂ u Rzu;
  push_neg at this;
  obtain ⟨v, Ruv, h⟩ := this;

  have := h₁ v $ F_trans Ryu Ruv
  contradiction;

namespace Logic

open Formula.Kripke in
lemma mem_gAxiomPoint2_smallestMC_of_KC : (Axioms.Point2 (.atom 0)) ∈ Logic.KC.smallestMC := by
  have : □(∼□(.atom 0)) ⋎ □(∼□(∼□(.atom 0))) ∈ Logic.KC.smallestMC := by
    apply Logic.sumNormal.mem₂;
    use Axioms.WeakLEM (.atom 0);
    constructor;
    . simp;
    . simp [Axioms.WeakLEM, goedelTranslate]
      tauto;
  apply Propositional.Logic.smallestMC.mdp_S4 ?_ this;
  apply Hilbert.S4.Kripke.complete.complete;

  intro F ⟨F_refl, F_trans⟩ V x h₁ h₂ y Rxy;
  replace h₁ := Satisfies.or_def.mp h₁;
  replace h₂ := Satisfies.dia_def.mp h₂;
  obtain ⟨z, Rxz, h₂⟩ := h₂;

  rcases h₁ with (h₁ | h₁);
  . have := h₁ z Rxz;
    contradiction;
  . have := Satisfies.box_def.not.mp $ Satisfies.not_def.mp $ h₁ y Rxy
    push_neg at this;
    obtain ⟨u, Ryu, h⟩ := this;
    apply Satisfies.dia_def.mpr;
    use u;
    constructor;
    . assumption;
    . apply Satisfies.negneg_def.mp h u
      apply F_refl;

lemma S4Point2.is_smallestMC_of_KC : Logic.S4Point2 = Logic.KC.smallestMC := by
  ext φ;
  constructor;
  . intro hφ;
    induction hφ using Hilbert.Deduction.rec! with
    | maxm h =>
      rcases (by simpa using h) with (⟨s, rfl⟩ | ⟨s, rfl⟩ | ⟨s, rfl⟩ | ⟨s, rfl⟩);
      . apply Logic.sumNormal.mem₁; simp;
      . apply Logic.sumNormal.mem₁; simp;
      . apply Logic.sumNormal.mem₁; simp;
      . exact Logic.sumNormal.subst $ mem_gAxiomPoint2_smallestMC_of_KC;
    | mdp => apply Logic.sumNormal.mdp <;> assumption;
    | nec => apply Logic.sumNormal.nec; assumption;
    | _ => apply Logic.sumNormal.mem₁; simp;
  . intro hφ;
    induction hφ with
    | mem₁ h => apply Logic.S4_ssubset_S4Point2.1 h;
    | mdp hφ hψ ihφψ ihψ => apply Modal.Logic.mdp ihφψ ihψ;
    | subst h ih => apply Modal.Logic.subst ih;
    | nec h ih => apply Modal.Logic.nec ih;
    | mem₂ h =>
      rcases h with ⟨φ, hφ, rfl⟩;
      apply Hilbert.provable_goedelTranslated_of_provable Hilbert.KC Hilbert.S4Point2 ?_ (by trivial);
      rintro _ ⟨_, ⟨(rfl | rfl), ⟨s, rfl⟩⟩⟩;
      . apply Logic.S4_ssubset_S4Point2.1;
        apply modalCompanion_Int_S4.companion.mp;
        simp;
      . suffices Hilbert.S4Point2 ⊢! □(∼(s 0)ᵍ) ⋎ □(∼□(∼(s 0)ᵍ)) by simpa;
        exact Hilbert.S4Point2.goedelTranslated_axiomWLEM;

instance : ModalCompanion Logic.KC Logic.S4Point2 := by
  rw [Logic.S4Point2.is_smallestMC_of_KC];
  exact Modal.instModalCompanion_of_smallestMC_via_KripkeSemantics
    (IC := Kripke.FrameClass.confluent)
    (MC := Kripke.FrameClass.partial_confluent)
    (by
      intro φ;
      constructor;
      . apply Propositional.Hilbert.KC.Kripke.sound.sound;
      . apply Propositional.Hilbert.KC.Kripke.complete.complete;
    )
    (by
      rw [←Logic.S4Point2.is_smallestMC_of_KC];
      intro φ;
      constructor;
      . apply Modal.Hilbert.S4Point2.Kripke.sound.sound;
      . apply Modal.Hilbert.S4Point2.Kripke.complete.complete;
    )
    (by
      rintro F hF;
      refine ⟨F.rel_refl, F.rel_trans, hF⟩;
    );


end Logic


end LO.Modal
