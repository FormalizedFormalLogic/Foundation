import Foundation.Modal.ModalCompanion.Int
import Foundation.Modal.Kripke.Logic.S5Grz
import Foundation.Modal.Boxdot.Ver_Triv
import Foundation.Propositional.Kripke.Logic.Cl

namespace LO

namespace Propositional

open LO.Entailment LO.Entailment.FiniteContext LO.Modal.Entailment
open Formula.Kripke
open Modal
open Modal.Kripke
open Propositional
open Propositional.Formula (atom)
open Propositional.Formula (goedelTranslate)

lemma Logic.Cl.smallestMC.mem_diabox_box : (◇□(.atom 0) ➝ □(.atom 0)) ∈ Logic.Cl.smallestMC := by
  have : □(.atom 0) ⋎ □(∼□(.atom 0)) ∈ Logic.Cl.smallestMC := by
    apply Logic.sumNormal.mem₂;
    use Axioms.LEM (.atom 0);
    constructor;
    . simp;
    . tauto;
  apply Propositional.Logic.smallestMC.mdp_S4 ?_ this;
  apply C!_trans ?_ CANC!;
  apply C!_trans ?_ or_comm!;
  apply CAA!_of_C!_of_C!;
  . simp;
  . apply CN!_of_CN!_right;
    exact diaDuality_mp!;

lemma Logic.Cl.smallestMC.mem_AxiomFive : (◇(.atom 0) ➝ □◇(.atom 0)) ∈ Logic.Cl.smallestMC := by
  have := Logic.sumNormal.subst (s := λ _ => ∼(.atom 0)) $ mem_diabox_box;
  apply Propositional.Logic.smallestMC.mdp_S4 ?_ this;
  apply C!_trans ?_ CANC!;
  apply C!_trans CCAN! ?_;
  apply C!_trans ?_ or_comm!;
  apply CAA!_of_C!_of_C!;
  . apply CN!_of_CN!_left;
    exact diaDuality_mp!;
  . apply CN!_of_CN!_right;
    exact diaDuality_mp!;

end Propositional


namespace Modal

open LO.Entailment LO.Entailment.FiniteContext LO.Modal.Entailment
open Propositional
open Propositional.Formula (goedelTranslate)
open Propositional.Formula (atom)
open Modal
open Modal.Kripke

section S5

namespace Logic

lemma S5.is_smallestMC_of_Cl : Logic.S5 = Logic.Cl.smallestMC := by
  ext φ;
  constructor;
  . intro hφ;
    induction hφ using Hilbert.Deduction.rec! with
    | maxm h =>
      rcases (by simpa using h) with (⟨s, rfl⟩ | ⟨s, rfl⟩ | ⟨s, rfl⟩);
      . apply Logic.sumNormal.mem₁; simp;
      . apply Logic.sumNormal.mem₁; simp;
      . exact Logic.sumNormal.subst (s := λ _ => s 0) $ Logic.Cl.smallestMC.mem_AxiomFive;
    | mdp => apply Logic.sumNormal.mdp <;> assumption;
    | nec => apply Logic.sumNormal.nec; assumption;
    | _ => apply Logic.sumNormal.mem₁; simp;
  . intro hφ;
    induction hφ with
    | mdp hφ hψ ihφψ ihψ => apply Modal.Logic.mdp ihφψ ihψ;
    | subst h ih => apply Modal.Logic.subst ih;
    | nec h ih => apply Modal.Logic.nec ih;
    | mem₁ h => apply Logic.S5.proper_extension_of_S4.subset h;
    | mem₂ h =>
      rcases h with ⟨φ, hφ, rfl⟩;
      haveI : Hilbert.S4 ⊢! ◇φᵍ := iff_provable_Cl_provable_dia_gS4.mp hφ;
      haveI : Hilbert.S4 ⊢! ◇□φᵍ := (diaK'! $ Hilbert.goedelTranslated_axiomTc) ⨀ this;
      apply rm_diabox'!;
      apply S5.proper_extension_of_S4.subset this;

instance modalCompanion_Cl_S5 : ModalCompanion Logic.Cl Logic.S5 := by
  rw [Logic.S5.is_smallestMC_of_Cl];
  exact Modal.instModalCompanion_of_smallestMC_via_KripkeSemantics
    (IC := Propositional.Kripke.FrameClass.euclidean)
    (MC := Modal.Kripke.FrameClass.refl_eucl)
    (by rw [Propositional.Logic.Cl.Kripke.euclidean])
    (by rw [←Logic.S5.is_smallestMC_of_Cl, ←Logic.S5.Kripke.refl_eucl])
    (by
      simp;
      intro F hF;
      constructor;
      . infer_instance;
      . infer_instance;
    );

end Logic

end S5


section S5Grz

lemma Logic.gS5Grz_of_Cl : φ ∈ Logic.Cl → φᵍ ∈ Logic.S5Grz := by
  intro h;
  apply S5Grz.proper_extension_of_S5.subset;
  exact modalCompanion_Cl_S5.companion.mp h;

lemma Logic.S5Grz.is_largestMC_of_Cl : Logic.S5Grz = Logic.Cl.largestMC := by
  ext φ;
  constructor;
  . intro hφ;
    induction hφ using Hilbert.Deduction.rec! with
    | maxm h =>
      simp at h;
      rcases h with (⟨s, rfl⟩ | ⟨s, rfl⟩ | ⟨s, rfl⟩ | ⟨s, rfl⟩);
      . apply Logic.sumNormal.mem₁;
        apply Logic.sumNormal.mem₁;
        simp;
      . apply Logic.sumNormal.mem₁;
        apply Logic.sumNormal.mem₁;
        simp;
      . apply Logic.sumNormal.subst (φ := ◇(.atom 0) ➝ □◇(.atom 0)) (s := s);
        apply Logic.sumNormal.mem₁;
        exact Logic.Cl.smallestMC.mem_AxiomFive;
      . apply Logic.sumNormal.subst (φ := □(□((.atom 0) ➝ □(.atom 0)) ➝ (.atom 0)) ➝ (.atom 0)) (s := s);
        apply Logic.sumNormal.mem₂;
        simp;
    | mdp => apply Logic.sumNormal.mdp <;> assumption;
    | nec => apply Logic.sumNormal.nec; assumption;
    | _ => apply Logic.sumNormal.mem₁; apply Logic.sumNormal.mem₁; simp;
  . intro hφ;
    induction hφ with
    | mem₁ h =>
      apply S5Grz.proper_extension_of_S5.subset;
      rwa [S5.is_smallestMC_of_Cl];
    | mdp hφ hψ ihφψ ihψ => apply Modal.Logic.mdp ihφψ ihψ;
    | subst h ih => apply Modal.Logic.subst ih;
    | nec h ih => apply Modal.Logic.nec ih;
    | mem₂ h =>
      rcases h with ⟨φ, hφ, rfl⟩; simp;

instance modalCompanion_Cl_S5Grz : ModalCompanion Logic.Cl Logic.S5Grz := by
  rw [Logic.S5Grz.is_largestMC_of_Cl];
  apply Modal.instModalCompanion_of_largestMC_via_KripkeSemantics
    (IC := Propositional.Kripke.FrameClass.finite_symmetric)
    (MC := Modal.Kripke.FrameClass.finite_equality);
  . rw [Logic.Cl.Kripke.finite_symmetric]
  . rw [←Logic.S5Grz.is_largestMC_of_Cl, ←Logic.S5Grz.Kripke.finite_equality]
  . rintro F ⟨_, _⟩;
    refine ⟨inferInstance, inferInstance⟩;

instance modalCompanion_Cl_Triv : ModalCompanion Logic.Cl Logic.Triv := by
  rw [←Logic.eq_S5Grz_Triv];
  infer_instance

end S5Grz


section boxdot

theorem embedding_Cl_Ver {φ : Propositional.Formula ℕ} : φ ∈ Logic.Cl ↔ φᵍᵇ ∈ Logic.Ver := by
  exact Iff.trans modalCompanion_Cl_Triv.companion Hilbert.iff_boxdotTranslated_Ver_Triv.symm

end boxdot

end LO.Modal
