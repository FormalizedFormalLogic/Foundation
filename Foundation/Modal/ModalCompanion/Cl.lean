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

lemma Logic.Cl.smallestMC.mem_diabox_box : Logic.Cl.smallestMC ⊢! (◇□(.atom 0) ➝ □(.atom 0)) := by
  have : Logic.Cl.smallestMC ⊢! □(.atom 0) ⋎ □(∼□(.atom 0)) := by
    apply Logic.sumNormal.mem₂!;
    use Axioms.LEM (.atom 0);
    constructor;
    . simp [-Propositional.Logic.iff_provable, theory];
    . tauto;
  apply _ ⨀ this;
  apply C!_trans ?_ CANC!;
  apply C!_trans ?_ or_comm!;
  apply CAA!_of_C!_of_C!;
  . simp;
  . apply CN!_of_CN!_right;
    exact diaDuality_mp!;

instance : Entailment.HasAxiomFive Logic.Cl.smallestMC where
  Five φ := by
    constructor;
    apply Modal.Logic.iff_provable.mp;
    apply Modal.Logic.subst! (L := Logic.Cl.smallestMC) (φ := Modal.Axioms.Five (.atom 0)) (s := λ a => φ);
    have := Modal.Logic.subst! (s := λ _ => ∼(.atom 0)) $ Logic.Cl.smallestMC.mem_diabox_box;
    apply _ ⨀ this;
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
  apply Logic.iff_equal_provable_equiv.mpr;
  apply Entailment.Equiv.antisymm_iff.mpr;
  constructor;
  . apply Entailment.weakerThan_iff.mpr;
    intro φ hφ;
    induction hφ using Modal.Hilbert.rec! with
    | maxm h => rcases (by simpa using h) with (⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩) <;> simp;
    | mdp ihφψ ihφ => exact ihφψ ⨀ ihφ;
    | nec ihφ => exact nec! ihφ;
    | _ => simp;
  . apply Entailment.weakerThan_iff.mpr;
    intro _ hφ;
    induction hφ using Logic.sumNormal.rec! with
    | mem₁ h => apply WeakerThan.pbl h;
    | mdp ihφψ ihψ => exact ihφψ ⨀ ihψ;
    | nec ihφ => exact nec! ihφ;
    | subst ihφ => apply subst! _ ihφ;
    | mem₂ h =>
      rcases h with ⟨φ, hφ, rfl⟩;
      haveI : Logic.S4 ⊢! ◇φᵍ := iff_provable_Cl_provable_dia_gS4.mp hφ;
      haveI : Logic.S4 ⊢! ◇□φᵍ := (diaK'! $ goedelTranslated_axiomTc) ⨀ this;
      apply rm_diabox'!;
      apply WeakerThan.pbl this;

instance : Sound Logic.Cl.smallestMC FrameClass.S5 := by
  rw [←Logic.S5.is_smallestMC_of_Cl];
  infer_instance;

instance modalCompanion_Cl_S5 : ModalCompanion Logic.Cl Logic.S5 := by
  rw [Logic.S5.is_smallestMC_of_Cl];
  exact Modal.instModalCompanion_of_smallestMC_via_KripkeSemantics
    (IC := Propositional.Kripke.FrameClass.Cl)
    (MC := Modal.Kripke.FrameClass.S5)
    (by intro F hF; simp_all only [Set.mem_setOf_eq]; constructor);

end Logic

end S5


section S5Grz

lemma Logic.gS5Grz_of_Cl : Logic.Cl ⊢! φ → Logic.S5Grz ⊢! φᵍ := by
  intro h;
  apply WeakerThan.pbl $ modalCompanion_Cl_S5.companion.mp h;

lemma Logic.S5Grz.is_largestMC_of_Cl : Logic.S5Grz = Logic.Cl.largestMC := by
  apply Logic.iff_equal_provable_equiv.mpr;
  apply Entailment.Equiv.antisymm_iff.mpr;
  constructor;
  . apply Entailment.weakerThan_iff.mpr;
    intro _ hφ;
    induction hφ using Modal.Hilbert.rec! with
    | maxm h =>
      rcases (by simpa using h) with (⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩);
      . simp;
      . simp;
      . apply WeakerThan.pbl (𝓢 := Logic.Cl.smallestMC);
        simp;
      . simp;
    | mdp ihφψ ihφ => exact ihφψ ⨀ ihφ;
    | nec ihφ => exact nec! ihφ;
    | _ => simp;
  . apply Entailment.weakerThan_iff.mpr;
    intro φ hφ;
    induction hφ using Logic.sumNormal.rec! with
    | mem₁ h => apply WeakerThan.pbl $ Logic.S5.is_smallestMC_of_Cl ▸ h;
    | mdp ihφψ ihψ => exact ihφψ ⨀ ihψ;
    | subst ih => apply subst! _ ih;
    | nec ih => apply nec! ih;
    | mem₂ h => rcases h with ⟨φ, hφ, rfl⟩; simp;

instance : Sound Logic.Cl.largestMC FrameClass.finite_Triv := by
  suffices Sound Logic.Triv FrameClass.finite_Triv by
    simpa [←Logic.S5Grz.is_largestMC_of_Cl];
  infer_instance;

instance modalCompanion_Cl_S5Grz : ModalCompanion Logic.Cl Logic.S5Grz := by
  rw [Logic.S5Grz.is_largestMC_of_Cl];
  apply Modal.instModalCompanion_of_largestMC_via_KripkeSemantics
    (IC := Propositional.Kripke.FrameClass.finite_Cl)
    (MC := Modal.Kripke.FrameClass.finite_Triv);
  . intro F hF; simp_all only [Set.mem_setOf_eq]; exact {};

instance modalCompanion_Cl_Triv : ModalCompanion Logic.Cl Logic.Triv := by
  convert modalCompanion_Cl_S5Grz;
  simp;

end S5Grz


section boxdot

theorem embedding_Cl_Ver {φ : Propositional.Formula ℕ} : Logic.Cl ⊢! φ ↔ Logic.Ver ⊢! φᵍᵇ := by
  exact Iff.trans modalCompanion_Cl_Triv.companion Logic.iff_boxdotTranslated_Ver_Triv.symm

end boxdot

end LO.Modal
