import Foundation.Modal.ModalCompanion.Int
import Foundation.Modal.Kripke.Logic.S5Grz
import Foundation.Modal.Boxdot.Ver_Triv
import Foundation.Propositional.Kripke.Logic.Cl

namespace LO.Modal

open LO.Entailment LO.Entailment.FiniteContext LO.Modal.Entailment
open Propositional
open Propositional.Formula (atom goedelTranslate)
open Propositional.Logic (smallestMC largestMC)
open Modal
open Modal.Kripke
open Modal.Formula.Kripke


lemma smallestMC_of_Cl.mem_diabox_box : (𝐂𝐥.smallestMC) ⊢! (◇□(.atom 0) ➝ □(.atom 0)) := by
  have H₁ : (𝐂𝐥.smallestMC) ⊢! □(.atom 0) ⋎ □(∼□(.atom 0)) := by
    apply Logic.sumNormal.mem₂!;
    use Axioms.LEM (.atom 0);
    constructor;
    . simp [theory];
    . tauto;
  have H₂ : 𝐂𝐥.smallestMC ⊢! ◇□(.atom 0) ➝ ∼□(∼□(.atom 0)) := diaDuality_mp!;
  cl_prover [H₁, H₂];

instance : Entailment.HasAxiomFive (𝐂𝐥.smallestMC) where
  Five φ := by
    constructor;
    apply Modal.Logic.iff_provable.mp;
    apply Modal.Logic.subst! (L := (𝐂𝐥.smallestMC)) (φ := Modal.Axioms.Five (.atom 0)) (s := λ a => φ);
    have H₁ : 𝐂𝐥.smallestMC ⊢! ◇□(∼.atom 0) ➝ □(∼.atom 0) := Modal.Logic.subst! (s := λ _ => ∼(.atom 0)) $ smallestMC_of_Cl.mem_diabox_box;
    have H₂ : 𝐂𝐥.smallestMC ⊢! ∼□◇(.atom 0) ➝ ◇□(∼.atom 0) := diaDuality_mp!;
    have H₃ : 𝐂𝐥.smallestMC ⊢! ◇(.atom 0) ➝ ∼□(∼.atom 0) := diaDuality_mp!;
    cl_prover [H₁, H₂, H₃];

namespace S5

instance : Modal.S5 ≊ 𝐂𝐥.smallestMC := by
  apply Logic.equiv_of_provable;
  intro φ;
  constructor;
  . intro hφ;
    induction hφ using Modal.Hilbert.Normal.rec! with
    | axm s h =>
      rcases h with (rfl | rfl | rfl | rfl) <;> simp;
    | mdp ihφψ ihφ => exact ihφψ ⨀ ihφ;
    | nec ihφ => exact nec! ihφ;
    | _ => simp;
  . intro hφ;
    induction hφ using Logic.sumNormal.rec! with
    | mem₁ h => apply WeakerThan.pbl h;
    | mdp ihφψ ihψ => exact ihφψ ⨀ ihψ;
    | nec ihφ => exact nec! ihφ;
    | subst ihφ => apply Logic.subst! _ ihφ;
    | mem₂ h =>
      rcases h with ⟨φ, hφ, rfl⟩;
      apply provable_goedelTranslated_of_provable Hilbert.Cl Modal.S5;
      . rintro _ ⟨_, (rfl | rfl), ⟨s, rfl⟩⟩;
        . simp;
        . apply rm_diabox'!;
          apply WeakerThan.pbl (𝓢 := Modal.S4);
          apply (diaK'! $ goedelTranslated_axiomTc) ⨀ (iff_provable_Cl_provable_dia_gS4.mp _);
          simp [theory];
      . simpa [theory] using hφ;

lemma is_smallestMC_of_Cl : Modal.S5 = 𝐂𝐥.smallestMC := Logic.eq_of_equiv

instance : Sound (𝐂𝐥.smallestMC) FrameClass.S5 := Kripke.sound_frameClass_of_equiv Modal.S5 𝐂𝐥.smallestMC

instance : ModalCompanion 𝐂𝐥 Modal.S5 := by
  apply is_smallestMC_of_Cl ▸ Modal.instModalCompanion_of_smallestMC_via_KripkeSemantics
    (IL := 𝐂𝐥)
    (IC := Propositional.Kripke.FrameClass.Cl)
    (MC := Modal.Kripke.FrameClass.S5)
  rintro F hF;
  simp_all only [Set.mem_setOf_eq];
  constructor;

end S5


instance : 𝐂𝐥.smallestMC ⪯ Modal.S5Grz := calc
  _ ≊ Modal.S5    := by symm; infer_instance;
  _ ⪯ Modal.S5Grz := inferInstance


section S5Grz


instance : Modal.S5Grz ≊ 𝐂𝐥.largestMC := by
  apply Logic.equiv_of_provable;
  intro φ;
  constructor;
  . intro hφ;
    induction hφ using Modal.Hilbert.Normal.rec! with
    | axm _ h =>
      rcases h with (rfl | rfl | rfl | rfl);
      . simp;
      . simp;
      . apply WeakerThan.pbl (𝓢 := 𝐂𝐥.smallestMC); simp;
      . simp;
    | mdp ihφψ ihψ => exact ihφψ ⨀ ihψ;
    | nec ihφ => exact nec! ihφ;
    | _ => apply Logic.sumNormal.mem₁!; simp;
  . intro hφ;
    induction hφ using Logic.sumNormal.rec! with
    | mdp ihφψ ihψ => exact ihφψ ⨀ ihψ;
    | subst ih => apply Logic.subst! _ ih;
    | nec ih => apply nec! ih;
    | mem₁ h => apply WeakerThan.pbl h;
    | mem₂ h => rcases h with ⟨φ, hφ, rfl⟩; simp;

lemma is_largestMC_of_KC : Modal.S5Grz = 𝐂𝐥.largestMC := Logic.eq_of_equiv

instance : Sound 𝐂𝐥.largestMC FrameClass.finite_Triv := Kripke.sound_frameClass_of_equiv Modal.S5Grz 𝐂𝐥.largestMC

end S5Grz


instance S5Grz.modalCompanion : ModalCompanion 𝐂𝐥 Modal.S5Grz := by
  apply is_largestMC_of_KC ▸ Modal.instModalCompanion_of_largestMC_via_KripkeSemantics
    (IC := Propositional.Kripke.FrameClass.finite_Cl)
    (MC := Modal.Kripke.FrameClass.finite_Triv);
  . intro F hF; simp_all only [Set.mem_setOf_eq]; exact {};

instance Triv.modalCompanion : ModalCompanion 𝐂𝐥 Modal.Triv := by
  convert S5Grz.modalCompanion;
  have : Modal.Triv ≊ Modal.S5Grz := by symm; infer_instance;
  apply Logic.eq_of_equiv;


section boxdot

theorem embedding_Cl_Ver {φ : Propositional.Formula ℕ} : 𝐂𝐥 ⊢! φ ↔ Modal.Ver ⊢! φᵍᵇ :=
  Iff.trans ModalCompanion.companion Logic.iff_boxdotTranslated_Ver_Triv.symm

end boxdot


end LO.Modal
