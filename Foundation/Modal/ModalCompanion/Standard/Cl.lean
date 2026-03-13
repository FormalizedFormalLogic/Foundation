module

public import Foundation.Logic.Embedding
public import Foundation.Modal.ModalCompanion.Standard.Int
public import Foundation.Modal.Kripke.Logic.S5Grz
public import Foundation.Modal.Boxdot.Ver_Triv
public import Foundation.Propositional.Kripke.Logic.Cl

@[expose] public section

namespace LO.Modal

open LO.Entailment LO.Entailment.FiniteContext LO.Modal.Entailment
open Propositional
open Propositional.Formula (atom gödelTranslate)
open Propositional.Logic (smallestMC largestMC)
open Modal
open Modal.Kripke
open Modal.Formula.Kripke


lemma smallestMC_of_Cl.mem_diabox_box : (Propositional.Cl.smallestMC) ⊢ (◇□(.atom 0) 🡒 □(.atom 0)) := by
  have H₁ : (Propositional.Cl.smallestMC) ⊢ □(.atom 0) ⋎ □(∼□(.atom 0)) := by
    apply Logic.sumNormal.mem₂!;
    use Axioms.LEM (.atom 0);
    constructor;
    . apply Propositional.Logic.iff_provable.mp;
      simp;
    . tauto;
  have H₂ : Propositional.Cl.smallestMC ⊢ ◇□(.atom 0) 🡒 ∼□(∼□(.atom 0)) := dia_duality!_mp;
  cl_prover [H₁, H₂];

instance : Entailment.HasAxiomFive (Propositional.Cl.smallestMC) where
  Five φ := by
    constructor;
    apply Modal.Logic.iff_provable.mp;
    apply Modal.Logic.subst (L := (Propositional.Cl.smallestMC)) (φ := Modal.Axioms.Five (.atom 0)) (s := λ a => φ);
    have H₁ : Propositional.Cl.smallestMC ⊢ ◇□(∼.atom 0) 🡒 □(∼.atom 0) := Modal.Logic.subst (s := λ _ => ∼(.atom 0)) $ smallestMC_of_Cl.mem_diabox_box;
    have H₂ : Propositional.Cl.smallestMC ⊢ ∼□◇(.atom 0) 🡒 ◇□(∼.atom 0) := dia_duality!_mp;
    have H₃ : Propositional.Cl.smallestMC ⊢ ◇(.atom 0) 🡒 ∼□(∼.atom 0) := dia_duality!_mp;
    cl_prover [H₁, H₂, H₃];

namespace S5

instance : Modal.S5 ≊ Propositional.Cl.smallestMC := by
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
    | subst ihφ => apply Logic.subst _ ihφ;
    | mem₂ h =>
      rcases h with ⟨φ, hφ, rfl⟩;
      apply provable_gödelTranslated_of_provable ?_ (Propositional.Logic.iff_provable.mpr hφ);
      rintro _ ⟨_, (rfl | rfl), ⟨s, rfl⟩⟩;
      . simp;
      . apply rm_diabox'!;
        apply WeakerThan.pbl (𝓢 := Modal.S4);
        apply (diaK'! $ gödelTranslated_axiomTc) ⨀ (iff_provable_Cl_provable_dia_gS4.mp _);
        simp;

lemma is_smallestMC_of_Cl : Modal.S5 = Propositional.Cl.smallestMC := Logic.eq_of_equiv

instance : Sound (Propositional.Cl.smallestMC) FrameClass.S5 := Kripke.sound_frameClass_of_equiv Modal.S5 Propositional.Cl.smallestMC

instance : ModalCompanion Propositional.Cl Modal.S5 := by
  apply is_smallestMC_of_Cl ▸ Modal.instModalCompanion_of_smallestMC_via_KripkeSemantics
    (IL := Propositional.Cl)
    (IC := Propositional.Kripke.FrameClass.Cl)
    (MC := Modal.Kripke.FrameClass.S5)
  rintro F hF;
  simp_all only [Set.mem_setOf_eq];
  constructor;

end S5


instance : Propositional.Cl.smallestMC ⪯ Modal.S5Grz := calc
  _ ≊ Modal.S5    := by symm; infer_instance;
  _ ⪯ Modal.S5Grz := inferInstance


section S5Grz


instance : Modal.S5Grz ≊ Propositional.Cl.largestMC := by
  apply Logic.equiv_of_provable;
  intro φ;
  constructor;
  . intro hφ;
    induction hφ using Modal.Hilbert.Normal.rec! with
    | axm _ h =>
      rcases h with (rfl | rfl | rfl | rfl);
      . simp;
      . simp;
      . apply WeakerThan.pbl (𝓢 := Propositional.Cl.smallestMC); simp;
      . simp;
    | mdp ihφψ ihψ => exact ihφψ ⨀ ihψ;
    | nec ihφ => exact nec! ihφ;
    | _ => apply Logic.sumNormal.mem₁!; simp;
  . intro hφ;
    induction hφ using Logic.sumNormal.rec! with
    | mdp ihφψ ihψ => exact ihφψ ⨀ ihψ;
    | subst ih => apply Logic.subst _ ih;
    | nec ih => apply nec! ih;
    | mem₁ h => apply WeakerThan.pbl h;
    | mem₂ h => rcases h with ⟨φ, hφ, rfl⟩; simp;

lemma is_largestMC_of_Cl : Modal.S5Grz = Propositional.Cl.largestMC := Logic.eq_of_equiv

instance : Sound Propositional.Cl.largestMC FrameClass.finite_Triv := Kripke.sound_frameClass_of_equiv Modal.S5Grz Propositional.Cl.largestMC

end S5Grz


instance S5Grz.modalCompanion : ModalCompanion Propositional.Cl Modal.S5Grz := by
  apply is_largestMC_of_Cl ▸ Modal.instModalCompanion_of_largestMC_via_KripkeSemantics
    (IC := Propositional.Kripke.FrameClass.finite_Cl)
    (MC := Modal.Kripke.FrameClass.finite_Triv);
  . intro F hF; simp_all only [Set.mem_setOf_eq]; exact {};

instance Triv.modalCompanion : ModalCompanion Propositional.Cl Modal.Triv := by
  convert S5Grz.modalCompanion;
  have : Modal.Triv ≊ Modal.S5Grz := by symm; infer_instance;
  apply Logic.eq_of_equiv;


section boxdot

theorem embedding_Cl_Ver {φ : Propositional.Formula ℕ} : Propositional.Cl ⊢ φ ↔ Modal.Ver ⊢ φᵍᵇ :=
  Iff.trans ModalCompanion.companion Logic.iff_boxdotTranslated_Ver_Triv.symm

instance : Entailment.FaithfullyEmbeddable Propositional.Cl Modal.Ver where
  prop := ⟨(·ᵍᵇ), fun _ ↦ embedding_Cl_Ver.symm⟩

end boxdot


end LO.Modal
end
