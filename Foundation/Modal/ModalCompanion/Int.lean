import Foundation.Modal.ModalCompanion.Basic
import Foundation.Propositional.Logic.WellKnown
import Foundation.Modal.Logic.WellKnown
import Foundation.Modal.Logic.Extension
import Foundation.Modal.Logic.Sublogic.Grz

namespace LO.Modal

open Entailment FiniteContext
open Propositional
open Propositional.Formula (goedelTranslate)
open Modal
open Modal.Kripke

section S4

lemma Logic.gS4_of_Int : φ ∈ Logic.Int → φᵍ ∈ Logic.S4 := by
  apply Hilbert.provable_goedelTranslated_of_provable Hilbert.Int Hilbert.S4;
  rintro _ ⟨φ, ⟨_⟩, ⟨s, rfl⟩⟩;
  apply nec! $ efq!;

lemma Logic.S4.is_smallestMC_of_Int : Logic.S4 = Logic.Int.smallestMC := by
  ext φ;
  constructor;
  . intro hφ;
    induction hφ using Hilbert.Deduction.rec! with
    | maxm h =>
      rcases (by simpa using h) with (⟨s, rfl⟩ | ⟨s, rfl⟩ | ⟨s, rfl⟩);
      . apply Logic.sumNormal.mem₁; simp;
      . apply Logic.sumNormal.mem₁; simp;
      . apply Logic.sumNormal.mem₁; simp;
    | mdp => apply Logic.sumNormal.mdp <;> assumption;
    | nec => apply Logic.sumNormal.nec; assumption;
    | _ => apply Logic.sumNormal.mem₁; simp;
  . intro hφ;
    induction hφ with
    | mem₁ h => tauto;
    | mdp hφ hψ ihφψ ihψ => apply Modal.Logic.mdp ihφψ ihψ;
    | subst h ih => apply Modal.Logic.subst ih;
    | nec h ih => apply Modal.Logic.nec ih;
    | mem₂ h =>
      rcases h with ⟨φ, hφ, rfl⟩;
      apply Logic.gS4_of_Int hφ;

instance modalCompanion_Int_S4 : ModalCompanion Logic.Int Logic.S4 := by
  rw [Logic.S4.is_smallestMC_of_Int];
  exact Modal.instModalCompanion_of_smallestMC_via_KripkeSemantics
    (IC := Propositional.Kripke.FrameClass.all)
    (MC := Modal.Kripke.FrameClass.preorder)
    (by
      intro φ;
      constructor;
      . apply Propositional.Hilbert.Int.Kripke.sound.sound;
      . apply Propositional.Hilbert.Int.Kripke.complete.complete;
    )
    (by
      rw [←Logic.S4.is_smallestMC_of_Int];
      intro φ;
      constructor;
      . apply Modal.Hilbert.S4.Kripke.sound.sound;
      . apply Modal.Hilbert.S4.Kripke.complete.complete;
    )
    (fun F hF => ⟨F.rel_refl, F.rel_trans⟩);


end S4



section Grz

lemma Logic.gGrz_of_Int : φ ∈ Logic.Int → φᵍ ∈ Logic.Grz := by
  intro h;
  exact S4_ssubset_Grz.1 $ Logic.gS4_of_Int h;

lemma Logic.Grz.is_largestMC_of_Int : Logic.Grz = Logic.Int.largestMC := by
  ext φ;
  constructor;
  . intro hφ;
    induction hφ using Hilbert.Deduction.rec! with
    | maxm h =>
      rcases (by simpa using h) with (⟨s, rfl⟩ | ⟨s, rfl⟩);
      . apply Logic.sumNormal.mem₁;
        apply Logic.sumNormal.mem₁;
        simp;
      . apply Logic.sumNormal.subst (φ := □(□((.atom 0) ➝ □(.atom 0)) ➝ (.atom 0)) ➝ (.atom 0)) (s := s);
        apply Logic.sumNormal.mem₂;
        simp;
    | mdp => apply Logic.sumNormal.mdp <;> assumption;
    | nec => apply Logic.sumNormal.nec; assumption;
    | _ => apply Logic.sumNormal.mem₁; apply Logic.sumNormal.mem₁; simp;
  . intro hφ;
    induction hφ with
    | mem₁ h =>
      apply S4_ssubset_Grz.1;
      rwa [Logic.S4.is_smallestMC_of_Int]
    | mdp hφ hψ ihφψ ihψ => apply Modal.Logic.mdp ihφψ ihψ;
    | subst h ih => apply Modal.Logic.subst ih;
    | nec h ih => apply Modal.Logic.nec ih;
    | mem₂ h =>
      rcases h with ⟨φ, hφ, rfl⟩; simp;

instance : ModalCompanion Logic.Int Logic.Grz := by
  rw [Logic.Grz.is_largestMC_of_Int];
  exact Modal.instModalCompanion_of_largestMC_via_KripkeSemantics
    (IC := Propositional.Kripke.FrameClass.all_finite)
    (MC := Modal.Kripke.FiniteFrameClass.strict_preorder.toFrameClass)
    (by
      intro φ;
      constructor;
      . apply Propositional.Hilbert.Int.Kripke.sound_finite.sound;
      . apply Propositional.Hilbert.Int.Kripke.complete_finite.complete;
    )
    (by
      rw [←Logic.Grz.is_largestMC_of_Int];
      intro φ;
      constructor;
      . intro h F hF;
        obtain ⟨F, hF, rfl⟩ := hF;
        apply Modal.Hilbert.Grz.Kripke.finite_sound.sound h hF;
      . intro hF;
        apply Modal.Hilbert.Grz.Kripke.complete.complete;
        rintro _ _;
        apply hF;
        tauto;
    )
    (by
      rintro F hF;
      use ({ World := F.World, Rel := F.Rel, world_finite := by tauto; });
      simp only [Set.mem_setOf_eq, and_true];
      refine ⟨F.rel_refl, F.rel_trans, F.rel_antisymm⟩;
    )

end Grz

end LO.Modal
