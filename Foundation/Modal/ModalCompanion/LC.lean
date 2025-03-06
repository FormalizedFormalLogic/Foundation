import Foundation.Modal.ModalCompanion.Int
import Foundation.Modal.Logic.Sublogic.S4
import Foundation.Propositional.Kripke.Hilbert.LC

namespace LO.Modal

open Entailment FiniteContext
open Propositional
open Propositional.Formula (goedelTranslate)
open Propositional.Formula (atom)
open Modal
open Modal.Kripke

lemma Hilbert.S4Point3.goedelTranslated_axiomDummett : Hilbert.S4Point3 ⊢! □(□ψᵍ ➝ χᵍ) ➝ □(ψᵍ ➝ χᵍ) := by
  apply axiomK'!;
  apply nec!;
  apply imp_swap'!;
  apply deduct'!;
  apply deduct!;
  have h₁ : [□ψᵍ ➝ χᵍ, ψᵍ] ⊢[Hilbert.S4Point3]! ψᵍ ➝ □ψᵍ := of'! $ Hilbert.goedelTranslated_axiomTc;
  have h₂ : [□ψᵍ ➝ χᵍ, ψᵍ] ⊢[Hilbert.S4Point3]! ψᵍ := by_axm!;
  have h₃ : [□ψᵍ ➝ χᵍ, ψᵍ] ⊢[Hilbert.S4Point3]! □ψᵍ ➝ χᵍ := by_axm!;
  exact h₃ ⨀ (h₁ ⨀ h₂);

private lemma Hilbert.S4Point.lemma₁ : Hilbert.S4 ⊢! □(□φ ➝ □ψ) ➝ □(□φ ➝ ψ) := by
  apply Hilbert.S4.Kripke.complete.complete;
  intro F ⟨F_refl, _⟩ V x h₁ y Rxy h₂;
  apply @h₁ y Rxy h₂;
  apply F_refl;

namespace Logic

lemma mem_gAxiomPoint3_smallestMC_of_LC : □(□(.atom 0) ➝ (.atom 1)) ⋎ □(□(.atom 1) ➝ (.atom 0)) ∈ Logic.LC.smallestMC := by
  have : □(□.atom 0 ➝ □.atom 1) ⋎ □(□.atom 1 ➝ □.atom 0) ∈ Logic.LC.smallestMC := by
    apply Logic.sumNormal.mem₂;
    use Axioms.Dummett (.atom 0) (.atom 1);
    simp [Axioms.Dummett, goedelTranslate];
  apply Propositional.Logic.smallestMC.mdp_S4 ?_ this;
  apply or_replace!;
  repeat exact Hilbert.S4Point.lemma₁;

lemma S4Point3.is_smallestMC_of_LC : Logic.S4Point3 = Logic.LC.smallestMC := by
  ext φ;
  constructor;
  . intro hφ;
    induction hφ using Hilbert.Deduction.rec! with
    | maxm h =>
      rcases (by simpa using h) with (⟨s, rfl⟩ | ⟨s, rfl⟩ | ⟨s, rfl⟩ | ⟨s, rfl⟩);
      . apply Logic.sumNormal.mem₁; simp;
      . apply Logic.sumNormal.mem₁; simp;
      . apply Logic.sumNormal.mem₁; simp;
      . exact Logic.sumNormal.subst $ mem_gAxiomPoint3_smallestMC_of_LC;
    | mdp => apply Logic.sumNormal.mdp <;> assumption;
    | nec => apply Logic.sumNormal.nec; assumption;
    | _ => apply Logic.sumNormal.mem₁; simp;
  . intro hφ;
    induction hφ with
    | mem₁ h => apply Logic.S4_ssubset_S4Point3.1 h;
    | mdp hφ hψ ihφψ ihψ => apply Modal.Logic.mdp ihφψ ihψ;
    | subst h ih => apply Modal.Logic.subst ih;
    | nec h ih => apply Modal.Logic.nec ih;
    | mem₂ h =>
      rcases h with ⟨φ, hφ, rfl⟩;
      apply Hilbert.provable_goedelTranslated_of_provable Hilbert.LC Hilbert.S4Point3 ?_ (by trivial);
      rintro _ ⟨_, ⟨(rfl | rfl), ⟨s, rfl⟩⟩⟩;
      . apply Logic.S4_ssubset_S4Point3.1;
        apply modalCompanion_Int_S4.companion.mp;
        simp;
      . suffices Hilbert.S4Point3 ⊢! □(s 0ᵍ ➝ s 1ᵍ) ⋎ □(s 1ᵍ ➝ s 0ᵍ) by simpa [goedelTranslate];
        apply or_replace'! axiomPoint3!;
        repeat exact Hilbert.S4Point3.goedelTranslated_axiomDummett;

instance modalCompanion_LC_S4Point3 : ModalCompanion Logic.LC Logic.S4Point3 := by
  rw [Logic.S4Point3.is_smallestMC_of_LC];
  exact Modal.instModalCompanion_of_smallestMC_via_KripkeSemantics
    (IC := Propositional.Kripke.ConnectedFrameClass)
    (MC := Modal.Kripke.ReflexiveTransitiveConnectedFrameClass)
    (by
      intro φ;
      constructor;
      . apply Propositional.Hilbert.LC.Kripke.sound.sound;
      . apply Propositional.Hilbert.LC.Kripke.complete.complete;
    )
    (by
      rw [←Logic.S4Point3.is_smallestMC_of_LC];
      intro φ;
      constructor;
      . apply Modal.Hilbert.S4Point3.Kripke.sound.sound;
      . apply Modal.Hilbert.S4Point3.Kripke.complete.complete;
    )
    (by
      rintro F hF;
      refine ⟨F.rel_refl, F.rel_trans, hF⟩;
    );

end Logic


end LO.Modal
