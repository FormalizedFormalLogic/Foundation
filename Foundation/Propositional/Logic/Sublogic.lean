import Foundation.Propositional.Logic.WellKnown

namespace LO.Propositional.Logic

open Entailment
open Kripke
open Formula.Kripke

theorem Int_ssubset_KC : Logic.Int ⊂ Logic.KC := by
  constructor;
  . exact (Hilbert.weakerThan_of_subset_axioms (by simp)).subset;
  . suffices ∃ φ, Hilbert.KC ⊢! φ ∧ ¬AllFrameClass ⊧ φ by simpa [Int.eq_AllKripkeFrameClass_Logic];
    use Axioms.WeakLEM (.atom 0);
    constructor;
    . exact wlem!;
    . apply Formula.Kripke.ValidOnFrameClass.not_of_exists_frame;
      let F : Frame := {
        World := Fin 3
        Rel := λ x y => x = 0 ∨ (x = y)
        rel_refl := by simp [Reflexive];
        rel_trans := by simp [Transitive]; omega;
      };
      use F;
      constructor;
      . tauto;
      . apply (show ¬Confluent F.Rel → ¬ValidOnFrame F (Axioms.WeakLEM (.atom 0)) by
          simpa using Kripke.ConfluentFrameClass.definedByWeakLEM.defines F |>.not.mp
        );
        unfold Confluent;
        push_neg;
        use 0, 1, 2;
        simp [F];

theorem KC_ssubset_LC : Logic.KC ⊂ Logic.LC := by
  constructor;
  . exact (Hilbert.weakerThan_of_dominate_axiomInstances
      (by rintro _ ⟨ψ, ⟨(rfl | rfl), ⟨s, rfl⟩⟩⟩ <;> simp [efq!, wlem!])).subset
  . suffices ∃ φ, Hilbert.LC ⊢! φ ∧ ¬ConfluentFrameClass ⊧ φ by simpa [KC.eq_ConfluentKripkeFrameClass_Logic];
    use Axioms.Dummett (.atom 0) (.atom 1);
    constructor;
    . exact dummett!;
    . apply Formula.Kripke.ValidOnFrameClass.not_of_exists_frame;
      let F : Frame := {
        World := Fin 4
        Rel := λ x y => ¬(x = 1 ∧ y = 2) ∧ ¬(x = 2 ∧ y = 1) ∧ (x ≤ y)
        rel_refl := by simp [Reflexive]; omega;
        rel_trans := by simp [Transitive]; omega;
      }
      use F;
      constructor;
      . simp [F, Confluent];
        intros;
        use 3;
        omega;
      . apply (show ¬Connected F.Rel → ¬ValidOnFrame F (Axioms.Dummett (.atom 0) (.atom 1)) by
          simpa using Kripke.ConfluentFrameClass.definedByDummett.defines F |>.not.mp
        );
        unfold Connected;
        push_neg;
        use 0, 1, 2;
        simp [F];

theorem LC_ssubset_Cl : Logic.LC ⊂ Logic.Cl := by
  constructor;
  . apply (Hilbert.weakerThan_of_dominate_axiomInstances
      (by rintro _ ⟨ψ, ⟨(rfl | rfl), ⟨s, rfl⟩⟩⟩ <;> simp [efq!, dummett!])).subset;
  . suffices ∃ φ, Hilbert.Cl ⊢! φ ∧ ¬ConnectedFrameClass ⊧ φ by simpa [LC.eq_ConnectedKripkeFrameClass_Logic];
    use Axioms.LEM (.atom 0);
    constructor;
    . exact lem!;
    . apply Formula.Kripke.ValidOnFrameClass.not_of_exists_frame;
      let F : Frame := {
        World := Fin 2,
        Rel := λ x y => x ≤ y
        rel_refl := by simp [Reflexive];
        rel_trans := by simp [Transitive]; omega;
      }
      use F;
      constructor;
      . simp [F, Connected]; omega;
      . apply (show ¬Euclidean F.Rel → ¬ValidOnFrame F (Axioms.LEM (.atom 0)) by
          simpa using Kripke.EuclideanFrameClass.definedByLEM.defines F |>.not.mp
        );
        unfold Euclidean;
        push_neg;
        use 0, 0, 1;
        simp [F];

theorem Int_ssubset_Cl : Logic.Int ⊂ Logic.Cl := by
  trans Logic.LC;
  . trans Logic.KC;
    . exact Int_ssubset_KC;
    . exact KC_ssubset_LC;
  . exact LC_ssubset_Cl

end LO.Propositional.Logic
