import Foundation.Propositional.Logic.WellKnown


namespace List.finRange

#check List.getElem_finRange

-- lemma finRange_get

end List.finRange


namespace LO.Propositional.Logic

open Entailment
open Kripke
open Formula.Kripke

theorem Int_ssubset_KC : Logic.Int ⊂ Logic.KC := by
  constructor;
  . exact (Hilbert.weakerThan_of_subset_axioms (by simp)).subset;
  . suffices ∃ φ, Hilbert.KC ⊢! φ ∧ ¬FrameClass.all ⊧ φ by simpa [Int.Kripke.eq_all]
    use Axioms.WeakLEM (.atom 0);
    constructor;
    . exact wlem!;
    . apply not_validOnFrameClass_of_exists_frame;
      let F : Frame := {
        World := Fin 3
        Rel := λ x y => x = 0 ∨ (x = y)
        rel_partial_order := {
          refl := by omega;
          trans := by omega;
          antisymm := by omega;
        }
      };
      use F;
      constructor;
      . tauto;
      . apply not_imp_not.mpr $ Kripke.confluent_of_validate_WeakLEM;
        unfold Confluent;
        push_neg;
        use 0, 1, 2;
        simp [F];

theorem KC_ssubset_LC : Logic.KC ⊂ Logic.LC := by
  constructor;
  . exact (Hilbert.weakerThan_of_dominate_axiomInstances
      (by rintro _ ⟨ψ, ⟨(rfl | rfl), ⟨s, rfl⟩⟩⟩ <;> simp [efq!, wlem!])).subset
  . suffices ∃ φ, Hilbert.LC ⊢! φ ∧ ¬FrameClass.confluent ⊧ φ by simpa [KC.Kripke.eq_confluent];
    use Axioms.Dummett (.atom 0) (.atom 1);
    constructor;
    . exact dummett!;
    . apply not_validOnFrameClass_of_exists_frame;
      let F : Frame := {
        World := Fin 4
        Rel := λ x y => ¬(x = 1 ∧ y = 2) ∧ ¬(x = 2 ∧ y = 1) ∧ (x ≤ y)
        rel_partial_order := {
          refl := by omega;
          trans := by omega;
          antisymm := by omega;
        }
      }
      use F;
      constructor;
      . apply isConfluent_iff _ _ |>.mpr
        simp [F, Confluent];
        intros;
        use 3;
        omega;
      . apply not_imp_not.mpr $ Kripke.connected_of_validate_Dummett;
        unfold Connected;
        push_neg;
        use 0, 1, 2;
        simp [F];

theorem LC_ssubset_Cl : Logic.LC ⊂ Logic.Cl := by
  constructor;
  . apply (Hilbert.weakerThan_of_dominate_axiomInstances
      (by rintro _ ⟨ψ, ⟨(rfl | rfl), ⟨s, rfl⟩⟩⟩ <;> simp [efq!, dummett!])).subset;
  . suffices ∃ φ, Hilbert.Cl ⊢! φ ∧ ¬FrameClass.connected ⊧ φ by simpa [LC.Kripke.eq_connected];
    use Axioms.LEM (.atom 0);
    constructor;
    . exact lem!;
    . apply not_validOnFrameClass_of_exists_frame;
      let F : Frame := {
        World := Fin 2,
        Rel := λ x y => x ≤ y
        rel_partial_order := {
          refl := by omega;
          trans := by omega;
          antisymm := by omega;
        }
      }
      use F;
      constructor;
      . apply isConnected_iff _ _ |>.mpr
        simp [F, Connected];
        omega;
      . apply not_imp_not.mpr $ Kripke.euclidean_of_validate_LEM;
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
