import Foundation.Propositional.Logic.WellKnown

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



section BD

theorem BD_subset_BD_succ : Logic.BD (n + 1) ⊂ Logic.BD n := by
  constructor;
  . apply (Hilbert.weakerThan_of_dominate_axiomInstances ?_) |>.subset;
    simp;
    rintro φ (⟨s, rfl⟩ | ⟨s, rfl⟩);
    . simp;
    . sorry;
  . suffices ∃ φ, (Hilbert.BD n) ⊢! φ ∧ ¬(FrameClass.isDepthLt (n + 1)) ⊧ φ by
      simp [Set.setOf_subset_setOf, BD.Kripke.eq_isDepthLt];
      obtain ⟨φ, hφ₁, hφ₂⟩ := this;
      use φ;
      constructor;
      . exact BD.Kripke.eq_isDepthLt.subset hφ₁;
      . assumption;
    use Axioms.BoundDepth n;
    constructor;
    . apply Hilbert.Deduction.maxm!;
      simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, exists_eq_or_imp, exists_eq_left];
      right;
      use Substitution.id;
      simp;
    . apply not_validOnFrameClass_of_exists_frame;
      let F : Frame := {
        World := Fin (n + 1),
        Rel := λ x y => x ≤ y
        rel_partial_order := {
          refl := by omega;
          trans := by omega;
          antisymm := by omega;
        }
      }
      use F;
      constructor;
      . simp [Frame.IsDepthLt];
        intro l hl₁ hl₂;
        sorry;
      . apply not_imp_not.mpr $ Kripke.isDepthLt_of_validate_BoundDepth;
        dsimp [Frame.IsDepthLt];
        push_neg;
        use List.finRange (n + 1);
        refine ⟨⟨?_, ?_⟩, ?_⟩;
        . simp [List.finRange];
        . sorry;
        . intro i j;
          contrapose!;
          sorry;

lemma BD_subset_of_lt (hnm : n < m) : Logic.BD m ⊂ Logic.BD n  := by
  sorry;

lemma BD_injective (hnm : n ≠ m) : Logic.BD n ≠ Logic.BD m := by
  rcases lt_trichotomy n m with h | rfl | h;
  . apply BD_subset_of_lt h |>.ne.symm;
  . contradiction;
  . apply BD_subset_of_lt h |>.ne;

/-- There are countable infinite superintuitionistic logics. -/
instance : Infinite SuperintuitionisticLogic := Infinite.of_injective (λ n => ⟨Logic.BD n, inferInstance⟩) $ by
  intro i j;
  simp only [Subtype.mk.injEq];
  contrapose!;
  intro hij;
  apply BD_injective;
  exact hij;

end BD

end LO.Propositional.Logic
