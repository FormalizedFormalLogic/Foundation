import Foundation.Propositional.Logic.WellKnown


namespace List

lemma finfin {l : List (Fin n)} : l.length > n → ¬l.Nodup := by
  sorry

end List


namespace LO.Propositional.Logic

open Entailment
open Kripke
open Formula.Kripke

namespace BD

variable {n m : ℕ+}

theorem subset_succ : Logic.BD (n + 1) ⊂ Logic.BD n := by
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
        . sorry;
          /-
          intro i j;
          contrapose!;
          -- simp [List.get_finRange]
          sorry;
          -/

lemma subset_add : Logic.BD (n + m) ⊂ Logic.BD n := by
  induction m with
  | one => exact subset_succ;
  | succ m ih =>
    trans Logic.BD (n + m);
    . rw [(show n + (m + 1) = n + m + 1 by rfl)];
      apply subset_succ;
    . apply ih;

lemma subset_of_lt (hnm : n < m) : Logic.BD m ⊂ Logic.BD n := by
  convert subset_add (n := n) (m := m - n);
  exact PNat.add_sub_of_lt hnm |>.symm;

lemma neq_of_neq (hnm : n ≠ m) : Logic.BD n ≠ Logic.BD m := by
  rcases lt_trichotomy n m with h | rfl | h;
  . apply subset_of_lt h |>.ne.symm;
  . contradiction;
  . apply subset_of_lt h |>.ne;

/-- There are countable infinite superintuitionistic logics. -/
instance : Infinite { L : Logic // L.IsSuperintuitionistic ∧ L.Consistent } := Infinite.of_injective (λ n => ⟨Logic.BD n, ⟨inferInstance, inferInstance⟩⟩) $ by
  intro i j;
  simp only [Subtype.mk.injEq];
  contrapose!;
  intro hij;
  exact BD.neq_of_neq hij;

end BD

end LO.Propositional.Logic
