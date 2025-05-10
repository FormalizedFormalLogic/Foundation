import Foundation.Propositional.Logic.WellKnown

namespace LO.Propositional.Logic

open Entailment
open Kripke
open Formula.Kripke

namespace BD

variable {n m : ℕ+}

theorem subset_succ : Logic.BD (n + 1) ⊂ Logic.BD n := by
  constructor;
  . simp only [Kripke.eq_isDepthLt, Set.setOf_subset_setOf];
    intro φ hφ F hF;
    apply hφ;
    simp only [Set.mem_setOf_eq, Frame.IsDepthLt, and_imp, PNat.add_coe, PNat.val_ofNat] at hF ⊢;
    intro l hl₁ hl₂;
    apply List.not_noDup_of_not_tail_noDup $ hF l.tail ?_ ?_;
    . simpa;
    . apply List.Chain'.tail hl₂;
  . suffices ∃ φ, (Hilbert.BD n) ⊢! φ ∧ ¬(FrameClass.isDepthLt (n + 1)) ⊧ φ by
      obtain ⟨φ, hφ₁, hφ₂⟩ := this;
      simp only [Kripke.eq_isDepthLt, Set.setOf_subset_setOf];
      push_neg;
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
      use ⟨Fin (n + 1), (· ≤ ·)⟩;
      constructor;
      . simp only [Set.mem_setOf_eq, Frame.IsDepthLt, PNat.add_coe, PNat.val_ofNat, and_imp];
        rintro l hl _;
        apply List.not_nodup_of_lt_length;
        omega;
      . apply not_imp_not.mpr $ Kripke.isDepthLt_of_validate_BoundDepth;
        dsimp [Frame.IsDepthLt];
        push_neg;
        use List.finRange (n + 1);
        exact ⟨⟨List.length_finRange _, List.finRange.chain'_lt⟩, List.finRange.noDup⟩;

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
  apply BD.neq_of_neq;

end BD

end LO.Propositional.Logic
