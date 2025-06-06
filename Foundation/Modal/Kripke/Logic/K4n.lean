import Foundation.Modal.Kripke.Logic.K4
import Foundation.Modal.Kripke.AxiomFourN
import Foundation.Modal.Kripke.Filtration
import Foundation.Vorspiel.Relation.Iterate
import Foundation.Vorspiel.Fin.Supplemental
import Foundation.Modal.Logic.Extension

namespace LO.Modal

open Kripke
open Hilbert.Kripke
open IsGeachConfluent

namespace Kripke

protected abbrev FrameClass.weak_trans (n : ℕ+) : FrameClass := { F | IsWeakTrans n _ F.Rel }

end Kripke

namespace Hilbert.K4n.Kripke

variable {n : ℕ+}

instance sound : Sound (Hilbert.K4n n) (Kripke.FrameClass.weak_trans n) := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F F_trans φ rfl;
  apply @validate_axiomFourN_of_weak_transitive n F F_trans;

instance consistent : Entailment.Consistent (Hilbert.K4n n) :=
  consistent_of_sound_frameclass (FrameClass.weak_trans n) $ by
    use whitepoint;
    apply Set.mem_setOf_eq.mpr;
    constructor;
    induction n <;> { simp [WeakTransitive]; tauto; }

instance canonical : Canonical (Hilbert.K4n n) (FrameClass.weak_trans n) := ⟨by
  apply Set.mem_setOf_eq.mpr;
  infer_instance;
⟩

instance complete : Complete (Hilbert.K4n n) (FrameClass.weak_trans n) := inferInstance

end Hilbert.K4n.Kripke


namespace Logic

open Formula
open Entailment
open Kripke

namespace K4n

lemma Kripke.eq_weak_trans_logic (n : ℕ+) : Logic.K4n n = (Kripke.FrameClass.weak_trans n).logic := eq_hilbert_logic_frameClass_logic

lemma eq_K4_K4n_one : Logic.K4n 1 = Logic.K4 := rfl

abbrev counterexampleModel (n : ℕ+) : Kripke.Model := ⟨⟨Fin (n + 2), λ x y => y = x + 1⟩, λ w _ => w = n⟩

lemma NModel.iff_rel_zero {n : ℕ+} {m : Fin (n + 2)} {y : (counterexampleModel n).World} : (0 : counterexampleModel n) ≺^[m] y ↔ y = m := by
  induction m using Fin.induction generalizing y with
  | zero => simp; tauto;
  | succ m ih =>
    constructor;
    . intro h;
      obtain ⟨u, h, rfl⟩ := Rel.iterate.forward.mp h;
      convert @ih (u + 1) |>.mp ?_;
      . sorry;
      . sorry;
    . sorry;

instance : IsWeakTrans (n + 1) _ (counterexampleModel n).Rel := ⟨by
  rintro x y ⟨u, Rxy, Ruy⟩;
  sorry;
⟩

theorem subset_succ : Logic.K4n (n + 1) ⊂ Logic.K4n n := by
  constructor;
  . refine Hilbert.weakerThan_of_dominate_axioms ?_ |>.subset;
    suffices Hilbert.K4n n ⊢! □^[n](.atom 0) ➝ □^[(n + 1)](.atom 0) by
      simp only [Axioms.FourN, PNat.add_coe, PNat.val_ofNat, Box.multibox_succ, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, axiomK!, forall_eq, true_and];
      apply imply_box_distribute'!;
      simpa using this;
    exact axiomFourN!;
  . suffices ∃ φ, Hilbert.K4n n ⊢! φ ∧ ¬Kripke.FrameClass.weak_trans (n + 1) ⊧ φ by
      nth_rewrite 2 [Kripke.eq_weak_trans_logic];
      tauto;
    use (Axioms.FourN n (.atom 0));
    constructor;
    . exact axiomFourN!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use (counterexampleModel n), 0;
      constructor;
      . apply Set.mem_setOf_eq.mpr;
        infer_instance;
      . apply Satisfies.imp_def₂.not.mpr;
        push_neg;
        constructor;
        . apply Satisfies.multibox_def.mpr;
          intro y R0y;
          apply @NModel.iff_rel_zero n n y |>.mp;
          convert R0y;
          sorry;
        . apply Satisfies.multibox_def.not.mpr;
          push_neg;
          use (n + 1);
          constructor;
          . have := @NModel.iff_rel_zero n (n + 1) (n + 1) |>.mpr (by trivial);
            sorry;
          . simp [counterexampleModel, Semantics.Realize, Satisfies];
            sorry;

lemma subset_add : Logic.K4n (n + m) ⊂ Logic.K4n n := by
  induction m with
  | one => exact subset_succ;
  | succ m ih =>
    trans Logic.K4n (n + m);
    . rw [(show n + (m + 1) = n + m + 1 by rfl)];
      apply subset_succ;
    . apply ih;

lemma subset_of_lt (hnm : n < m) : Logic.K4n m ⊂ Logic.K4n n := by
  convert subset_add (n := n) (m := m - n);
  exact PNat.add_sub_of_lt hnm |>.symm;

lemma neq_of_neq (hnm : n ≠ m) : Logic.K4n n ≠ Logic.K4n m := by
  rcases lt_trichotomy n m with h | rfl | h;
  . apply subset_of_lt h |>.ne.symm;
  . contradiction;
  . apply subset_of_lt h |>.ne;

end K4n

/-- There are countable infinite consistent normal logics in `NExt(K4)`. -/
instance : Infinite { L : Logic // L.IsNormal ∧ L.Consistent } := Infinite.of_injective (β := ℕ+) (λ n => ⟨Logic.K4n n, ⟨inferInstance, inferInstance⟩⟩) $ by
  intro i j;
  simp only [Subtype.mk.injEq];
  contrapose!;
  apply K4n.neq_of_neq;

end Logic

end LO.Modal
