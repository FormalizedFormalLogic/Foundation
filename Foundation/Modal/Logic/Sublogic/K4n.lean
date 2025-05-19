import Foundation.Modal.Logic.WellKnown

namespace LO.Modal.Logic

open Formula
open Entailment
open Entailment.Modal
open Kripke

namespace K4n

variable {n m : ℕ+}

lemma eq_K4_K4n_one : Logic.K4n 1 = Logic.K4 := rfl

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
      simpa;
    use (Axioms.FourN n (.atom 0));
    constructor;
    . exact axiomFourN!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Kripke.Model := ⟨⟨Fin (n + 2), λ x y => y = x.castSucc⟩, λ w _ => w < Fin.last (n + 1)⟩;
      have hM : ∀ {y m : M}, (0 : M) ≺^[m] y ↔ y = m := by
        rintro y m;
        induction m using Fin.induction generalizing y with
        | zero =>
          simp [M];
          tauto;
        | succ m ih =>
          constructor;
          . intro h;
            sorry;
          . sorry;
      use M, 0;
      constructor;
      . refine ⟨?_⟩;
        rintro x y Rxy;
        induction x using Fin.induction generalizing y with
        | zero =>
          apply hM (m := ⟨n + 1, by omega⟩) |>.mpr;
          obtain ⟨u, Rxu, Ruy⟩ := Rel.iterate.forward.mp Rxy;
          rw [Ruy]
          simp only [Fin.coe_castSucc, Fin.cast_val_eq_self];
          rw [hM (m := ⟨n + 1, by omega⟩) |>.mp Rxu];
        | succ x ih =>

          sorry;
      . apply Satisfies.imp_def₂.not.mpr;
        push_neg;
        constructor;
        . apply Satisfies.multibox_def.mpr;
          intro x R0x;
          rw [@hM (y := x) (m := ⟨n, by omega⟩) |>.mp ?_];
          . apply Fin.lt_last;
          . simpa using R0x;
        . apply Satisfies.multibox_def.not.mpr
          push_neg;
          use Fin.last (n + 1);
          constructor;
          . apply hM (y := Fin.last (n + 1)) (m := ⟨(n + 1), by omega⟩) |>.mpr;
            tauto;
          . simp [M, Satisfies, Semantics.Realize];

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

/-- There are countable infinite consistent normal logics in `NExt(K4)`. -/
instance : Infinite { L : Logic // L.Normal ∧ L.Consistent } := Infinite.of_injective (β := ℕ+) (λ n => ⟨Logic.K4n n, ⟨inferInstance, inferInstance⟩⟩) $ by
  intro i j;
  simp only [Subtype.mk.injEq];
  contrapose!;
  apply neq_of_neq;

end K4n

end LO.Modal.Logic
