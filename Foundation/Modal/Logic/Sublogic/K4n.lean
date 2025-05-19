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
      simp only [Axioms.Modal.FourN, PNat.add_coe, PNat.val_ofNat, Box.multibox_succ, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, axiomK!, forall_eq, true_and];
      apply imply_box_distribute'!;
      simpa using this;
    exact axiomFourN!;
  . suffices ∃ φ, Hilbert.K4n n ⊢! φ ∧ ¬Kripke.FrameClass.weak_trans (n + 1) ⊧ φ by
      nth_rewrite 2 [Kripke.eq_weak_trans_logic];
      simpa;
    use (Axioms.Modal.FourN n (.atom 0));
    constructor;
    . exact axiomFourN!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Kripke.Model := ⟨⟨ℕ, λ x y => x ≤ n + 1 ∧ y ≤ n + 1 → y = x + 1⟩, λ w _ => w ≠ n + 1⟩;
      have hM : ∀ {x y : ℕ}, x ≤ n + 1 ∧ y ≤ n + 1 → ∀ {m : ℕ+}, Rel.iterate M.Rel m x y ↔ y = x + m := by
        rintro x y ⟨hx, hy⟩ m;
        induction m generalizing x y with
        | one =>
          simp [M];
          tauto;
        | succ m ih =>
          constructor;
          . intro h;
            sorry;
          . rintro h;
            apply Rel.iterate.forward.mpr;
            sorry;
      use M, 0;
      sorry;
      /-
      constructor;
      . refine ⟨?_⟩;
        rintro x y Rxy;
        have : y = x + ↑↑(n + 2) := @hM x y (n + 2) |>.mp $ by
          obtain ⟨u, Rxu, Ruy⟩ := Rxy;
          use u;
          exact ⟨Rxu, Ruy⟩;
        have : y.1 < n + 2 := y.2;

        apply hM.mpr;
        simp at this;
        sorry;
      . apply Satisfies.imp_def₂.not.mpr;
        push_neg;
        constructor;
        . apply Satisfies.multibox_def.mpr;
          intro y R0y;
          simp [Semantics.Realize, Satisfies, M];
          replace R0y := hM.mp R0y;
          subst R0y;
          sorry;
        . apply Satisfies.multibox_def.not.mpr;
          push_neg;
          use (n + 1);
          constructor;
          . apply @hM 0 (n + 1) (n + 1) |>.mpr;
            sorry;
          . simp [Semantics.Realize, Satisfies, M];
      induction n with
      | one =>
        constructor;
        . refine ⟨?_⟩;
          intro x y z;
          simp_all;
          sorry;
        . apply Satisfies.imp_def₂.not.mpr;
          push_neg;
          constructor;
          . rintro y rfl;
            simp [Satisfies, M];
            trivial;
          . apply Satisfies.box_def.not.mpr;
            push_neg;
            use 1;
            constructor;
            . tauto;
            . apply Satisfies.box_def.not.mpr;
              push_neg;
              use 2;
              constructor;
              . tauto;
              . tauto;
      | succ n ih =>
        sorry;
      use M, 0;
      constructor;
      . refine ⟨?_⟩;

        sorry;
      . apply Satisfies.imp_def₂.not.mpr;
        push_neg;
        constructor;
        . apply Satisfies.multibox_def.mpr
          intro x R0x;
          simp [Semantics.Realize, Satisfies];
          sorry;
        . apply Satisfies.multibox_def.not.mpr;
          push_neg;
          use (n + 1);
          constructor;
          . induction n with
            | one => simp; tauto;
            | succ n ih =>
              have := @Rel.iterate.comp (x := 0) (y := n) (R := M.Rel) (n := n) (m := 2) |>.mp;
              sorry;
          . simp [M, Semantics.Realize, Satisfies];
      -/

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

/-- There are countable infinite normal logics. -/
instance : Infinite { L : Logic // L.Normal ∧ L.Consistent } := Infinite.of_injective (β := ℕ+) (λ n => ⟨Logic.K4n n, ⟨inferInstance, inferInstance⟩⟩) $ by
  intro i j;
  simp only [Subtype.mk.injEq];
  contrapose!;
  apply neq_of_neq;

end K4n

end LO.Modal.Logic
