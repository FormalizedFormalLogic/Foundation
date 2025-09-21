import Foundation.Modal.Logic.SumQuasiNormal
import Foundation.Modal.Maximal.Unprovability
import Mathlib.Data.ENat.Basic
import Foundation.Modal.Kripke.Logic.GL.Completeness


namespace LO.Modal

open Logic

variable {n : ℕ∞}

protected def GLPlusBoxBot (n : ℕ∞) :=
  match n with
  | .some n => Modal.GL.sumQuasiNormal {□^[n]⊥}
  | .none   => Modal.GL

instance : (Modal.GLPlusBoxBot n).IsQuasiNormal := by
  dsimp [Modal.GLPlusBoxBot];
  split <;> infer_instance;

instance : Modal.GL ⪯ Modal.GLPlusBoxBot n := by
  dsimp [Modal.GLPlusBoxBot];
  split <;> infer_instance;

@[simp]
lemma Logic.GLPlusBoxBot.boxbot {n : ℕ} : Modal.GLPlusBoxBot n ⊢! (□^[n]⊥) := by
  apply Logic.sumQuasiNormal.mem₂!;
  tauto;

lemma iff_provable_GLPlusBoxBot_provable_GL {n : ℕ} {φ} : Modal.GLPlusBoxBot n ⊢! φ ↔ Modal.GL ⊢! (□^[n]⊥) ➝ φ := by
  constructor;
  . intro h;
    induction h using sumQuasiNormal.rec! with
    | mem₁ h => cl_prover [h]
    | mem₂ h => simp_all [Logic.iff_provable];
    | mdp ihφψ ihφ => cl_prover [ihφψ, ihφ];
    | subst ihφ => simpa using Logic.subst! _ ihφ;
  . intro h;
    replace h : Modal.GLPlusBoxBot n ⊢! (□^[n]⊥) ➝ φ := sumQuasiNormal.mem₁! h;
    exact h ⨀ (by simp);

@[simp] lemma eq_GLPlusBoxBot_omega_GL : (Modal.GLPlusBoxBot ⊤) = Modal.GL := by simp [Modal.GLPlusBoxBot];


section

open LO.Entailment LO.Modal.Entailment

lemma Logic.GLPlusBoxBot.weakerThan_succ {n : ℕ} : (Modal.GLPlusBoxBot (n + 1)) ⪯ (Modal.GLPlusBoxBot n) := by
  apply weakerThan_iff.mpr;
  intro φ;
  suffices Modal.GL ⊢! □^[(n + 1)]⊥ ➝ φ → Modal.GL ⊢! □^[n]⊥ ➝ φ by
    simpa [
      (show Modal.GLPlusBoxBot (↑n + 1) = Modal.GLPlusBoxBot ↑(n + 1) by simp),
      iff_provable_GLPlusBoxBot_provable_GL
    ];
  intro h;
  apply C!_trans ?_ h;
  suffices Modal.GL ⊢! □^[n]⊥ ➝ □^[n](□⊥) by simpa [Function.iterate_succ_apply]
  apply imply_multibox_distribute'!;
  cl_prover;

lemma Logic.GLPlusBoxBot.weakerThan_add {n k : ℕ} : (Modal.GLPlusBoxBot (n + k)) ⪯ (Modal.GLPlusBoxBot n) := by
  induction k with
  | zero => simp [Modal.GLPlusBoxBot];
  | succ k ih =>
    trans (Modal.GLPlusBoxBot (n + k));
    . apply Logic.GLPlusBoxBot.weakerThan_succ;
    . assumption;

lemma Logic.GLPlusBoxBot.weakerThan_lt {n m : ℕ} (hmn : m > n) : (Modal.GLPlusBoxBot m) ⪯ (Modal.GLPlusBoxBot n) := by
  rw [(show m = n + (m - n) by omega)];
  apply Logic.GLPlusBoxBot.weakerThan_add;

end

end LO.Modal
