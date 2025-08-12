import Foundation.Modal.Logic.Extension
import Foundation.Modal.Maximal.Unprovability
import Mathlib.Data.ENat.Basic
import Foundation.Modal.Kripke.Logic.GL.Completeness

namespace LO.Modal.Axioms

variable {F : Type*} [BasicModalLogicalConnective F]

protected abbrev BoxBot (n : ℕ∞) : F :=
  match n with
  | .some n => □^[n]⊥
  | .none   => ⊤

@[simp]
lemma BoxBot.eq_omega : (Axioms.BoxBot ⊤ : F) = ⊤ := rfl

@[simp]
lemma BoxBot.subst {s : Substitution α} : (Axioms.BoxBot n)⟦s⟧ = (Axioms.BoxBot n) := by cases n <;> simp;

end LO.Modal.Axioms


namespace LO.Modal

open Logic

variable {n : ℕ∞}

protected def GLPlusBoxBot (n : ℕ∞) : Logic ℕ := sumQuasiNormal Modal.GL { (Modal.Axioms.BoxBot n) }

instance : (Modal.GLPlusBoxBot n).IsQuasiNormal := by
  dsimp [Modal.GLPlusBoxBot];
  infer_instance;

instance : Modal.GL ⪯ Modal.GLPlusBoxBot n := by
  dsimp [Modal.GLPlusBoxBot];
  infer_instance;

@[simp]
lemma Logic.GLPlusBoxBot.boxbot : Modal.GLPlusBoxBot n ⊢! (Modal.Axioms.BoxBot n) := by
  apply Logic.sumQuasiNormal.mem₂!;
  tauto;

lemma iff_provable_GLBB_provable_GL {n : ℕ∞} {φ} : Modal.GLPlusBoxBot n ⊢! φ ↔ Modal.GL ⊢! (Modal.Axioms.BoxBot n) ➝ φ := by
  constructor;
  . intro h;
    induction h using sumQuasiNormal.rec! with
    | mem₁ h => cl_prover [h]
    | mem₂ h => simp_all;
    | mdp ihφψ ihφ => cl_prover [ihφψ, ihφ];
    | subst ihφ => simpa using Logic.subst! _ ihφ;
  . intro h;
    replace h : Modal.GLPlusBoxBot n ⊢! (Modal.Axioms.BoxBot n) ➝ φ := sumQuasiNormal.mem₁! h;
    exact h ⨀ Logic.GLPlusBoxBot.boxbot;

@[simp]
lemma eq_GLBB_omega_GL : (Modal.GLPlusBoxBot ⊤ : Logic ℕ) = Modal.GL := by
  ext φ;
  suffices Modal.GLPlusBoxBot ⊤ ⊢! φ ↔ Modal.GL ⊢! φ by simpa;
  apply Iff.trans iff_provable_GLBB_provable_GL;
  constructor <;> . intro h; cl_prover [h];

end LO.Modal
