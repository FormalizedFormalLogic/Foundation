import Foundation.Modal.Logic.Extension
import Foundation.Modal.Maximal.Unprovability
import Mathlib.Data.ENat.Basic


namespace LO.Modal.Axioms

variable {F : Type*} [BasicModalLogicalConnective F]

protected abbrev BoxBot (n : ℕ∞) : F :=
  match n with
  | .some n => □^[n]⊥
  | .none   => ⊤

@[simp]
lemma BoxBot.eq_omega : (Axioms.BoxBot ⊤ : F) = ⊤ := rfl

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

lemma Logic.GLPlusBoxBot.boxbot : (Modal.Axioms.BoxBot n) ∈ Modal.GLPlusBoxBot n := by
  apply Logic.sumQuasiNormal.mem₂;
  tauto;

@[simp]
lemma GLPlusBoxBot.eq_omega : (Modal.GLPlusBoxBot ⊤ : Logic ℕ) = Modal.GL := by
  ext φ;
  suffices Modal.GLPlusBoxBot ⊤ ⊢! φ ↔ Modal.GL ⊢! φ by simpa;
  constructor;
  . intro h;
    induction h using sumQuasiNormal.rec! with
    | mem₁ h => assumption;
    | mem₂ h => simp_all;
    | mdp ihφψ ihφ => exact ihφψ ⨀ ihφ;
    | subst => apply Logic.subst!; assumption;
  . intro h;
    apply sumQuasiNormal.mem₁!;
    assumption;

end LO.Modal
