import Foundation.Modal.Logic.Extension
import Foundation.Modal.Maximal.Unprovability
import Mathlib.Data.ENat.Basic

namespace LO.Modal

open Logic

instance : Modal.GL.IsNormal where

variable {n : ℕ∞}

protected def GLPlusBoxBot (n : ℕ∞) : Logic ℕ :=
  match n with
  | .some n => sumQuasiNormal Modal.GL {□^[n]⊥}
  | .none   => Modal.GL

instance : (Modal.GLPlusBoxBot n).IsQuasiNormal := by
  match n with
  | .some n | .none =>
    dsimp [Modal.GLPlusBoxBot];
    infer_instance

instance : Modal.GL ⪯ Modal.GLPlusBoxBot n := by
  match n with
  | .some n | .none =>
    dsimp [Modal.GLPlusBoxBot];
    infer_instance;

lemma Logic.GLPlusBoxBot.boxbot {n : ℕ} : (□^[n]⊥) ∈ Modal.GLPlusBoxBot n := by
  apply Logic.sumQuasiNormal.mem₂;
  tauto;

end LO.Modal
