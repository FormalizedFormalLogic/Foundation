import Foundation.FirstOrder.Q.Basic
import Foundation.FirstOrder.PeanoMinus.Basic
import Mathlib.Data.ENat.Basic

namespace LO

open FirstOrder FirstOrder.Arithmetic


namespace RobinsonQ

namespace Countermodel

namespace ENat

variable {a b : ℕ∞} {m n : ℕ}

local instance : ORingStruc ENat where
  add := (· + ·)
  mul := (· * ·)
  lt := (· < ·)

end ENat

set_option linter.flexible false in
instance : ℕ∞ ⊧ₘ* 𝐐 := ⟨by
  intro σ h;
  rcases h <;> simp [models_def];
  case equal h =>
    have : ℕ∞ ⊧ₘ* (𝐄𝐐 : ArithmeticTheory) := inferInstance
    exact modelsTheory_iff.mp this h
  case addSucc =>
    intro f;
    generalize f 0 = m;
    generalize f 1 = n;
    match m, n with
    | ⊤, _ | _, ⊤ => simp;
    | .some m, .some n => rfl;
  case mulSucc =>
    intro f;
    generalize f 0 = m;
    generalize f 1 = n;
    cases m <;> cases n;
    case coe.top m => match m with | 0 | m + 1 => simp;
    case coe.coe m n => rfl;
    all_goals simp;
  case succInj =>
    intro f;
    generalize f 0 = m;
    generalize f 1 = n;
    cases m <;> cases n;
    case coe.coe m n =>
      intro h;
      simpa using ENat.coe_inj.mp h
    all_goals tauto;
⟩

end Countermodel

lemma unprovable_neSucc : 𝐐 ⊬ “x | x + 1 ≠ x” := unprovable_of_countermodel (M := ℕ∞) (fun x ↦ ⊤) _ (by simp)

end RobinsonQ


namespace PeanoMinus

variable {M : Type*} [ORingStruc M] [M ⊧ₘ* 𝐏𝐀⁻]

instance : M ⊧ₘ* 𝐐 := modelsTheory_iff.mpr <| by
  intro φ h
  rcases h
  case equal h =>
    have : M ⊧ₘ* (𝐄𝐐 : ArithmeticTheory) := inferInstance
    exact modelsTheory_iff.mp this h
  case addSucc h =>
    suffices ∀ (f : ℕ → M), f 0 + (f 1 + 1) = f 0 + f 1 + 1 by simpa [models_iff];
    intro f;
    rw [add_assoc]
  case mulSucc h =>
    suffices ∀ (f : ℕ → M), f 0 * (f 1 + 1) = f 0 * f 1 + f 0 by simpa [models_iff];
    intro f;
    calc
      f 0 * (f 1 + 1) = (f 0 * f 1) + (f 0 * 1) := by rw [mul_add_distr]
      _               = (f 0 * f 1) + f 0       := by rw [mul_one]
    ;
  all_goals simp [models_iff];

instance : 𝐐 ⪯ 𝐏𝐀⁻ := oRing_weakerThan_of.{0} _ _ fun _ _ _ ↦ inferInstance

instance : 𝐐 ⪱ 𝐏𝐀⁻ := Entailment.StrictlyWeakerThan.of_unprovable_provable RobinsonQ.unprovable_neSucc $ by
  apply oRing_provable_of.{0};
  intro _ _ _;
  simp [models_iff];


end PeanoMinus

end LO
