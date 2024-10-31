import Foundation.AutoProver.Prover
import Foundation.Propositional.Classical.Basic.Calculus
--import Foundation.FirstOrder.Arith.Basic

namespace LO

namespace Propositional.Classical

variable (T : Theory ℕ) {φ ψ r : Formula ℕ}

example : T ⊢! φ ⋎ ψ ⋎ r ⋎ s ⭤ r ⋎ φ ⋎ s ⋎ ψ ⋎ φ := by tautology

example : T ⊢! φ ⭤ φ ⋎ φ ⋎ φ ⋎ φ ⋎ φ ⋎ φ ⋎ φ := by tautology

example : T ⊢! ((φ ➝ ψ) ➝ φ) ➝ φ := by tautology

example : T ⊢! (r ➝ φ) ➝ ((φ ➝ ψ) ➝ r) ➝ φ := by tautology

example : T ⊢! (∼φ ➝ φ) ➝ φ := by tautology

example : T ⊢! (φ ➝ ψ) ⋎ (ψ ➝ φ) := by tautology

example : T ⊢! (φ ⭤ ψ) ⭤ (∼ψ ⭤ ∼φ) := by tautology

example (h : T ⊢! φ ⭤ ψ) : T ⊢! ∼ψ ⭤ ∼φ := by prover [h]

example (h : T ⊢! φ ⭤ ψ) (hp : T ⊢! φ) : T ⊢! ψ := by prover [h, hp]

end Propositional.Classical

/-
namespace FirstOrder
open Arith
variable (T : Theory ℒₒᵣ)

example : T ⊢! “1 < 0 → 1 < 0” := by prover

example (h : T ⊢! “¬∀ #0 ≠ 0 → ⊥”) : T ⊢! “∀ #0 ≠ 0” := by prover [h]

end FirstOrder
-/

end LO
