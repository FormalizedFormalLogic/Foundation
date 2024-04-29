import Logic.AutoProver.Prover
import Logic.Propositional.Classical.Basic.Calculus
--import Logic.FirstOrder.Arith.Basic

namespace LO

namespace Propositional.Classical

variable (T : Theory ℕ) {p q r : Formula ℕ}

example : T ⊢! p ⋎ q ⋎ r ⋎ s ⟷ r ⋎ p ⋎ s ⋎ q ⋎ p := by tautology

example : T ⊢! p ⟷ p ⋎ p ⋎ p ⋎ p ⋎ p ⋎ p ⋎ p := by tautology

example : T ⊢! ((p ⟶ q) ⟶ p) ⟶ p := by tautology

example : T ⊢! (r ⟶ p) ⟶ ((p ⟶ q) ⟶ r) ⟶ p := by tautology

example : T ⊢! (~p ⟶ p) ⟶ p := by tautology

example : T ⊢! (p ⟶ q) ⋎ (q ⟶ p) := by tautology

example : T ⊢! (p ⟷ q) ⟷ (~q ⟷ ~p) := by tautology

example (h : T ⊢! p ⟷ q) : T ⊢! ~q ⟷ ~p := by prover [h]

example (h : T ⊢! p ⟷ q) (hp : T ⊢! p) : T ⊢! q := by prover [h, hp]

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
