import Foundation.FirstOrder.Completeness.Completeness
import Mathlib.SetTheory.Cardinal.Basic

/-! # Löwenheim-Skolem theorems -/

namespace LO.FirstOrder

variable {L : Language} [L.Encodable]

open Classical

namespace Completeness

lemma models_of_consistent {T : Theory L} (con : Entailment.Consistent T) : Model T [] ⊧ₘ* T :=
  have : ¬WellFounded (SearchTree.Lt T []) := by
    intro wf
    have : Entailment.Inconsistent T :=
      Entailment.inconsistent_iff_provable_bot.mpr
      <| Tait.provable_bot_iff_derivable_nil.mp ⟨syntacticMainLemmaTop wf⟩
    exact Entailment.not_consistent_iff_inconsistent.mpr this con
  Model.models this

end Completeness

namespace Structure

variable (L) (M : Type*) [Structure L M] [Nonempty M]

abbrev CountableLS : Type _ := Completeness.Model (theory L M) []

lemma CountableLS.models : CountableLS L M ⊧ₘ* theory L M :=
  Completeness.models_of_consistent <| consistent_of_satidfiable <| theory_satisfiable

/-- Downward Löwenheim-Skolem theorem for countable language -/
instance CountableLS.equiv : CountableLS L M ≡ₑ[L] M where
  models := by
    intro φ
    by_cases hφ : φ ∈ theory L M
    · have : M ⊧ₘ φ := by simpa using hφ
      have : CountableLS L M ⊧ₘ φ := modelsTheory_iff.mp (CountableLS.models L M) hφ
      simp_all
    · have hφ : ∼φ ∈ theory L M := by simpa using hφ
      have : ¬M ⊧ₘ φ := by simpa
      have : ¬CountableLS L M ⊧ₘ φ := by simpa using modelsTheory_iff.mp (CountableLS.models L M) hφ
      simp_all

instance countable : Countable (CountableLS L M) := Encodable.countable

instance infinite : Infinite (CountableLS L M) := Infinite.of_injective (fun x : ℕ ↦ &x) fun x y ↦ (by simp)

open Cardinal

/-- Downward Löwenheim-Skolem theorem for countable language -/
theorem CountableLS.card : #(CountableLS L M) = ℵ₀ := mk_eq_aleph0 _

end Structure

end LO.FirstOrder
