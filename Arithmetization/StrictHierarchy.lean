import Arithmetization.Vorspiel.Vorspiel

namespace LO.FirstOrder

variable {L : Language} [L.LT] {μ : Type v}

namespace Arith

inductive StrictHierarchy : Polarity → ℕ → {n : ℕ} → Semiformula L μ n → Prop
  | zero (b s n) {p : Semiformula L μ n}             : Hierarchy Σ 0 p → StrictHierarchy b s p
  | and {b s n} {p q : Semiformula L μ n}            : StrictHierarchy b s p → StrictHierarchy b s q → StrictHierarchy b s (p ⋏ q)
  | or {b s n} {p q : Semiformula L μ n}             : StrictHierarchy b s p → StrictHierarchy b s q → StrictHierarchy b s (p ⋎ q)
  | ex {s n} {p : Semiformula L μ (n + 1)}           : StrictHierarchy Σ (s + 1) p → StrictHierarchy Σ (s + 1) (∃' p)
  | all {s n} {p : Semiformula L μ (n + 1)}          : StrictHierarchy Π (s + 1) p → StrictHierarchy Π (s + 1) (∀' p)
  | sigma {s n} {p : Semiformula L μ (n + 1)}        : StrictHierarchy Π s p → StrictHierarchy Σ (s + 1) (∃' p)
  | pi {s n} {p : Semiformula L μ (n + 1)}           : StrictHierarchy Σ s p → StrictHierarchy Π (s + 1) (∀' p)
  | dummy_sigma {s n} {p : Semiformula L μ (n + 1)}  : StrictHierarchy Π (s + 1) p → StrictHierarchy Σ (s + 1 + 1) (∀' p)
  | dummy_pi {s n} {p : Semiformula L μ (n + 1)}     : StrictHierarchy Σ (s + 1) p → StrictHierarchy Π (s + 1 + 1) (∃' p)

end Arith

end LO.FirstOrder
