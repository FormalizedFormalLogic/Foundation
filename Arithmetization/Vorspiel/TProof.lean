import Arithmetization.Vorspiel.Vorspiel

namespace LO.FirstOrder

#check LO.FirstOrder.Derivation

variable (L : Language) [(k : ℕ) → DecidableEq (L.Func k)] [(k : ℕ) → DecidableEq (L.Rel k)]

inductive FDerivation : Finset (SyntacticFormula L) → Type _
| axL (Δ) {k} (r : L.Rel k) (v) : Semiformula.rel r v ∈ Δ → Semiformula.nrel r v ∈ Δ → FDerivation Δ
| verum (Δ)    : ⊤ ∈ Δ → FDerivation Δ
| or {Γ Δ} {p q : SyntacticFormula L} : Γ ⊆ insert p (insert q Δ) → FDerivation Γ → p ⋎ q ∈ Δ → FDerivation Δ
| and {Γp Γq Δ} {p q : SyntacticFormula L} :
    Γp ⊆ insert p Δ → Γq ⊆ insert q Δ → FDerivation Γp → FDerivation Γq → p ⋏ q ∈ Δ → FDerivation Δ
| all {Γ Δ p}    : Γ ⊆ insert (Rew.free.hom p) Δ → FDerivation Γ → ∀' p ∈ Δ → FDerivation Δ
| ex {Δ p} (t) : Derivation (p/[t] :: Δ) → Derivation ((∃' p) :: Δ)
| wk {Δ Γ}     : Derivation Δ → Δ ⊆ Γ → Derivation Γ
| cut {Δ p}    : Derivation (p :: Δ) → Derivation (~p :: Δ) → Derivation Δ

end LO.FirstOrder
