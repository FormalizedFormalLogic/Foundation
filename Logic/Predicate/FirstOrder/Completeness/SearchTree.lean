import Logic.Predicate.FirstOrder.Calculus
import Logic.Predicate.FirstOrder.Coding

universe u v

namespace FirstOrder

namespace Derivation

open SubFormula

variable {L : Language.{u}}
  [∀ k, DecidableEq (L.func k)] [∀ k, DecidableEq (L.rel k)]
  [∀ k, Encodable (L.func k)] [∀ k, Encodable (L.rel k)]

def decomp (s : Finset (SyntacticTerm L)) :
  SyntacticFormula L → Finset (SyntacticFormula L) → Set (Finset $ SyntacticFormula L)
| rel _ _,  Γ => {Γ}
| nrel _ _, Γ => {Γ}
| ⊤,        _ => ∅
| ⊥,        Γ => {Γ}
| p ⋏ q,    Γ => { insert p Γ, insert q Γ }
| p ⋎ q,    Γ => { insert q (insert p Γ) }
| ∀' p,     Γ => { insert (SubFormula.free p) (shifts Γ) }
| ∃' p,     Γ => { s.image (subst · p) ∪ Γ }

def IsTerminal (Δ : Finset (SyntacticFormula L)) : Prop :=
  ∃ (k : ℕ) (r : L.rel k) (v : Fin k → SyntacticTerm L), rel r v ∈ Δ ∧ nrel r v ∈ Δ

inductive SearchTreeAux (i : ℕ) : Finset (SyntacticFormula L) → Finset (SyntacticFormula L) → Prop
| decomp : ∀ (Γ₁ : Finset (SyntacticFormula L)) (Γ₂ : Finset (SyntacticFormula L))
    (p : SyntacticFormula L) (hp : p ∈ Γ₁) (hi : p.index = i.unpair.fst),
    sigma.mk m₂ Γ₂ ∈ decomp i.unpair.snd p Γ₁ → search_tree_decomp Γ₂ Γ₁
| none : ∀ {m} (Γ : finset (bounded_formula L m)) 
    (hi : ∀ p ∈ Γ, subformula.index p ≠ i.unpair.fst),
    search_tree_decomp Γ Γ

#check decomp

end Derivation

end FirstOrder