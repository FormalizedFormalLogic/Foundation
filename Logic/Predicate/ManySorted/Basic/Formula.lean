import Logic.Predicate.ManySorted.Basic.Term

namespace LO

namespace ManySorted

inductive Subformula {S : Type w} (L : Language.{w, u} S) (μ : S → Type v) : ℕ → Type _
  | verum  {n} : Subformula L μ n
  | falsum {n} : Subformula L μ n
  | rel    {n} {arity : ℕ} {aug : Fin arity → S} :
    L.Rel aug → ((i : Fin arity) → Subterm (aug i) L μ n) → Subformula L μ n
  | nrel   {n} {arity : ℕ} {aug : Fin arity → S} :
    L.Rel aug → ((i : Fin arity) → Subterm (aug i) L μ n) → Subformula L μ n
  | and    {n} : Subformula L μ n → Subformula L μ n → Subformula L μ n
  | or     {n} : Subformula L μ n → Subformula L μ n → Subformula L μ n
  | all    {n} : Subformula L μ (n + 1) → Subformula L μ n
  | ex     {n} : Subformula L μ (n + 1) → Subformula L μ n



end ManySorted

end LO
