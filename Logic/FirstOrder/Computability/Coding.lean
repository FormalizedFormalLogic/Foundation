import Logic.FirstOrder.Computability.Formula

namespace LO

namespace FirstOrder

variable {L : Language.{u}} {μ : Type v}
  [(k : ℕ) → Encodable (L.Func k)] [(k : ℕ) → Encodable (L.Rel k)] [Encodable μ]

def UTerm.encodable : Encodable (UTerm L μ) := Encodable.ofEquiv (WType (Edge L μ)) (equivW L μ)

def Semiterm.encodable : Encodable (Semiterm L μ n) :=
  letI : Encodable (UTerm L μ) := UTerm.encodable
  Encodable.ofEquiv { t : UTerm L μ // t.bv ≤ n } UTerm.subtEquiv

def UFormula.encodable : Encodable (UFormula L μ) :=
  letI : Encodable (UTerm L μ) := UTerm.encodable
  Encodable.ofEquiv (WType (UFormula.Edge L μ)) (equivW L μ)

def Semiformula.encodable : Encodable (Semiformula L μ n) :=
  letI : Encodable (UFormula L μ) := UFormula.encodable
  Encodable.ofEquiv { p : UFormula L μ // p.bv ≤ n } UFormula.subfEquiv

end FirstOrder

end LO
