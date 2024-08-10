import Arithmetization.Vorspiel.Lemmata
import Arithmetization.Vorspiel.Graph
import Logic.FirstOrder.Arith.StrictHierarchy

namespace LO.FirstOrder

variable {L : Language} {V : Type*} [Structure L V]

def Defined {k} (R : (Fin k → V) → Prop) (p : Semisentence L k) : Prop :=
  ∀ v, R v ↔ Semiformula.Evalbm V v p

def DefinedWithParam {k} (R : (Fin k → V) → Prop) (p : Semiformula L V k) : Prop :=
  ∀ v, R v ↔ Semiformula.Evalm V v id p

lemma Defined.iff {k} {R : (Fin k → V) → Prop} {p : Semisentence L k} (h : Defined R p) (v) :
    Semiformula.Evalbm V v p ↔ R v := (h v).symm

lemma DefinedWithParam.iff {k} {R : (Fin k → V) → Prop} {p : Semiformula L V k} (h : DefinedWithParam R p) (v) :
    Semiformula.Evalm V v id p ↔ R v := (h v).symm

variable (L)

def Definable {k} (C : Semisentence L k → Prop) (R : (Fin k → V) → Prop) : Prop :=
  ∃ p, C p ∧ Defined R p

def DefinableWithParam {k} (C : Semiformula L V k → Prop) (R : (Fin k → V) → Prop) : Prop :=
  ∃ p, C p ∧ DefinedWithParam R p

end LO.FirstOrder
