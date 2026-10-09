module

public import Foundation.FirstOrder.LK.Basic

/-! # Axiomatizability

## References

- [HP98]
-/

@[expose] public section

namespace FFL.FirstOrder

open _root_.FFL.Entailment

variable {L : Language} {C : Sentence L → Prop} {T U : Theory L}

/-- `U` axiomatizes `T` through sentences satisfying `C`. -/
structure AxiomatizableBy (C : Sentence L → Prop) (T U : Theory L) : Prop where
  forall_mem : ∀ σ ∈ U, C σ
  equiv : T ≊ U

/-- `T` is axiomatized by some theory consisting of sentences satisfying `C`. -/
def Axiomatizable (C : Sentence L → Prop) (T : Theory L) : Prop :=
  ∃ U : Theory L, AxiomatizableBy C T U

end FFL.FirstOrder
