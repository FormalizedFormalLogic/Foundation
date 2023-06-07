import Logic.Predicate.FirstOrder.Semantics

namespace FirstOrder

namespace Arith
open Language

namespace Semantics

instance StandardModel : Structure oring ℕ where
  func := fun f =>
    match f with
    | ORingFunc.zero => fun _ => 0
    | ORingFunc.one  => fun _ => 1
    | ORingFunc.add  => fun v => v 0 + v 1
    | ORingFunc.mul  => fun v => v 0 * v 1
  rel := fun r =>
    match r with
    | ORingRel.eq => fun v => v 0 = v 1
    | ORingRel.lt => fun v => v 0 < v 1

variable (L : Language.{u}) [L.ORing]

structure Cut (M : Type w) [s : Structure L M] where
  domain : Set M
  closedSucc : ∀ x ∈ domain, (ᵀ“#0 + 1”).bVal s ![x] ∈ domain
  closedLt : ∀ x y : M, SubFormula.BVal s ![x, y] “#0 < #1” → y ∈ domain → x ∈ domain

structure ClosedCut (M : Type w) [s : Structure L M] extends Structure.ClosedSubset L M where
  closedLt : ∀ x y : M, SubFormula.BVal s ![x, y] “#0 < #1” → y ∈ domain → x ∈ domain

end Semantics

end Arith

end FirstOrder