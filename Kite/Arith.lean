import Kite.Basic
import Foundation.FirstOrder.Arith.Basic
-- import Foundation.FirstOrder.Incompleteness.StandardProvability.FormalizedArithmetic

open Lean Meta Qq Elab Command
open LO.FirstOrder

namespace Kite

def isMatch (ci : ConstantInfo) : MetaM (Option Edge) := withNewMCtxDepth do
  match ← inferTypeQ ci.type with
  | ⟨1, ~q(Prop), ~q(LO.Entailment.StrictlyWeakerThan (S := Theory ℒₒᵣ) (T := Theory ℒₒᵣ) $a $b)⟩ =>
    return some ⟨toString (←Lean.PrettyPrinter.ppExpr a), toString (←Lean.PrettyPrinter.ppExpr b), .ssub⟩
  | ⟨1, ~q(Prop), ~q(LO.Entailment.WeakerThan (S := Theory ℒₒᵣ) (T := Theory ℒₒᵣ) $a $b)⟩ =>
    return some ⟨toString (←Lean.PrettyPrinter.ppExpr a), toString (←Lean.PrettyPrinter.ppExpr b), .sub⟩
  | _ => return none

def findMatches : MetaM Json := do
  let mut edges : Edges := .emptyWithCapacity
  for (name, ci) in (← getEnv).constants do
    if ci.isUnsafe then continue
    if ←name.isBlackListed then continue
    try
      match ←isMatch ci with
      | some i => edges := edges.insert i
      | none => continue
    catch _ => continue

  return edges.toOutput

end Kite


unsafe def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules (loadExts := true) #[`Foundation] {}
  let ⟨s, _, _⟩ ← Kite.findMatches.toIO { fileName := "<compiler>", fileMap := default } { env := env }
  IO.FS.writeFile "Kite/arith.json" s.pretty
