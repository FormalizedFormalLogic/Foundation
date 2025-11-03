import Zoo.Basic
import Foundation.FirstOrder.Arithmetic.Basic

open Lean Meta Qq Elab Command
open LO.FirstOrder

namespace Zoo

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

end Zoo


unsafe def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules (loadExts := true) #[`Foundation] {}
  let ⟨s, _, _⟩ ← Zoo.findMatches.toIO { fileName := "<compiler>", fileMap := default } { env := env }
  IO.FS.writeFile "Zoo/Arith.json" s.pretty
