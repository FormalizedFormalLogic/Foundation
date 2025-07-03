import Foundation.Propositional.Logic.Basic
import Kite.Basic

open Lean Meta Qq Elab Command PrettyPrinter
open LO.Propositional

namespace Kite

def isMatch (ci : ConstantInfo) : MetaM (Option Edge) := withNewMCtxDepth do
  match ← inferTypeQ ci.type with
  | ⟨1, ~q(Prop), ~q(LO.Entailment.StrictlyWeakerThan (S := Logic ℕ) (T := Logic ℕ) $a $b)⟩ =>
    return some ⟨s!"{←PrettyPrinter.ppExpr a}", s!"{←PrettyPrinter.ppExpr b}", .ssub⟩
  | ⟨1, ~q(Prop), ~q(LO.Entailment.WeakerThan (S := Logic ℕ) (T := Logic ℕ) $a $b)⟩ =>
    return some ⟨s!"{←PrettyPrinter.ppExpr a}", s!"{←PrettyPrinter.ppExpr b}", .sub⟩
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
  IO.FS.writeFile "Kite/propositional.json" s.pretty
