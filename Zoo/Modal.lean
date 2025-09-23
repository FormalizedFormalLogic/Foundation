import Zoo.Basic
import Foundation.Modal.Hilbert.Normal.Basic
-- import Foundation.Modal.Kripke.Logic.S5

open Lean Meta Qq Elab Command
open LO.Modal

namespace Zoo

def isMatch (ci : ConstantInfo) : MetaM (Option Edge) := withNewMCtxDepth do
  match ← inferTypeQ ci.type with
  | ⟨1, ~q(Prop), ~q(LO.Entailment.StrictlyWeakerThan (S := Logic ℕ) (T := Logic ℕ) $a $b)⟩ =>
    return some ⟨toString (←Lean.PrettyPrinter.ppExpr a), toString (←Lean.PrettyPrinter.ppExpr b), .ssub⟩
  | ⟨1, ~q(Prop), ~q(LO.Entailment.WeakerThan (S := Logic ℕ) (T := Logic ℕ) $a $b)⟩ =>
    return some ⟨toString (←Lean.PrettyPrinter.ppExpr a), toString (←Lean.PrettyPrinter.ppExpr b), .sub⟩
  | ⟨1, ~q(Prop), ~q(LO.Entailment.Equiv (S := Logic ℕ) (T := Logic ℕ) $a $b)⟩ =>
    return some ⟨toString (←Lean.PrettyPrinter.ppExpr a), toString (←Lean.PrettyPrinter.ppExpr b), .eq⟩
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
  IO.FS.writeFile "Zoo/modal.json" s.pretty
