import Lean
import Batteries.Lean.IO.Process
import Foundation
-- import Foundation.Modal.Kripke.Logic.S5

open Lean Meta Qq Elab Command
open LO.Modal

inductive Relation
| eq
| proper_ext
| ext

instance : ToString Relation := ⟨λ t =>
  match t with
  | .eq => "equal"
  | .proper_ext => "proper_extension"
  | .ext => "extension"
⟩

def isMatch (ci : ConstantInfo) : MetaM (Option (Relation × Q(Logic) × Q(Logic))) := withNewMCtxDepth do
  match ← inferTypeQ ci.type with
  | ⟨1, ~q(Prop), ~q(@HasSSubset.SSubset Logic _ $a $b)⟩ => return some (.proper_ext, a, b)
  -- | ⟨1, ~q(Prop), ~q(@HasSubset.Subset Logic _ $a $b)⟩ => return some (.ext, a, b)
  -- | ⟨1, ~q(Prop), ~q(($a : Logic) = $b)⟩ => return some (.ext, a, b)
  | _ => return none

def findMatches : MetaM Json := do
  let mut names : Array ((Q(Logic) × Q(Logic))) := #[]
  for (name, ci) in (← getEnv).constants do
    if ci.isUnsafe then continue
    if ←name.isBlackListed then continue
    try
      match ←isMatch ci with
      | some (.proper_ext, a, b) => names := names.push (⟨a, b⟩)
      | some (.ext, a, b) => names := names.push (⟨a, b⟩)
      | some (.eq, a, b) => names := names.push (⟨a, b⟩)
      | none => continue
    catch _ => continue

  return Json.arr $ names.map $ (λ ⟨a, b⟩ => Json.mkObj [
    ("from", Json.str s!"{a}"),
    ("to", s!"{b}"),
    ("type", Json.str "strict")
  ])

#eval do logInfo (← findMatches).pretty

unsafe def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules (loadExts := true) #[`Foundation] {}
  let action := findMatches
  let ⟨s, _, _⟩ ← action.toIO
    { fileName := "<compiler>", fileMap := default }
    { env := env }
  _ ← IO.FS.writeFile "modal_kite.json" s.pretty
