import Foundation.Propositional.Logic.Basic

open Lean Meta Qq Elab Command
open LO.Propositional

namespace Kite

inductive EdgeType
| eq
| ssub
| sub

instance : ToString EdgeType := ⟨λ t =>
  match t with
  | .eq => "eq"
  | .ssub => "ssub"
  | .sub => "sub"
⟩

structure Edge where
  a: String
  b: String
  type: EdgeType

def isMatch (ci : ConstantInfo) : MetaM (Option Edge) := withNewMCtxDepth do
  match ← inferTypeQ ci.type with
  | ⟨1, ~q(Prop), ~q(@HasSSubset.SSubset Logic _ $a $b)⟩ => return some ⟨a.constName.toString, b.constName.toString, .ssub⟩
  -- | ⟨1, ~q(Prop), ~q(@HasSubset.Subset Logic _ $a $b)⟩ => return some (.ext, a, b)
  -- | ⟨1, ~q(Prop), ~q(($a : Logic) = $b)⟩ => return some (.ext, a, b)
  | _ => return none

def findMatches : MetaM Json := do
  let mut edges : Array Edge := #[]
  for (name, ci) in (← getEnv).constants do
    if ci.isUnsafe then continue
    if ←name.isBlackListed then continue
    try
      match ←isMatch ci with
      | some i => edges := edges.push i
      | none => continue
    catch _ => continue

  return Json.arr $ edges.map $ (λ ⟨a, b, t⟩ => Json.mkObj [
    ("from", s!"{a}"),
    ("to", s!"{b}"),
    ("type", s!"{t}")
  ])

end Kite

unsafe def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules (loadExts := true) #[`Foundation] {}
  let ⟨s, _, _⟩ ← Kite.findMatches.toIO { fileName := "<compiler>", fileMap := default } { env := env }
  IO.FS.writeFile "Kite/propositional_kite.json" s.pretty
