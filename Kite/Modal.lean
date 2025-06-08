import Kite.Basic
import Foundation.Modal.Logic.Basic
-- import Foundation.Modal.Kripke.Logic.S5

open Lean Meta Qq Elab Command
open LO.Modal


namespace Kite

def isMatch (ci : ConstantInfo) : MetaM (Option Edge) := withNewMCtxDepth do
  match ← inferTypeQ ci.type with
  | ⟨1, ~q(Prop), ~q(@HasSSubset.SSubset Logic _ $a $b)⟩ => return some ⟨a.constName.toString, b.constName.toString, .ssub⟩
  -- | ⟨1, ~q(Prop), ~q(@HasSubset.Subset Logic _ $a $b)⟩ => return some (.ext, a, b)
  -- | ⟨1, ~q(Prop), ~q(($a : Logic) = $b)⟩ => return some (.ext, a, b)
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

  return Json.arr $ edges.reductTrans.map $ (λ ⟨a, b, t⟩ => Json.mkObj [
    ("from", s!"{a}"),
    ("to", s!"{b}"),
    ("type", s!"{t}")
  ])

end Kite


unsafe def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules (loadExts := true) #[`Foundation] {}
  let ⟨s, _, _⟩ ← Kite.findMatches.toIO { fileName := "<compiler>", fileMap := default } { env := env }
  IO.FS.writeFile "Kite/modal.json" s.pretty
