import Foundation.Meta.Kite.Arith

open Lean
open Lean.Meta

unsafe def main : IO Unit := do
  withImportModules #[Import.mk `Foundation false] {} 0 fun env => do
    let ⟨s, _, _⟩ ← LO.Meta.Kite.Arith.kite.toStringM.toIO
      { fileName := "<compiler>", fileMap := default }
      { env := env }
    IO.FS.writeFile ("pages/kites/arith.json") s
