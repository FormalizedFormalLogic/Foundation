import Foundation.Meta.Kite.Modal

open Lean
open Lean.Meta

unsafe def main : IO Unit := do
  withImportModules #[Import.mk `Foundation false] {} 0 fun env => do
    let ⟨s, _, _⟩ ← LO.Meta.Kite.Modal.kite.toStringM.toIO
      { fileName := "<compiler>", fileMap := default }
      { env := env }
    IO.FS.writeFile ("pages/kites/modal.json") s
