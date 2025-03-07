import Kite.Generator
import Kite.Arith
import Kite.Modal

open Lean
open Lean.Meta

unsafe
def main : IO Unit := do
  searchPathRef.set compile_time_search_path%
  withImportModules #[Import.mk `Kite false] {} 0 fun env => do
    let ⟨s, _, _⟩ ← LO.Meta.Kite.Modal.kite.toStringM.toIO { fileName := "<compiler>", fileMap := default } { env := env }
    IO.FS.writeFile ("pages/kites/modal.json") s
  withImportModules #[Import.mk `Kite false] {} 0 fun env => do
    let ⟨s, _, _⟩ ← LO.Meta.Kite.Arith.kite.toStringM.toIO { fileName := "<compiler>", fileMap := default } { env := env }
    IO.FS.writeFile ("pages/kites/arith.json") s
