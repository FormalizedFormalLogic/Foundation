import Foundation.Meta.Kite.Modal
import Batteries.Lean.IO.Process

open Lean
open Lean.Meta

unsafe def main : IO Unit := do
  -- TODO: `./scripts/`と書かなくとも同じディレクトリに出力されるようにしたい．
  let jsonPath := "scripts/modal_kite.json"
  let typstPath := "scripts/modal_kite.typ"
  let pngPath := "scripts/modal_kite.png"

  searchPathRef.set compile_time_search_path%
  withImportModules #[Import.mk `Foundation false] {} 0 fun env => do
    let ⟨s, _, _⟩ ← LO.Meta.Kite.Modal.kite.toStringM.toIO
      { fileName := "<compiler>", fileMap := default }
      { env := env }
    _ ← IO.FS.writeFile jsonPath s

  _ ← IO.Process.runCmdWithInput "typst" #["compile", "--format", "png", typstPath, pngPath]
