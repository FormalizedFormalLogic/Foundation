module

public import Zoo.Basic
public import Lean

/-!
# Arithmetic theory zoo

Executable collecting every `⪯`, `⪱` and `≊` between two closed `ArithmeticTheory`s stated by a
constant of `Foundation`, and writing their transitive reduction to a JSON file.

`Foundation` is imported at run time rather than by this module: linking an executable against it
would force the whole of `Foundation` and `Mathlib` to be compiled to native code.
-/

@[expose] public section

open Lean Meta

namespace Zoo

/-- Classes stating a relation between two theories, and the relation each of them states. -/
def relationClasses : Array (Name × EdgeType) :=
  #[(`LO.Entailment.WeakerThan, .sub),
    (`LO.Entailment.StrictlyWeakerThan, .ssub),
    (`LO.Entailment.Equiv, .eq)]

/-- The module whose constants are scanned, and the type whose inhabitants are the vertices. -/
def rootModule : Name := `Foundation

/-- Type of the theories the zoo is about. -/
def vertexType : Name := `LO.FirstOrder.ArithmeticTheory

/--
The relation stated by `type`, if it relates two theories of type `vertexType`.

The head symbol is matched first, so that the unification below only runs on the handful of
constants that can possibly contribute an edge.
-/
def edgeOf? (vertex : Expr) (type : Expr) : MetaM (Option Edge) := withNewMCtxDepth do
  let .const c _ := type.getAppFn | return none
  let some (_, edgeType) := relationClasses.find? (·.1 == c) | return none
  let args := type.getAppArgs
  unless args.size ≥ 2 do return none
  let a := args[args.size - 2]!
  let b := args[args.size - 1]!
  unless ← isDefEq (← inferType a) vertex do return none
  unless ← isDefEq (← inferType b) vertex do return none
  -- Vertices become node names of a graph, so they must not be broken across lines.
  let render (e : Expr) : MetaM String := return (← ppExpr e).pretty (width := 1000)
  return some ⟨← render a, ← render b, edgeType⟩

/-- Every relation between two theories stated by a constant of the environment. -/
def edges : MetaM Edges := do
  let vertex ← mkConstWithLevelParams vertexType
  let mut edges : Edges := ∅
  for (name, ci) in (← getEnv).constants do
    if ci.isUnsafe || name.isInternal then continue
    let edge? ← try edgeOf? vertex ci.type catch _ => pure none
    if let some edge := edge? then edges := edges.insert edge
  return edges

end Zoo

public def main (args : List String) : IO Unit := do
  let output := args.head?.getD "Zoo/arithmetic.json"
  initSearchPath (← findSysroot)
  -- Required by `importModules (loadExts := true)`, and by the delaborators naming the vertices.
  unsafe enableInitializersExecution
  let env ← importModules (loadExts := true) #[Zoo.rootModule] {}
  let (edges, _, _) ← Zoo.edges.toIO { fileName := "<zoo>", fileMap := default } { env }
  IO.FS.writeFile output edges.toJson.pretty
