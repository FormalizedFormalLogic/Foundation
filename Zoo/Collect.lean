module

public import Zoo.Basic
public import Lean

/-!
# Collecting a zoo

The scan shared by the `zoo_*` executables: every `⪯`, `⪱` and `≊` between two vertices of a
given type stated by a constant of `Foundation`, and the `run` writing their transitive reduction
to a JSON file.

`Foundation` is imported at run time rather than by the executables: linking one against it would
force the whole of `Foundation` and `Mathlib` to be compiled to native code.
-/

@[expose] public section

open Lean Meta

namespace Zoo

/-- Classes stating a relation between two theories, and the relation each of them states. -/
def relationClasses : Array (Name × EdgeType) :=
  #[(`FFL.Entailment.WeakerThan, .sub),
    (`FFL.Entailment.StrictlyWeakerThan, .ssub),
    (`FFL.Entailment.Equiv, .eq)]

/-- The module whose constants are scanned. -/
def rootModule : Name := `Foundation

/-- `vertexType` applied to fresh metavariables, such as `Logic ?α` for `Logic`. -/
def freshVertex (vertexType : Name) : MetaM Expr := do
  let v ← mkConstWithFreshMVarLevels vertexType
  return mkAppN v (← forallMetaTelescope (← inferType v)).1

/-- What the type of a constant says about the vertices of a zoo. -/
inductive Found
  /-- Nothing: the type states no relation between two vertices. -/
  | none
  /-- A relation between two vertices depending on parameters other than those of the vertices. -/
  | parametrised
  | edge (e : Edge)

/--
The relation stated by `type` between two inhabitants of `vertexType`, applied to fresh
metavariables for its parameters.

The conclusion of `type` may be preceded by the parameters of `vertexType` and by instances on
them, such as `[Inhabited α]` for `Logic α`. Any other parameter makes the relation `parametrised`,
unless an endpoint is a bare parameter: such a constant is a lemma about arbitrary vertices.

The head symbol is matched first, so that the unification below only runs on the handful of
constants that can possibly contribute an edge.
-/
def edgeOf? (vertexType : Name) (type : Expr) : MetaM Found := withNewMCtxDepth do
  let .const c _ := type.getForallBody.getAppFn | return .none
  let some (_, edgeType) := relationClasses.find? (·.1 == c) | return .none
  let (params, binderInfos, conclusion) ← forallMetaTelescope type
  let args := conclusion.getAppArgs
  unless args.size ≥ 2 do return .none
  let vertex ← freshVertex vertexType
  unless ← isDefEq (← inferType args[args.size - 2]!) vertex do return .none
  unless ← isDefEq (← inferType args[args.size - 1]!) vertex do return .none
  let a ← instantiateMVars args[args.size - 2]!
  let b ← instantiateMVars args[args.size - 1]!
  if a.isMVar || b.isMVar then return .none
  let paramsOf (e : Expr) : MetaM (Array MVarId) := do getMVars (← instantiateMVars e)
  let vertexParams ← paramsOf vertex
  for p in params, bi in binderInfos do
    if (← paramsOf p).all vertexParams.contains then continue
    let ms ← paramsOf (← inferType p)
    unless bi.isInstImplicit && !ms.isEmpty && ms.all vertexParams.contains do
      return .parametrised
  -- Vertices become node names of a graph, so they must not be broken across lines.
  let render (e : Expr) : MetaM String := return (← ppExpr e).pretty (width := 1000)
  return .edge ⟨← render a, ← render b, edgeType⟩

/--
Every relation between two inhabitants of `vertexType` stated by a constant of the environment,
and the constants skipped for relating vertices that depend on parameters.
-/
def edges (vertexType : Name) : MetaM (Edges × Array Name) := do
  -- Report a renamed class or type instead of quietly producing a zoo with no edge of that kind.
  for (c, _) in relationClasses do discard <| getConstInfo c
  discard <| getConstInfo vertexType
  let mut edges : Edges := ∅
  let mut skipped := #[]
  for (name, ci) in (← getEnv).constants do
    if ci.isUnsafe || name.isInternal then continue
    match ← try edgeOf? vertexType ci.type catch _ => pure .none with
    | .none => pure ()
    | .parametrised => skipped := skipped.push name
    | .edge edge => edges := edges.insert edge
  return (edges, skipped.qsort (·.toString < ·.toString))

/--
Writes the zoo of `vertexType` to the file given as the first argument, or to `defaultOutput`,
and lists the skipped constants on the standard error.
-/
def run (vertexType : Name) (defaultOutput : String) (args : List String) : IO Unit := do
  let output := args.head?.getD defaultOutput
  initSearchPath (← findSysroot)
  -- Required by `importModules (loadExts := true)`, and by the delaborators naming the vertices.
  unsafe enableInitializersExecution
  let env ← importModules (loadExts := true) #[rootModule] {}
  let ((edges, skipped), _, _) ←
    (Zoo.edges vertexType).toIO { fileName := "<zoo>", fileMap := default } { env }
  IO.FS.writeFile output edges.toJson.pretty
  unless skipped.isEmpty do
    IO.eprintln "Skipped, as relating vertices that depend on parameters:"
    for name in skipped do IO.eprintln s!"  {name}"

end Zoo
