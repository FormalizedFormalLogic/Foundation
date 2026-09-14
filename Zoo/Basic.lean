module

public import Std.Data.HashMap
public import Std.Data.HashSet
public import Lean.Data.Json

/-!
# Zoo diagrams

A zoo is a directed graph whose vertices are theories and whose edges record how their
provability strengths compare. This module provides the graph, its transitive reduction and
its serialisation to JSON; the edges themselves are collected from a Lean environment by the
executables rooted at the other modules of `Zoo`.
-/

@[expose] public section

open Lean

namespace Zoo

/-- How the two endpoints of an edge of a zoo compare in provability strength. -/
inductive EdgeType
  /-- `⪱`: the source is strictly weaker than the target. -/
  | ssub
  /-- `⪯`: the source is weaker than the target. -/
  | sub
  /-- `≊`: the two endpoints are equivalent. -/
  | eq
deriving BEq, Hashable, Repr, Inhabited

namespace EdgeType

instance : ToString EdgeType where
  toString
    | .ssub => "ssub"
    | .sub  => "sub"
    | .eq   => "eq"

/-- Relation witnessed by an edge of type `t` followed by an edge of type `u`. -/
def comp : (t u : EdgeType) → EdgeType
  | .eq,   u     => u
  | t,     .eq   => t
  | .sub,  .sub  => .sub
  | .ssub, _     => .ssub
  | _,     .ssub => .ssub

/-- Whether a relation of type `t` entails one of type `u`. -/
def entails : (t u : EdgeType) → Bool
  | .eq,   .eq   => true
  | .eq,   .sub  => true
  | .ssub, .ssub => true
  | .ssub, .sub  => true
  | .sub,  .sub  => true
  | _,     _     => false

end EdgeType

/-- An edge `⟨a, b, t⟩` records that the theories `a` and `b` are related by `t`. -/
structure Edge where
  src : String
  dst : String
  type : EdgeType
deriving BEq, Hashable, Repr, Inhabited

/-- Lexicographic order, so that a diagram does not depend on hash iteration order. -/
protected def Edge.compare (e₁ e₂ : Edge) : Ordering :=
  (compare e₁.src e₂.src).then <|
    (compare e₁.dst e₂.dst).then (compare (toString e₁.type) (toString e₂.type))

instance : Ord Edge := ⟨Edge.compare⟩

abbrev Edges := Std.HashSet Edge

namespace Edges

/-- Outgoing edges of each vertex. -/
def adjacency (es : Edges) : Std.HashMap String (Array (String × EdgeType)) :=
  es.fold (init := ∅) fun adj e => adj.insert e.src ((adj.getD e.src #[]).push (e.dst, e.type))

/--
For every vertex reachable from `src`, the relations witnessed by some path leading to it.
A vertex carries at most three relations, so the search visits each edge a bounded number of times.
-/
def relationsFrom (es : Edges) (src : String) : Std.HashMap String (Std.HashSet EdgeType) := Id.run do
  let adj := adjacency es
  let mut found : Std.HashMap String (Std.HashSet EdgeType) := ∅
  let mut pending := adj.getD src #[]
  while !pending.isEmpty do
    let (v, t) := pending.back!
    pending := pending.pop
    let ts := found.getD v ∅
    if ts.contains t then continue
    found := found.insert v (ts.insert t)
    for (w, u) in adj.getD v #[] do
      pending := pending.push (w, t.comp u)
  return found

/-- Whether `e` already follows by transitivity from the remaining edges. -/
def isRedundant (es : Edges) (e : Edge) : Bool :=
  (relationsFrom (es.erase e) e.src).getD e.dst ∅ |>.any (EdgeType.entails · e.type)

/-- Transitive reduction: the edges that do not follow from the others. -/
def reduce (es : Edges) : Edges := es.filter fun e => !isRedundant es e

/-- The transitive reduction of `es`, as a JSON array in lexicographic order. -/
def toJson (es : Edges) : Json :=
  .arr <| (reduce es).toArray.qsort (compare · · |>.isLT) |>.map fun e =>
    Json.mkObj [("from", e.src), ("to", e.dst), ("type", toString e.type)]

end Edges

end Zoo
