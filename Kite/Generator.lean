import Foundation
import Lean.Data.Json

open Lean Meta

namespace LO.Meta

structure Kite (V : Type*) (E : Type) where
  vertices : List V
  search : V → V → MetaM (Option E)
  vs : V → String
  es : E → String
  prefer : E → E → E

namespace Kite

section

variable [DecidableEq V] [DecidableEq E] [Inhabited E] {K : Kite V E}

abbrev Graph.Vertex (_ : Kite V E) := String
abbrev Graph.Edge (K : Kite V E) := (Graph.Vertex K × Graph.Vertex K) × E
structure Graph (K : Kite V E) where
  vertices : List (Graph.Vertex K)
  edges : List (Graph.Edge K)

def Graph.addEdge (G : Graph K) (e : Graph.Edge K) : Graph K := ⟨G.vertices, e :: G.edges⟩

def Graph.removeEdge (G : Graph K) (e : Graph.Edge K) : Graph K := ⟨G.vertices, G.edges.filter (· ≠ e)⟩

def Graph.isContainEdge (G : Graph K) (e : Graph.Edge K) : Bool := G.edges.map (·.1) |>.contains e.1

def Graph.genReflClosure (G : Graph K) : Graph K where
  vertices := G.vertices
  edges := (G.edges ++ (G.vertices.map (λ a => ⟨⟨a, a⟩, default⟩))) |> List.dedup

def Graph.genTransClosure₁ (G : Graph K) : Graph K where
  vertices := G.vertices
  edges := List.dedup (
    G.edges ++
    G.edges.flatMap (λ a => (G.edges.filter (λ b => a.1.2 = b.1.1) |>.map (λ b => ⟨⟨a.1.1, b.1.2⟩, (K.prefer a.2 b.2)⟩)))
  )

partial def Graph.genTransClosure (G : Graph K) :=
  let G' := G.genTransClosure₁
  if G'.edges.length > G.edges.length then G'.genTransClosure else G'

partial def Graph.genReflTransClosure (G : Graph K) := G.genTransClosure.genReflClosure

partial def Graph.nthN (G : Graph K) (n : Fin (G.edges.length + 1)) :=
  match n with
  | ⟨0, _⟩ => G
  | ⟨k + 1, _⟩ =>
    let e := G.edges.get ⟨k, by omega⟩
    let Gn := G.nthN ⟨k, by omega⟩
    let Gn' := Gn.removeEdge e
    if Gn'.genReflTransClosure.isContainEdge e then Gn' else Gn

end


protected def toJson [ToString V] [DecidableEq E] [Inhabited E] (d : Kite V E) : MetaM Json := do
  let E : List (Graph.Edge d) <- (List.product d.vertices d.vertices) |>.filterMapM $ fun ⟨a, b⟩ ↦ do
    let o <- d.search a b
    match o with
    | .some e => return some ⟨⟨ToString.toString a, ToString.toString b⟩, e⟩
    | .none => return none

  let G : Graph d := ⟨d.vertices.map ToString.toString, E⟩
  let Gn := G.nthN ⟨G.edges.length, by omega⟩;

  return Gn.edges
    |>.map (λ ⟨⟨a, b⟩, e⟩ => Json.mkObj [
        ("from", Json.str a),
        ("to", Json.str b),
        ("type", Json.str (d.es e))
      ])
    |> List.toArray
    |> Json.arr

protected def toStringM [ToString V] [DecidableEq E] [Inhabited E] (d : Kite V E) : MetaM String := do
  let j ← d.toJson
  return j.pretty

end LO.Meta.Kite
