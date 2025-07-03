import Std.Data.HashSet
import Lean.Data.Json

open Lean

namespace Kite

inductive EdgeType
-- | eq
| ssub
| sub
deriving BEq, Hashable, Repr

def EdgeType.comp : EdgeType → EdgeType → EdgeType
| .ssub, .ssub => .ssub
| .ssub, .sub  => .ssub
| .sub,  .ssub => .ssub
| .sub,  .sub  => .sub


instance : ToString EdgeType := ⟨λ t =>
  match t with
  -- | .eq => "eq"
  | .ssub => "ssub"
  | .sub => "sub"
⟩

structure Edge where
  a: String
  b: String
  type: EdgeType
deriving BEq, Hashable, Repr

abbrev Edges := Std.HashSet Edge

def Edges.cleanDup (es : Edges) : Edges := es.filter (
  λ ⟨a, b, t⟩ =>
    match t with
    | .ssub => true
    | .sub => !es.contains ⟨a, b, .ssub⟩
)

def Edges.TC (es : Edges) := Id.run do
  let mut closure : Edges := es
  let mut added : Bool := true
  while added do
    added := false
    for ⟨a₁, b₁, t₁⟩ in closure.toList do
      for ⟨a₂, b₂, t₂⟩ in closure.toList do
        if b₁ == a₂ then
          let p : Edge := ⟨a₁, b₂, t₁.comp t₂⟩
          if !closure.contains p then
            closure := closure.insert p
            added := true
  closure

def Edges.isDerivable (es : Edges) (e : Edge) := Edges.TC (es.erase e) |>.contains e
def Edges.reductTrans (es : Edges) := es.toArray.filter (λ x => !es.isDerivable x)

def Edges.toOutput (es : Edges) := es.cleanDup.reductTrans
  |> .map (λ ⟨a, b, t⟩ => Json.mkObj [
      ("from", s!"{a}"),
      ("to", s!"{b}"),
      ("type", s!"{t}")
    ])
  |> Json.arr

end Kite
