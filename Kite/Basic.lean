import Std.Data.HashSet

namespace Kite

inductive EdgeType
-- | eq
| ssub
-- | sub
deriving BEq, Hashable, Repr

instance : ToString EdgeType := ⟨λ t =>
  match t with
  -- | .eq => "eq"
  | .ssub => "ssub"
  -- | .sub => "sub"
⟩

structure Edge where
  a: String
  b: String
  type: EdgeType
deriving BEq, Hashable, Repr

abbrev Edges := Std.HashSet Edge

def Edges.TC (es : Edges) := Id.run do
  let mut closure : Edges := es
  let mut added : Bool := true
  while added do
    added := false
    for ⟨a, b, _⟩ in closure.toList do
      for ⟨c, d, t⟩ in closure.toList do
        if b == c then
          let p : Edge := ⟨a, d, t⟩
          if !closure.contains p then
            closure := closure.insert p
            added := true
  closure

def Edges.isDerivable (es : Edges) (e : Edge) := Edges.TC (es.erase e) |>.contains e
def Edges.reductTrans (es : Edges) := es.toArray.filter (λ x => ¬(es.isDerivable x))

end Kite
