module

public import Foundation.FirstOrder.Ultraproduct
public import Foundation.Vorspiel.List.ChainI
public import Mathlib.Data.Finset.Lattice.Lemmas

@[expose] public section
namespace LO.FirstOrder

namespace Completeness

variable (L : Language)

abbrev Clause := Finset (Proposition L)

variable {L}

namespace Clause

def IsClosed (C : Clause L) : Prop := ∃ φ ∈ C, ∼φ ∈ C

def shift (C : Clause L) : Clause L := C.map ⟨Semiformula.shift, LawfulSyntacticRewriting.shift_injective⟩

inductive IsBoundary (C : Clause L) : Proposition L → Prop
| rel (R : L.Rel k) (v) : IsBoundary C (.rel R v)
| nrel (R : L.Rel k) (v) : IsBoundary C (.nrel R v)
| verum : IsBoundary C ⊤
| falsum : IsBoundary C ⊥
| and {φ ψ} : φ ∉ C → ψ ∉ C → IsBoundary C (φ ⋏ ψ)
| or {φ ψ} : φ ∉ C ∨ ψ ∉ C → IsBoundary C (φ ⋎ ψ)


def rank (C : Clause L) : ℕ := C.fold (λ φ r => max φ.rank r) 0

end Clause

open Classical

inductive Search : Clause L → Clause L → Prop
| and_left {C : Clause L} : ¬C.IsClosed → φ ⋏ ψ ∈ C → Search (insert φ C) C
| and_right {C : Clause L} : ¬C.IsClosed → φ ⋏ ψ ∈ C → Search (insert ψ C) C
| or {C : Clause L} : ¬C.IsClosed → φ ⋎ ψ ∈ C → Search (insert φ (insert ψ C)) C
| all {C : Clause L} : ¬C.IsClosed → ∀⁰ φ ∈ C → Search (insert φ.free C.shift) C
| exs {C : Clause L} : ¬C.IsClosed → ∃⁰ φ ∈ C → (t : SyntacticTerm L) → Search (insert (φ/[t]) C) C

structure SearchPath (C : Clause L) where
  path : List (Clause L)
  last : Clause L
  chain : path.ChainI Search last C

namespace SearchPath

variable {C : Clause L}

instance : LE (SearchPath C) where
  le π τ := π.path <+: τ.path

end SearchPath


end LO.FirstOrder.Completeness
