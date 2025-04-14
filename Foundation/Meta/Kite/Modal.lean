import Foundation.Meta.Kite.Generator
import Foundation.Modal.Logic.WellKnown
-- import Foundation.Modal.Logic.S

namespace LO.Meta.Kite.Modal

open Lean Qq
open LO.Meta
open LO.Modal (Logic)

structure Vertex where
  thy : Q(Logic)

instance : ToString Vertex where
  toString v := s!"{v.thy}"

inductive EdgeType where
  | weaker
  | strict
deriving ToExpr, DecidableEq

def EdgeType.prefer : EdgeType → EdgeType → EdgeType
  | .strict, .strict => .strict
  | _, _ => .weaker

instance : Inhabited EdgeType := ⟨.weaker⟩

def EdgeType.search (s t : Vertex) : MetaM (Option EdgeType) := do
  let ⟨L₁⟩ := s
  let ⟨L₂⟩ := t
  let w ← Meta.synthInstance? q(Logic.Sublogic $L₁ $L₂)
  let s ← Meta.synthInstance? q(Logic.ProperSublogic $L₁ $L₂)
  match w, s with
  |   .none,   .none => return .none
  | .some _,   .none => return .some .weaker
  |       _, .some _ => return .some .strict

def kite : Kite Vertex EdgeType where
  vertices := [
    ⟨q(Logic.Empty)⟩,
    ⟨q(Logic.GL)⟩,
    ⟨q(Logic.GLPoint3)⟩,
    ⟨q(Logic.Grz)⟩,
    ⟨q(Logic.GrzPoint2)⟩,
    ⟨q(Logic.GrzPoint3)⟩,
    ⟨q(Logic.K)⟩,
    ⟨q(Logic.K4)⟩,
    ⟨q(Logic.K45)⟩,
    ⟨q(Logic.K4Point2)⟩,
    ⟨q(Logic.K4Point3)⟩,
    ⟨q(Logic.K5)⟩,
    ⟨q(Logic.KB)⟩,
    ⟨q(Logic.KB4)⟩,
    ⟨q(Logic.KB5)⟩,
    ⟨q(Logic.KD)⟩,
    ⟨q(Logic.KD4)⟩,
    ⟨q(Logic.KD45)⟩,
    ⟨q(Logic.KD5)⟩,
    ⟨q(Logic.KDB)⟩,
    ⟨q(Logic.KH)⟩,
    ⟨q(Logic.KT)⟩,
    ⟨q(Logic.KTB)⟩,
    ⟨q(Logic.KTc)⟩,
    -- ⟨q(Logic.S)⟩,
    ⟨q(Logic.S4)⟩,
    ⟨q(Logic.S4Point2)⟩,
    ⟨q(Logic.S4Point3)⟩,
    ⟨q(Logic.S5)⟩,
    ⟨q(Logic.Triv)⟩,
    ⟨q(Logic.Univ)⟩,
    ⟨q(Logic.Ver)⟩,
  ]
  search := EdgeType.search
  vs v := s!"{v.thy}"
  es e :=
    match e with
    | .weaker => "weaker"
    | .strict => "strict"
  prefer := EdgeType.prefer

end LO.Meta.Kite.Modal
