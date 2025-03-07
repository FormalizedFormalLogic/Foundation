import Kite.Generator

namespace LO.Meta.Kite.Arith

open Lean Qq
open LO.FirstOrder
open LO.Meta

structure Vertex (F : Q(Type)) where
  name : String
  Entailment : Q(Type)
  thy : Q($Entailment)

instance : ToString (Vertex F) where
  toString v := s!"{v.name}"

inductive EdgeType where
  | weaker
  | strict
deriving ToExpr, DecidableEq

def EdgeType.prefer : EdgeType → EdgeType → EdgeType
  | .strict, .strict => .strict
  | _, _ => .weaker

instance : Inhabited EdgeType := ⟨.weaker⟩
instance : ToString EdgeType where
  toString
    | .weaker => "weaker"
    | .strict => "strict"

def EdgeType.search {F : Q(Type)} (s t : Vertex F) : MetaM (Option EdgeType) := do
  let ⟨_, S, 𝓢⟩ := s
  let ⟨_, T, 𝓣⟩ := t
  let _ssys : Q(Entailment.{0,0,0} $F $S) ← Qq.synthInstanceQ q(Entailment.{0,0,0} $F $S)
  let _tsys : Q(Entailment.{0,0,0} $F $T) ← Qq.synthInstanceQ q(Entailment.{0,0,0} $F $T)
  let w ← Meta.synthInstance? q(Entailment.WeakerThan $𝓢 $𝓣)
  let s ← Meta.synthInstance? q(Entailment.StrictlyWeakerThan $𝓢 $𝓣)
  match w, s with
  |   .none,   .none => return .none
  | .some _,   .none => return .some <| .weaker
  |       _, .some _ => return .some <| .strict

def kite : Kite (Vertex q(SyntacticFormula ℒₒᵣ)) EdgeType where
  vertices := [
    ⟨"CobhamR0", q(Theory ℒₒᵣ), q(𝐑₀)⟩,
    ⟨"PAMinus", q(Theory ℒₒᵣ), q(𝐏𝐀⁻)⟩,
    ⟨"ISigma0", q(Theory ℒₒᵣ), q(𝐈𝚺₀)⟩,
    ⟨"ISigma1", q(Theory ℒₒᵣ), q(𝐈𝚺₁)⟩,
    ⟨"PA", q(Theory ℒₒᵣ), q(𝐏𝐀)⟩,
    ⟨"TA", q(Theory ℒₒᵣ), q(𝐓𝐀)⟩,
  ]
  search := EdgeType.search
  vs v := s!"{v.name}"
  es e :=
    match e with
    | .weaker => "weaker"
    | .strict => "strict"
  prefer := EdgeType.prefer

end LO.Meta.Kite.Arith

/-
open Lean
open Lean.Meta

unsafe
def main : IO Unit := do
  searchPathRef.set compile_time_search_path%
  withImportModules #[Import.mk `Kite false] {} 0 fun env => do
    let ⟨s, _, _⟩ ← LO.Meta.Kite.Arith.kite.toStringM.toIO { fileName := "<compiler>", fileMap := default } { env := env }
    IO.FS.writeFile ("Arith.json") s
-/
