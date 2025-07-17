import Foundation.FirstOrder.Internal.Syntax.Formula.Coding
import Foundation.FirstOrder.Internal.Syntax.Formula.Iteration

namespace LO.ISigma1.Metamath

open FirstOrder Arithmetic PeanoMinus IOpen ISigma0

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

variable {L : Language} [L.Encodable] [L.LORDefinable]

class _root_.LO.FirstOrder.Theory.Δ₁Definable (T : Theory L) where
  ch : 𝚫₁.Semisentence 1
  mem_iff : ∀ φ, ℕ ⊧/![⌜φ⌝] ch.val ↔ φ ∈ T
  isDelta1 : ch.ProvablyProperOn 𝐈𝚺₁

abbrev _root_.LO.FirstOrder.Theory.Δ₁ch (T : Theory L) [T.Δ₁Definable] : 𝚫₁.Semisentence 1 := Theory.Δ₁Definable.ch T

def _root_.LO.FirstOrder.Theory.Δ₁Class (T : Theory L) [T.Δ₁Definable] : Set V := { φ : V | V ⊧/![φ] T.Δ₁ch.val }

variable {T : Theory L} [T.Δ₁Definable]

instance Δ₁Class.defined : 𝚫₁-Predicate[V] (· ∈ T.Δ₁Class) via T.Δ₁ch := by
  constructor
  · intro v
    have : V ⊧/![v 0] (Theory.Δ₁Definable.ch T).sigma.val ↔ V ⊧/![v 0] (Theory.Δ₁Definable.ch T).pi.val := by
      have := (consequence_iff (T := 𝐈𝚺₁)).mp (sound!₀ <| FirstOrder.Theory.Δ₁Definable.isDelta1 (T := T)) V inferInstance
      simp [models_iff] at this ⊢
      simpa [Matrix.constant_eq_singleton] using this ![v 0]
    rwa [show v = ![v 0] from Matrix.fun_eq_vec_one]
  · intro v; simp [←Matrix.fun_eq_vec_one, Theory.Δ₁Class]

instance Δ₁Class.definable : 𝚫₁-Predicate[V] (· ∈ T.Δ₁Class) := Δ₁Class.defined.to_definable

@[simp] lemma Δ₁Class.proper : T.Δ₁ch.ProperOn V := (Theory.Δ₁Definable.isDelta1 (T := T)).properOn V

@[simp] lemma Δ₁Class.mem_iff {φ : SyntacticFormula L} : (⌜φ⌝ : V) ∈ T.Δ₁Class ↔ φ ∈ T :=
  have : V ⊧/![⌜φ⌝] T.Δ₁ch.val ↔ ℕ ⊧/![⌜φ⌝] T.Δ₁ch.val := by
    simpa [Semiformula.coe_quote_eq_quote, Matrix.constant_eq_singleton]
      using FirstOrder.Arithmetic.models_iff_of_Delta1 (V := V) (σ := T.Δ₁ch) (by simp) (by simp) (e := ![⌜φ⌝])
  Iff.trans this (Theory.Δ₁Definable.mem_iff _)

@[simp] lemma Δ₁Class.mem_iff' {φ : SyntacticFormula L} : V ⊧/![⌜φ⌝] T.Δ₁ch.val ↔ φ ∈ T := Δ₁Class.mem_iff

@[simp] lemma Δ₁Class.mem_iff'' {φ : SyntacticFormula L} : ((⌜φ⌝ : Metamath.Formula V L).val : V) ∈ T.Δ₁Class ↔ φ ∈ T :=
  Δ₁Class.mem_iff

end LO.ISigma1.Metamath

namespace LO.FirstOrder.Theory

variable {L : Language} [L.Encodable] [L.LORDefinable]

variable {T U : Theory L}

namespace Δ₁Definable

open Arithmetic.HierarchySymbol.Semiformula LO.FirstOrder.Theory

instance add (dT : T.Δ₁Definable) (dU : U.Δ₁Definable) : (T + U).Δ₁Definable where
  ch := T.Δ₁ch ⋎ U.Δ₁ch
  mem_iff {φ} := by simp [Theory.add_def]
  isDelta1 := ProvablyProperOn.ofProperOn.{0} _ fun V _ _ ↦ ProperOn.or (by simp) (by simp)

def ofEq (dT : T.Δ₁Definable) (h : T = U) : U.Δ₁Definable where
  ch := dT.ch
  mem_iff := by rcases h; exact dT.mem_iff
  isDelta1 := by rcases h; exact dT.isDelta1

/-
def add_subset_left (dT : T.Δ₁Definable) (dU : U.Δ₁Definable) :
    haveI := dT.add dU
    T.codeIn V ⊆ (T + U).codeIn V := by
  intro p hp
  apply FirstOrder.Semiformula.curve_mem_left
  simpa [val_sigma] using hp

def add_subset_right (dT : T.Δ₁Definable) (dU : U.Δ₁Definable) :
    haveI := dT.add dU
    U.codeIn V ⊆ (T + U).codeIn V := by
  intro p hp
  apply FirstOrder.Semiformula.curve_mem_right
  simpa [val_sigma] using hp
-/


instance empty : Theory.Δ₁Definable (∅ : Theory L) where
  ch := ⊥
  mem_iff {ψ} := by simp
  isDelta1 := ProvablyProperOn.ofProperOn.{0} _ fun V _ _ ↦ by simp

def singleton (φ : SyntacticFormula L) : Theory.Δ₁Definable {φ} where
  ch := .ofZero (.mkSigma “x. x = ↑(Encodable.encode φ)”) _
  mem_iff {ψ} := by simp [Semiformula.quote_eq_encode]
  isDelta1 := ProvablyProperOn.ofProperOn.{0} _ fun V _ _ ↦ by simp

@[simp] lemma singleton_toTDef_ch_val (φ : FirstOrder.SyntacticFormula L) :
    letI := Δ₁Definable.singleton φ
    ({φ} : Theory L).Δ₁ch.val = “x. x = ↑(Encodable.encode φ)” := by rfl

def ofList (l : List (SyntacticFormula L)) : Δ₁Definable {φ | φ ∈ l} :=
  match l with
  |     [] => empty.ofEq (by ext; simp)
  | φ :: l => ((singleton φ).add (ofList l)).ofEq (by ext; simp [Theory.add_def])

noncomputable def ofFinite (T : Theory L) (h : Set.Finite T) : T.Δ₁Definable := (ofList h.toFinset.toList).ofEq (by ext; simp)

instance [T.Δ₁Definable] [U.Δ₁Definable] : (T + U).Δ₁Definable := add inferInstance inferInstance

instance (φ : SyntacticFormula L) : Theory.Δ₁Definable {φ} := singleton φ

end Δ₁Definable

end LO.FirstOrder.Theory
