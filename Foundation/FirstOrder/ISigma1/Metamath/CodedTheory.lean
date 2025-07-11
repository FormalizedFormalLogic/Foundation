import Foundation.FirstOrder.ISigma1.Metamath.Coding
import Foundation.FirstOrder.ISigma1.Metamath.Proof.Typed

namespace LO.FirstOrder.Theory

@[simp] lemma mem_add_iff {T U : Theory L} {φ} : φ ∈ T + U ↔ φ ∈ T ∨ φ ∈ U := by simp [add_def]

end LO.FirstOrder.Theory

namespace LO.FirstOrder.Semiformula

variable {L : Language}

variable {M : Type*} [Structure L M]

def curve (σ : Semisentence L 1) : Set M := {x | M ⊧/![x] σ}

variable {σ π : Semisentence L 1}

lemma curve_mem_left {x : M} (hx : x ∈ σ.curve) : x ∈ (σ ⋎ π).curve := by left; simpa [curve] using hx

lemma curve_mem_right {x : M} (hx : x ∈ π.curve) : x ∈ (σ ⋎ π).curve := by right; simpa [curve] using hx

end LO.FirstOrder.Semiformula

namespace LO.FirstOrder.Theory

open LO.ISigma1.Metamath

variable {L : Language} [L.Encodable] [L.LORDefinable]

class Δ₁Definable (T : Theory L) extends Arithmetic.LDef.TDef L.lDef where
  mem_iff {φ} : ℕ ⊧/![⌜φ⌝] ch.val ↔ φ ∈ T
  isDelta1 : ch.ProvablyProperOn 𝐈𝚺₁

def tDef (T : Theory L) [d : T.Δ₁Definable] : L.lDef.TDef := d.toTDef

@[simp] lemma Δ₁Definable.mem_iff' (T : Theory L) [d : T.Δ₁Definable] :
    ℕ ⊧/![⌜φ⌝] T.tDef.ch.val ↔ φ ∈ T := d.mem_iff

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

variable {T : Theory L} [T.Δ₁Definable]

variable (T V)

def codeIn : (L.codeIn V).Theory where
  set := T.tDef.ch.val.curve

@[simp] lemma properOn : T.tDef.ch.ProperOn V := (LO.FirstOrder.Theory.Δ₁Definable.isDelta1 (T := T)).properOn V

variable {T V}

@[simp] lemma mem_codeIn_iff {σ} : ⌜σ⌝ ∈ T.codeIn V ↔ σ ∈ T :=
  have : V ⊧/![⌜σ⌝] T.tDef.ch.val ↔ ℕ ⊧/![⌜σ⌝] T.tDef.ch.val := by
    simpa [coe_quote, Matrix.constant_eq_singleton]
      using FirstOrder.Arithmetic.models_iff_of_Delta1 (V := V) (σ := T.tDef.ch) (by simp) (by simp) (e := ![⌜σ⌝])
  Iff.trans this Theory.Δ₁Definable.mem_iff

instance tDef_defined : (T.codeIn V).Defined T.tDef where
  defined := ⟨by
    intro v
    rw [show v = ![v 0] from Matrix.fun_eq_vec_one]
    have := (consequence_iff (T := 𝐈𝚺₁)).mp (sound!₀ <| FirstOrder.Theory.Δ₁Definable.isDelta1 (T := T)) V inferInstance
    simp [models_iff] at this ⊢
    simp [Matrix.constant_eq_singleton, Theory.tDef, this],
  by intro v; simp [FirstOrder.Semiformula.curve, Theory.codeIn, ←Matrix.fun_eq_vec_one]⟩

variable (T V)

def tCodeIn (T : Theory L) [T.Δ₁Definable] : (L.codeIn V).TTheory where
  thy := T.codeIn V
  pthy := T.tDef

variable {T V}

variable {U : Theory L}

namespace Δ₁Definable

open Arithmetic.HierarchySymbol.Semiformula LO.FirstOrder.Theory

instance add (dT : T.Δ₁Definable) (dU : U.Δ₁Definable) : (T + U).Δ₁Definable where
  ch := T.tDef.ch ⋎ U.tDef.ch
  mem_iff {φ} := by simp
  isDelta1 := ProvablyProperOn.ofProperOn.{0} _ fun V _ _ ↦ ProperOn.or (by simp) (by simp)

def ofEq (dT : T.Δ₁Definable) (h : T = U) : U.Δ₁Definable where
  ch := dT.ch
  mem_iff := by rcases h; exact dT.mem_iff
  isDelta1 := by rcases h; exact dT.isDelta1

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

instance empty : Theory.Δ₁Definable (∅ : Theory L) where
  ch := ⊥
  mem_iff {ψ} := by simp
  isDelta1 := ProvablyProperOn.ofProperOn.{0} _ fun V _ _ ↦ by simp

def singleton (φ : SyntacticFormula L) : Theory.Δ₁Definable {φ} where
  ch := .ofZero (.mkSigma “x. x = ↑⌜φ⌝” (by simp)) _
  mem_iff {ψ} := by simp
  isDelta1 := ProvablyProperOn.ofProperOn.{0} _ fun V _ _ ↦ by simp

@[simp] lemma singleton_toTDef_ch_val (φ : FirstOrder.SyntacticFormula L) :
    letI := Δ₁Definable.singleton φ
    (FirstOrder.Theory.Δ₁Definable.toTDef {φ}).ch.val = “x. x = ↑⌜φ⌝” := rfl

noncomputable
def ofList (l : List (SyntacticFormula L)) : Δ₁Definable {φ | φ ∈ l} :=
  match l with
  |     [] => empty.ofEq (by ext; simp)
  | φ :: l => ((singleton φ).add (ofList l)).ofEq (by ext; simp)

noncomputable
def ofFinite (T : Theory L) (h : Set.Finite T) : T.Δ₁Definable := (ofList h.toFinset.toList).ofEq (by ext; simp)

instance [T.Δ₁Definable] [U.Δ₁Definable] : (T + U).Δ₁Definable := add inferInstance inferInstance

instance (φ : SyntacticFormula L) : Theory.Δ₁Definable {φ} := singleton φ

end Δ₁Definable

end LO.FirstOrder.Theory
