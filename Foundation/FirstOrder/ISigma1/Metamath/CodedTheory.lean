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

variable {L : Language} [(k : ℕ) → Encodable (L.Func k)] [(k : ℕ) → Encodable (L.Rel k)] [DefinableLanguage L]

class Delta1Definable (T : Theory L) extends Arith.LDef.TDef L.lDef where
  mem_iff {φ} : ℕ ⊧/![⌜φ⌝] ch.val ↔ φ ∈ T
  isDelta1 : ch.ProvablyProperOn 𝐈𝚺₁

def tDef (T : Theory L) [d : T.Delta1Definable] : L.lDef.TDef := d.toTDef

@[simp] lemma Delta1Definable.mem_iff' (T : Theory L) [d : T.Delta1Definable] :
    ℕ ⊧/![⌜φ⌝] T.tDef.ch.val ↔ φ ∈ T := d.mem_iff

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

variable {T : Theory L} [T.Delta1Definable]

variable (T V)

def codeIn : (L.codeIn V).Theory where
  set := T.tDef.ch.val.curve

@[simp] lemma properOn : T.tDef.ch.ProperOn V := (LO.FirstOrder.Theory.Delta1Definable.isDelta1 (T := T)).properOn V

variable {T V}

@[simp] lemma mem_codeIn_iff {σ} : ⌜σ⌝ ∈ T.codeIn V ↔ σ ∈ T :=
  have : V ⊧/![⌜σ⌝] T.tDef.ch.val ↔ ℕ ⊧/![⌜σ⌝] T.tDef.ch.val := by
    simpa [coe_quote, Matrix.constant_eq_singleton]
      using FirstOrder.Arith.models_iff_of_Delta1 (V := V) (σ := T.tDef.ch) (by simp) (by simp) (e := ![⌜σ⌝])
  Iff.trans this Theory.Delta1Definable.mem_iff

instance tDef_defined : (T.codeIn V).Defined T.tDef where
  defined := ⟨by
    intro v
    rw [show v = ![v 0] from Matrix.fun_eq_vec_one]
    have := (consequence_iff (T := 𝐈𝚺₁)).mp (sound! <| FirstOrder.Theory.Delta1Definable.isDelta1 (T := T)) V inferInstance
    simp [models_iff] at this ⊢
    simp [Matrix.constant_eq_singleton, Theory.tDef, this],
  by intro v; simp [FirstOrder.Semiformula.curve, Theory.codeIn, ←Matrix.fun_eq_vec_one]⟩

variable (T V)

def tCodeIn (T : Theory L) [T.Delta1Definable] : (L.codeIn V).TTheory where
  thy := T.codeIn V
  pthy := T.tDef

variable {T V}

variable {U : Theory L}

namespace Delta1Definable

open Arith.HierarchySymbol.Semiformula LO.FirstOrder.Theory

def add (dT : T.Delta1Definable) (dU : U.Delta1Definable) : (T + U).Delta1Definable where
  ch := T.tDef.ch ⋎ U.tDef.ch
  mem_iff {φ} := by simp
  isDelta1 := ProvablyProperOn.ofProperOn.{0} _ fun V _ _ ↦ ProperOn.or (by simp) (by simp)

def ofEq (dT : T.Delta1Definable) (h : T = U) : U.Delta1Definable where
  ch := dT.ch
  mem_iff := by rcases h; exact dT.mem_iff
  isDelta1 := by rcases h; exact dT.isDelta1

def add_subset_left (dT : T.Delta1Definable) (dU : U.Delta1Definable) :
    haveI := dT.add dU
    T.codeIn V ⊆ (T + U).codeIn V := by
  intro p hp
  apply FirstOrder.Semiformula.curve_mem_left
  simpa [val_sigma] using hp

def add_subset_right (dT : T.Delta1Definable) (dU : U.Delta1Definable) :
    haveI := dT.add dU
    U.codeIn V ⊆ (T + U).codeIn V := by
  intro p hp
  apply FirstOrder.Semiformula.curve_mem_right
  simpa [val_sigma] using hp

instance empty : Theory.Delta1Definable (∅ : Theory L) where
  ch := ⊥
  mem_iff {ψ} := by simp
  isDelta1 := ProvablyProperOn.ofProperOn.{0} _ fun V _ _ ↦ by simp

/-! memo: This noncomputable is *not* essetial. -/
noncomputable
def singleton (φ : SyntacticFormula L) : Theory.Delta1Definable {φ} where
  ch := .ofZero (.mkSigma “x. x = ↑⌜φ⌝” (by simp)) _
  mem_iff {ψ} := by simp
  isDelta1 := ProvablyProperOn.ofProperOn.{0} _ fun V _ _ ↦ by simp

@[simp] lemma singleton_toTDef_ch_val (φ : FirstOrder.SyntacticFormula L) :
    letI := Delta1Definable.singleton φ
    (FirstOrder.Theory.Delta1Definable.toTDef {φ}).ch.val = “x. x = ↑⌜φ⌝” := rfl

noncomputable
def ofList (l : List (SyntacticFormula L)) : Delta1Definable {φ | φ ∈ l} :=
  match l with
  |     [] => empty.ofEq (by ext; simp)
  | φ :: l => ((singleton φ).add (ofList l)).ofEq (by ext; simp)

noncomputable
def ofFinite (T : Theory L) (h : Set.Finite T) : T.Delta1Definable := (ofList h.toFinset.toList).ofEq (by ext; simp)

end Delta1Definable

end LO.FirstOrder.Theory
