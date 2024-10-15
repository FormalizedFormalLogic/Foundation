import Arithmetization.ISigmaOne.Metamath.Coding
import Arithmetization.ISigmaOne.Metamath.Proof.Typed
import Foundation.FirstOrder.Arith.PeanoMinus

namespace LO.FirstOrder.Semiformula

variable {L : Language}

variable {M : Type*} [Structure L M]

def curve (σ : Semisentence L 1) : Set M := {x | M ⊧/![x] σ}

variable {σ π : Semisentence L 1}

lemma curve_mem_left {x : M} (hx : x ∈ σ.curve) : x ∈ (σ ⋎ π).curve := by simp [curve]; left; exact hx

lemma curve_mem_right {x : M} (hx : x ∈ π.curve) : x ∈ (σ ⋎ π).curve := by simp [curve]; right; exact hx

end LO.FirstOrder.Semiformula

namespace LO.Arith

open LO.FirstOrder

variable {L : Language} [(k : ℕ) → Encodable (L.Func k)] [(k : ℕ) → Encodable (L.Rel k)] [DefinableLanguage L]

class _root_.LO.FirstOrder.Theory.Delta1Definable (T : Theory L) extends Arith.LDef.TDef L.lDef where
  mem_iff {p} : p ∈ T ↔ ℕ ⊧/![⌜p⌝] ch.val
  isDelta1 : ch.ProvablyProperOn 𝐈𝚺₁

def _root_.LO.FirstOrder.Theory.tDef (T : Theory L) [d : T.Delta1Definable] : L.lDef.TDef := d.toTDef

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

variable {T : Theory L} [T.Delta1Definable]

variable (T V)

def _root_.LO.FirstOrder.Theory.codeIn : (L.codeIn V).Theory where
  set := T.tDef.ch.val.curve

@[simp] lemma _root_.LO.FirstOrder.Theory.properOn : T.tDef.ch.ProperOn V := (LO.FirstOrder.Theory.Delta1Definable.isDelta1 (T := T)).properOn V

variable {T V}

lemma Language.Theory.codeIn_iff : x ∈ T.codeIn V ↔ V ⊧/![x] T.tDef.ch.val := iff_of_eq rfl

lemma mem_coded_theory_iff {σ} : ⌜σ⌝ ∈ T.codeIn V ↔ σ ∈ T :=
  have : V ⊧/![⌜σ⌝] T.tDef.ch.val ↔ ℕ ⊧/![⌜σ⌝] T.tDef.ch.val := by
    simpa [coe_quote] using FirstOrder.Arith.models_iff_of_Delta1 (V := V) (σ := T.tDef.ch) (by simp) (by simp) (e := ![⌜σ⌝])
  Iff.trans this Theory.Delta1Definable.mem_iff.symm

instance tDef_defined : (T.codeIn V).Defined T.tDef where
  defined := ⟨by
    intro v
    rw [show v = ![v 0] from Matrix.constant_eq_singleton']
    have := (consequence_iff (T := 𝐈𝚺₁)).mp (sound! <| FirstOrder.Theory.Delta1Definable.isDelta1 (T := T)) V inferInstance
    simp [models_iff] at this ⊢
    simp [Theory.tDef, this],
  by intro v; simp [FirstOrder.Semiformula.curve, Theory.codeIn, ←Matrix.constant_eq_singleton']⟩

variable (T V)

def _root_.LO.FirstOrder.Theory.tCodeIn (T : Theory L) [T.Delta1Definable] : (L.codeIn V).TTheory where
  thy := T.codeIn V
  pthy := T.tDef

variable {T V}

variable {U : Theory L}

def _root_.LO.FirstOrder.Theory.Delta1Definable.add (dT : T.Delta1Definable) (dU : U.Delta1Definable) : (T + U).Delta1Definable where
  ch := T.tDef.ch.or U.tDef.ch
  mem_iff {p} := by
    simp [Arith.HierarchySymbol.Semiformula.or, Theory.add_def,
      LO.FirstOrder.Theory.Delta1Definable.mem_iff, Arith.HierarchySymbol.Semiformula.val_sigma]; rfl
  isDelta1 := Arith.HierarchySymbol.Semiformula.ProvablyProperOn.ofProperOn.{0} _ fun V _ _ _ ↦
    by simp [models_iff, models_iff, Arith.HierarchySymbol.Semiformula.or, Arith.HierarchySymbol.Semiformula.val_sigma,
         (T.properOn (V := V)).iff', (U.properOn (V := V)).iff']

def _root_.LO.FirstOrder.Theory.Delta1Definable.ofEq (dT : T.Delta1Definable) (h : T = U) : U.Delta1Definable where
  ch := dT.ch
  mem_iff := by rcases h; exact dT.mem_iff
  isDelta1 := by rcases h; exact dT.isDelta1

def _root_.LO.FirstOrder.Theory.Delta1Definable.add_subset_left
    (dT : T.Delta1Definable) (dU : U.Delta1Definable) :
    haveI := dT.add dU
    T.codeIn V ⊆ (T + U).codeIn V := by
  intro p hp
  apply FirstOrder.Semiformula.curve_mem_left
  simpa [Arith.HierarchySymbol.Semiformula.val_sigma] using hp

def _root_.LO.FirstOrder.Theory.Delta1Definable.add_subset_right
    (dT : T.Delta1Definable) (dU : U.Delta1Definable) :
    haveI := dT.add dU
    U.codeIn V ⊆ (T + U).codeIn V := by
  intro p hp
  apply FirstOrder.Semiformula.curve_mem_right
  simpa [Arith.HierarchySymbol.Semiformula.val_sigma] using hp

end LO.Arith
