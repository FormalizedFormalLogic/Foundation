import Arithmetization.ISigmaOne.Metamath.Coding
import Arithmetization.ISigmaOne.Metamath.Proof.Typed
import Logic.FirstOrder.Arith.PeanoMinus

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
  set := {x | V ⊧/![x] T.tDef.ch.val}

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
  by intro v; simp [Theory.codeIn, ←Matrix.constant_eq_singleton']⟩

variable (T V)

def _root_.LO.FirstOrder.Theory.tCodeIn (T : Theory L) [T.Delta1Definable] : (L.codeIn V).TTheory where
  thy := T.codeIn V
  pthy := T.tDef

variable {T V}

variable (T) (U : Theory L)

def _root_.LO.FirstOrder.Theory.delta1Definable_add [T.Delta1Definable] [U.Delta1Definable] : (T + U).Delta1Definable where
  ch := T.tDef.ch.or U.tDef.ch
  mem_iff {p} := by
    simp [Arith.HierarchySymbol.Semiformula.or, Theory.add_def,
      LO.FirstOrder.Theory.Delta1Definable.mem_iff, Arith.HierarchySymbol.Semiformula.val_sigma]; rfl
  isDelta1 := Arith.HierarchySymbol.Semiformula.ProvablyProperOn.ofProperOn.{0} _ fun V _ _ _ ↦
    by simp [models_iff, models_iff, Arith.HierarchySymbol.Semiformula.or, Arith.HierarchySymbol.Semiformula.val_sigma,
         (T.properOn (V := V)).iff', (U.properOn (V := V)).iff']

def _root_.LO.FirstOrder.Theory.Delta1Definable.intro'
    (φ : L.lDef.TDef)
    (H : ∀ p, p ∈ T ↔ ℕ ⊧/![⌜p⌝] φ.ch.val)
    (Δ : φ.ch.ProvablyProperOn 𝐈𝚺₁) : T.Delta1Definable where
  ch := φ.ch
  mem_iff {p} := H p
  isDelta1 := Δ

def _root_.LO.FirstOrder.Theory.Delta1Definable.intro''
    (φ : L.lDef.TDef)
    (Th : ∀ (M : Type) [ORingStruc M] [M ⊧ₘ* 𝐈𝚺₁], (L.codeIn M).Theory)
    (H : ∀ (M : Type) [ORingStruc M] [M ⊧ₘ* 𝐈𝚺₁], (Th M).Defined φ)
    (hTh : ∀ p, p ∈ T ↔ ⌜p⌝ ∈ Th ℕ) : T.Delta1Definable where
  ch := φ.ch
  mem_iff {p} := by simpa [hTh] using (H ℕ).defined.df ![⌜p⌝]
  isDelta1 := Arith.HierarchySymbol.Semiformula.ProvablyProperOn.ofProperOn.{0} _ fun V _ _ v ↦ (H V).defined.proper v

end LO.Arith
