import Arithmetization.ISigmaOne.Metamath.Coding
import Arithmetization.ISigmaOne.Metamath.Proof.Typed
import Logic.FirstOrder.Arith.PeanoMinus

namespace LO.Arith

open LO.FirstOrder

variable {L : Language} [(k : ℕ) → Encodable (L.Func k)] [(k : ℕ) → Encodable (L.Rel k)] [DefinableLanguage L]

class _root_.LO.FirstOrder.SyntacticTheory.Delta1Definable (T : SyntacticTheory L) extends Arith.LDef.TDef L.lDef where
  mem_iff {σ} : σ ∈ T ↔ 𝐈𝚺₁ ⊢₌! ch.val/[(⌜σ⌝ : Semiterm ℒₒᵣ Empty 0)]
  isDelta1 : 𝐈𝚺₁ ⊢₌! “∀ x, !ch.sigma x ↔ !ch.pi x”

abbrev _root_.LO.FirstOrder.Theory.Delta1Definable (T : Theory L) := SyntacticTheory.Delta1Definable (L := L) ↑T

def _root_.LO.FirstOrder.SyntacticTheory.tDef (T : SyntacticTheory L) [d : T.Delta1Definable] : Arith.LDef.TDef L.lDef := d.toTDef

abbrev _root_.LO.FirstOrder.Theory.tDef (T : Theory L) [d : T.Delta1Definable] : Arith.LDef.TDef L.lDef := d.toTDef

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

variable {T : SyntacticTheory L} [T.Delta1Definable]

variable (T V)

def _root_.LO.FirstOrder.SyntacticTheory.codeIn : (L.codeIn V).Theory where
  set := {x | V ⊧/![x] T.tDef.ch.val}

@[simp] lemma _root_.LO.FirstOrder.SyntacticTheory.properOn : T.tDef.ch.ProperOn V := by
  intro v
  have := by simpa [models_iff] using
    consequence_iff_add_eq.mp (sound! <| LO.FirstOrder.SyntacticTheory.Delta1Definable.isDelta1 (T := T)) V inferInstance
  simpa [←Matrix.constant_eq_singleton'] using this (v 0)

abbrev _root_.LO.FirstOrder.Theory.codeIn (T : Theory L) [T.Delta1Definable] : (L.codeIn V).Theory := SyntacticTheory.codeIn (L := L) V T

variable {T V}

lemma Language.SyntacticTheory.codeIn_iff : x ∈ T.codeIn V ↔ V ⊧/![x] T.tDef.ch.val := iff_of_eq rfl

lemma mem_coded_theory_iff {σ} : ⌜σ⌝ ∈ T.codeIn V ↔ σ ∈ T :=
  have : V ⊧/![⌜σ⌝] T.tDef.ch.val ↔ 𝐈𝚺₁ ⊢₌! T.tDef.ch.val/[⌜σ⌝] := by
    simpa [coe_quote, numeral_quote] using
      FirstOrder.Arith.models_iff_provable_of_Delta1_param (V := V) (T := 𝐈𝚺₁) (σ := T.tDef.ch) (by simp) (by simp) (e := ![⌜σ⌝])
  Iff.trans this SyntacticTheory.Delta1Definable.mem_iff.symm

instance tDef_defined : (T.codeIn V).Defined T.tDef where
  defined := ⟨by
    intro v
    rw [show v = ![v 0] from Matrix.constant_eq_singleton']
    have := consequence_iff_add_eq.mp (sound! <| FirstOrder.SyntacticTheory.Delta1Definable.isDelta1 (T := T)) V inferInstance
    simp [models_iff] at this ⊢
    simp [SyntacticTheory.tDef, this],
  by intro v; simp [SyntacticTheory.codeIn, ←Matrix.constant_eq_singleton']⟩

variable (T V)

def _root_.LO.FirstOrder.SyntacticTheory.tCodeIn (T : SyntacticTheory L) [T.Delta1Definable] : (L.codeIn V).TTheory where
  thy := T.codeIn V
  pthy := T.tDef

def _root_.LO.FirstOrder.Theory.tCodeIn (T : Theory L) [T.Delta1Definable] : (L.codeIn V).TTheory where
  thy := T.codeIn V
  pthy := T.tDef

end LO.Arith
