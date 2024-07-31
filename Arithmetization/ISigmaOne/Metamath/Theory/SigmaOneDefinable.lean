import Arithmetization.ISigmaOne.Metamath.Coding
import Arithmetization.ISigmaOne.Metamath.Proof.Typed

namespace LO.Arith

open LO.FirstOrder

variable {L : Language} [(k : ℕ) → Encodable (L.Func k)] [(k : ℕ) → Encodable (L.Rel k)] [DefinableLanguage L]

class _root_.LO.FirstOrder.SyntacticTheory.Δ₁Definable (T : SyntacticTheory L) extends Arith.LDef.TDef L.lDef where
  mem_iff {σ} : σ ∈ T ↔ 𝐈𝚺₁ ⊢₌! ch.val/[(⌜σ⌝ : Semiterm ℒₒᵣ Empty 0)]
  isΔ₁ : 𝐈𝚺₁ ⊢₌! “∀ x, !ch.sigma x ↔ !ch.pi x”

abbrev _root_.LO.FirstOrder.Theory.Δ₁Definable (T : Theory L) := SyntacticTheory.Δ₁Definable (L := L) ↑T

def _root_.LO.FirstOrder.SyntacticTheory.tDef (T : SyntacticTheory L) [d : T.Δ₁Definable] : Arith.LDef.TDef L.lDef := d.toTDef

abbrev _root_.LO.FirstOrder.Theory.tDef (T : Theory L) [d : T.Δ₁Definable] : Arith.LDef.TDef L.lDef := d.toTDef

variable {V : Type*} [Zero V] [One V] [Add V] [Mul V] [LT V] [V ⊧ₘ* 𝐈𝚺₁]

variable {T : SyntacticTheory L} [T.Δ₁Definable]

variable (T V)

def _root_.LO.FirstOrder.SyntacticTheory.codeIn : (L.codeIn V).Theory where
  set := {x | V ⊧/![x] T.tDef.ch.val}

abbrev _root_.LO.FirstOrder.Theory.codeIn (T : Theory L) [T.Δ₁Definable] : (L.codeIn V).Theory := SyntacticTheory.codeIn (L := L) V T

variable {T V}

lemma Language.SyntacticTheory.codeIn_iff : x ∈ T.codeIn V ↔ V ⊧/![x] T.tDef.ch.val := iff_of_eq rfl

lemma mem_coded_theory {σ} (h : σ ∈ T) : ⌜σ⌝ ∈ T.codeIn V := Language.SyntacticTheory.codeIn_iff.mpr <| by
  have := consequence_iff_add_eq.mp (sound! <| SyntacticTheory.Δ₁Definable.mem_iff.mp h) V inferInstance
  simpa [models_iff, Semiformula.syntacticformula_goedelNumber_def, numeral_eq_natCast] using this

instance tDef_defined : (T.codeIn V).Defined T.tDef where
  defined := ⟨by
    intro v
    rw [show v = ![v 0] from Matrix.constant_eq_singleton']
    have := consequence_iff_add_eq.mp (sound! <| FirstOrder.SyntacticTheory.Δ₁Definable.isΔ₁ (T := T)) V inferInstance
    simp [models_iff] at this ⊢
    simp [SyntacticTheory.tDef, this],
  by intro v; simp [SyntacticTheory.codeIn, ←Matrix.constant_eq_singleton']⟩

variable (T V)

def _root_.LO.FirstOrder.SyntacticTheory.tCodeIn (T : SyntacticTheory L) [T.Δ₁Definable] : (L.codeIn V).TTheory where
  thy := T.codeIn V
  pthy := T.tDef

def _root_.LO.FirstOrder.Theory.tCodeIn (T : Theory L) [T.Δ₁Definable] : (L.codeIn V).TTheory where
  thy := T.codeIn V
  pthy := T.tDef

end LO.Arith
