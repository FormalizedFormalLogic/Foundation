import Arithmetization.ISigmaOne.Metamath.Coding
import Arithmetization.ISigmaOne.Metamath.Proof.Typed

namespace LO.Arith

open LO.FirstOrder

variable {L : Language} [(k : ℕ) → Encodable (L.Func k)] [(k : ℕ) → Encodable (L.Rel k)] [DefinableLanguage L]

class _root_.LO.FirstOrder.Theory.Sigma₁Definable (T : Theory L) extends Arith.LDef.TDef L.lDef where
  mem_iff {σ} : σ ∈ T ↔ 𝐈𝚺₁ ⊢₌! ch.val/[(⌜σ⌝ : Semiterm ℒₒᵣ Empty 0)]
  fvfree : 𝐈𝚺₁ ⊢₌! “∀ σ, !ch σ → !L.lDef.isFVFreeDef 0 σ”

def _root_.LO.FirstOrder.Theory.tDef (T : Theory L) [d : T.Sigma₁Definable] : Arith.LDef.TDef L.lDef := d.toTDef

variable {V : Type*} [Zero V] [One V] [Add V] [Mul V] [LT V] [V ⊧ₘ* 𝐈𝚺₁]

variable {T : Theory L} [T.Sigma₁Definable]

variable (T V)

def _root_.LO.FirstOrder.Theory.codeIn : (L.codeIn V).Theory where
  set := {x | V ⊧/![x] T.tDef.ch.val}
  set_fvFree := by
    intro x hx
    have : ∀ x, V ⊧/![x] T.tDef.ch.val → (L.codeIn V).IsFVFree 0 x := by
      simpa [models_iff, (isFVFree_defined (V := V) (L.codeIn V)).df.iff] using
        consequence_iff_add_eq.mp (sound! <| LO.FirstOrder.Theory.Sigma₁Definable.fvfree (T := T)) V inferInstance
    exact this x hx

variable {T V}

lemma Language.Theory.codeIn_iff : x ∈ T.codeIn V ↔ V ⊧/![x] T.tDef.ch.val := iff_of_eq rfl

lemma mem_coded_theory {σ} (h : σ ∈ T) : ⌜σ⌝ ∈ T.codeIn V := Language.Theory.codeIn_iff.mpr <| by
  have := consequence_iff_add_eq.mp (sound! <| Theory.Sigma₁Definable.mem_iff.mp h) V inferInstance
  simpa [models_iff, Semiformula.sentence_goedelNumber_def, numeral_eq_natCast] using this

instance : (T.codeIn V).Defined T.tDef where
  defined := by intro v; simp [Theory.codeIn, ←Matrix.constant_eq_singleton']

end LO.Arith
