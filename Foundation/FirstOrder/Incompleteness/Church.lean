module

public import Foundation.FirstOrder.Basic.Coding
public import Foundation.FirstOrder.Basic.PrimrecCoding
public import Foundation.FirstOrder.Incompleteness.RosserProvability
public import Foundation.FirstOrder.Arithmetic.R0.Representation
public import Foundation.FirstOrder.Incompleteness.Halting
public import Foundation.Meta.ClProver
public import Mathlib.Computability.Reduce

/-!
# Church's undecidability theorem

The set of sentences provable in an arithmetic theory `T ⊇ 𝗥₀` is not computable, whether `T` is
sound on `𝚺₁` sentences (`uncomputable_theory_of_sigma1Sound`) or merely consistent and extends
`𝗜𝚺₁` (`uncomputable_theory_of_consistent`). Provability in pure first-order logic is likewise
undecidable (`undecidability_first_order_logic`).
-/

@[expose] public section

namespace LO.FirstOrder.Arithmetic

open Bootstrapping Bootstrapping.Arithmetic

section Diagonalization

lemma computable_iff_sigma1_simulate {α β : Type*} [Primcodable α] [Primcodable β]
    {f : ℕ → ℕ} (hf : 𝚺₁-Function₁ f)
    {F : α → β} (h : ∀ a, f (Encodable.encode a) = Encodable.encode (F a)) :
    Computable F := by
  have hCode : Computable fun a : α ↦ f (Encodable.encode a) :=
    (computable_iff_sigma1.mpr hf).comp Computable.encode
  have hDecode :=
    Computable.ofOption ((Computable.decode (α := β)).comp hCode)
  exact hDecode.of_eq_tot fun a ↦ by simp [h a]

lemma computable₂_iff_sigma1_simulate {α β γ : Type*} [Primcodable α] [Primcodable β] [Primcodable γ]
    {f : ℕ → ℕ → ℕ} (hf : 𝚺₁-Function₂ f)
    {F : α → β → γ} (h : ∀ a b, f (Encodable.encode a) (Encodable.encode b) = Encodable.encode (F a b)) :
    Computable₂ F := by
  have hCode : Computable fun p : α × β ↦ f (Encodable.encode p.1) (Encodable.encode p.2) :=
    (computable₂_iff_sigma1.mpr hf).comp
      (Computable.encode.comp Computable.fst) (Computable.encode.comp Computable.snd)
  have hDecode :=
    Computable.ofOption ((Computable.decode (α := γ)).comp hCode)
  exact Computable₂.mk <| hDecode.of_eq_tot fun p ↦ by simp [h p.1 p.2]

variable {T : ArithmeticTheory} [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1]

theorem uncomputable_theory_of_sigma1Sound : ¬ComputablePred T.theory := by
  by_contra hC
  have hQuoteSubst :
      Computable₂ fun σ π : ArithmeticSemisentence 1 ↦ (σ/[⌜π⌝] : ArithmeticSentence) :=
    computable₂_iff_sigma1_simulate (f := substNumeral (V := ℕ)) (by definability)
      fun σ τ ↦ by simp [←Sentence.quote_eq_encode_nat, substNumeral_app_quote]
  have hSubst : Computable fun σ : ArithmeticSemisentence 1 ↦ (σ/[⌜σ⌝] : ArithmeticSentence) :=
    hQuoteSubst.comp Computable.id Computable.id
  have hD : ComputablePred (fun σ : ArithmeticSemisentence 1 ↦ T ⊬ σ/[⌜σ⌝]) :=
    ComputablePred.computable_of_manyOneReducible
      (ManyOneReducible.mk (fun σ ↦ T ⊬ σ) hSubst) hC.not
  let D : ℕ → Prop :=
    fun n ↦ (Encodable.decode (α := ArithmeticSemisentence 1) n).elim False
      (fun σ ↦ T ⊬ σ/[⌜σ⌝])
  have hRe : REPred D := by
    simpa [D] using REPred.iff_decoded_pred.mp hD.to_re
  have hδ : T ⊬ (codeOfREPred D)/[⌜codeOfREPred D⌝] ↔
      T ⊢ (codeOfREPred D)/[⌜codeOfREPred D⌝] := by
    simpa [D, Encodable.encodek, Arithmetic.gödelNumber'_eq_coe_encode]
      using rePred_weak_representation (T := T) hRe (x := Encodable.encode (codeOfREPred D))
  tauto

end Diagonalization

section ConsistencyOnly

variable {T : ArithmeticTheory} [𝗜𝚺₁ ⪯ T] [Entailment.Consistent T]

theorem uncomputable_theory_of_consistent : ¬ComputablePred T.theory := by
  by_contra hC
  let p : ℕ → Prop := fun n ↦ (Encodable.decode (α := ArithmeticSentence) n).elim False (fun σ ↦ T ⊢ σ)
  have hp : ComputablePred p := ComputablePred.iff_decoded_pred.mp hC
  let ψ : ArithmeticSemisentence 1 := codeOfComputablePred p
  let δ : ArithmeticSentence := fixedpoint (∼ψ)
  have hδ : T ⊢ δ 🡘 ∼(ψ/[⌜δ⌝]) := by simpa using diagonal (T := T) (∼ψ)
  have hp_iff : p (Encodable.encode δ) ↔ T ⊢ δ := by simp [p, Encodable.encodek]
  by_cases h : T ⊢ δ
  · have hψ : T ⊢ ψ/[⌜δ⌝] := by
      simpa [Arithmetic.gödelNumber'_eq_coe_encode] using
        codeOfComputablePred_provable hp (hp_iff.mpr h)
    apply Entailment.Consistent.not_bot (𝓢 := T)
    cl_prover [hδ, h, hψ]
  · have hnψ : T ⊢ ∼(ψ/[⌜δ⌝]) := by
      simpa [Arithmetic.gödelNumber'_eq_coe_encode] using
        codeOfComputablePred_provable_neg hp (hp_iff.not.mpr h)
    exact h (by cl_prover [hδ, hnψ])

end ConsistencyOnly

section PeanoMinusReduction

/-- Provability in pure first-order logic, i.e. provability from the empty theory, is
undecidable. -/
theorem undecidability_first_order_logic : ¬ComputablePred ((∅ : ArithmeticTheory).theory) := by
  have hDeduction (σ : ArithmeticSentence) :
      𝗣𝗔⁻ ⊢ σ ↔ (∅ : ArithmeticTheory) ⊢ PeanoMinus.finite.toFinset.conj 🡒 σ := by
    rw [Entailment.Equiv.iff.mp PeanoMinus.equiv_singleton_finiteConj σ, ←insert_empty_eq]
    exact Entailment.deduction_iff
  by_contra hC
  have hImpIntro : Computable fun σ : ArithmeticSentence ↦ PeanoMinus.finite.toFinset.conj 🡒 σ :=
    let c := Encodable.encode (∼PeanoMinus.finite.toFinset.conj : ArithmeticSentence)
    computable_iff_sigma1_simulate (f := fun e ↦ ⟪5, c, e⟫ + 1)
      (by definability)
      fun σ ↦ by
      simp [nat_pair_eq, c, Semiformula.imp_eq, Semiformula.encode_or,
        ← Semiformula.encode_eq_toNat, ← Semiformula.encode_eq_toNat]
  apply uncomputable_theory_of_sigma1Sound (T := 𝗣𝗔⁻) (ComputablePred.computable_of_manyOneReducible ?_ hC)
  refine ⟨fun σ ↦ PeanoMinus.finite.toFinset.conj 🡒 σ, ?_, ?_⟩
  . exact hImpIntro
  . exact hDeduction

end PeanoMinusReduction

end LO.FirstOrder.Arithmetic

end
