module

public import Foundation.FirstOrder.Arithmetic.R0.Cobham
public import Foundation.FirstOrder.Incompleteness.Church
public import Foundation.Logic.Decidability

/-!
# Essential undecidability of $\mathsf{R}_0$

A first-order theory is essentially undecidable if every consistent extension of it in its
language is undecidable. $\mathsf{R}_0$ is essentially undecidable
(`R0.undecidable_of_consistent`): diagonalizing against a decision procedure through the weak
representation of computable functions by Cobham's order.

## References

- [Sve08]
- [HH14]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder

variable {L : Language} [L.Encodable] [L.Primcodable]

class Theory.EssentiallyUndecidable (T : Theory L) : Prop where
  undecidable_of_consistent : ∀ U : Theory L, T ⪯ U → Entailment.Consistent U →
    Entailment.Undecidable U

namespace Theory.EssentiallyUndecidable

theorem undecidable (T : Theory L) [T.EssentiallyUndecidable] [Entailment.Consistent T] :
    Entailment.Undecidable T :=
  undecidable_of_consistent (T := T) T (Entailment.WeakerThan.refl T) inferInstance

lemma of_weakerThan (T U : Theory L) [T.EssentiallyUndecidable] [T ⪯ U] :
    U.EssentiallyUndecidable where
  undecidable_of_consistent V hUV hV :=
    undecidable_of_consistent (T := T) V (Entailment.WeakerThan.trans inferInstance hUV) hV

instance (T : Theory L) [T.EssentiallyUndecidable] : Entailment.EssentiallyUndecidable T where
  essentially_undec U hTU hU := undecidable_of_consistent U hTU <|
    Entailment.consistent_of_incomplete (h := hU)

end Theory.EssentiallyUndecidable

namespace Arithmetic.R0

open Bootstrapping Bootstrapping.Arithmetic

theorem undecidable_of_consistent (T : ArithmeticTheory) [𝗥₀ ⪯ T]
    [Entailment.Consistent T] : Entailment.Undecidable T := by
  rintro ⟨hC⟩
  have hQuoteSubst :
      Computable₂ fun σ π : ArithmeticSemisentence 1 ↦ (σ/[⌜π⌝] : ArithmeticSentence) :=
    computable₂_iff_sigma1_simulate (f := substNumeral (V := ℕ)) (by definability)
      fun σ τ ↦ by simp [← Sentence.quote_eq_encode_nat, substNumeral_app_quote]
  have hSubst : Computable fun σ : ArithmeticSemisentence 1 ↦ (σ/[⌜σ⌝] : ArithmeticSentence) :=
    hQuoteSubst.comp Computable.id Computable.id
  have hD : ComputablePred fun σ : ArithmeticSemisentence 1 ↦ T ⊢ σ/[⌜σ⌝] :=
    ComputablePred.computable_of_manyOneReducible (ManyOneReducible.mk (fun σ ↦ T ⊢ σ) hSubst) hC
  let D : ℕ → Prop :=
    fun n ↦ (Encodable.decode (α := ArithmeticSemisentence 1) n).elim False
      fun σ ↦ T ⊢ σ/[⌜σ⌝]
  obtain ⟨_, hDdec⟩ : ComputablePred D := ComputablePred.iff_decoded_pred.mp hD
  have hγ := cobhamRepresentation_spec
    (Computable.cond hDdec (Computable.const 0) (Computable.const 1))
  generalize cobhamRepresentation _ = γ at hγ
  let δ : ArithmeticSemisentence 1 := “x. ¬!γ x 0”
  have hδ : D (Encodable.encode δ) ↔ T ⊢ δ/[⌜δ⌝] := by simp [D, Encodable.encodek]
  have : 𝗘𝗤 ℒₒᵣ ⪯ T := Entailment.WeakerThan.trans (𝓣 := 𝗥₀) inferInstance inferInstance
  by_cases h : T ⊢ δ/[⌜δ⌝]
  · apply Entailment.Consistent.not_bot (𝓢 := T)
    apply complete.{0} T
    intro M _ _
    have hR0 : M↓[ℒₒᵣ] ⊧* 𝗥₀ := ModelsTheory.of_provably_subtheory M 𝗥₀ T inferInstance
    have h₁ := models_of_provable hR0 (hγ (Encodable.encode δ))
    have h₂ := models_of_provable (M := M) inferInstance h
    simp [hδ.mpr h, models_iff, δ, Arithmetic.gödelNumber'_eq_coe_encode] at h₁ h₂
    simp_all
  · apply h
    apply complete.{0} T
    intro M _ _
    have hR0 : M↓[ℒₒᵣ] ⊧* 𝗥₀ := ModelsTheory.of_provably_subtheory M 𝗥₀ T inferInstance
    have h₁ := models_of_provable hR0 (hγ (Encodable.encode δ))
    simp [hδ.not.mpr h, models_iff] at h₁
    simpa [models_iff, δ, Arithmetic.gödelNumber'_eq_coe_encode, h₁]
      using numeral_ne_numeral_of_ne (M := M) zero_ne_one

instance : (𝗥₀ : ArithmeticTheory).EssentiallyUndecidable where
  undecidable_of_consistent T _ _ := undecidable_of_consistent T

theorem undecidable : Entailment.Undecidable 𝗥₀ := Theory.EssentiallyUndecidable.undecidable 𝗥₀

end Arithmetic.R0

end FFL.FirstOrder
