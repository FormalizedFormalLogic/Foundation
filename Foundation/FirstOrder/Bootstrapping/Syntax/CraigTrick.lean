module

public import Foundation.FirstOrder.Arithmetic.Sigma1WitnessForm
public import Foundation.FirstOrder.Bootstrapping.Syntax.Theory
public import Foundation.FirstOrder.Bootstrapping.Syntax.Formula.Iteration
public import Foundation.FirstOrder.Basic.Padding

/-!
# Craig's trick
-/

@[expose] public section

namespace LO.FirstOrder.Theory

open LO.FirstOrder.Arithmetic

variable {L : Language} [L.Encodable] [L.LORDefinable]

noncomputable def «Σ₁witness» (T : Theory L) [T.«Σ₁»] : 𝚺₀.Semisentence 2 :=
  let h := exists_delta0_witness_form.{0} T.«Σ₁ch».sigma_prop;
  .mkSigma h.choose h.choose_spec.1

lemma «Σ₁witness_spec» (T : Theory L) [T.«Σ₁»]
    (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (e : Fin 1 → V) :
    V ⊧/e T.«Σ₁ch».val ↔ ∃ w, V ⊧/(w :> e) T.«Σ₁witness».val := by
  simpa [«Σ₁witness»] using
    (exists_delta0_witness_form.{0} T.«Σ₁ch».sigma_prop).choose_spec.2 (V := V) e

end LO.FirstOrder.Theory

namespace LO.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

variable {L : Language} [L.Encodable] [L.LORDefinable]

lemma quote_weight (k : ℕ) :
    (⌜(Semiformula.weight k : Proposition L)⌝ : V) = qqVerums (k : V) := by
  induction k with
  | zero => simp [Semiformula.weight]
  | succ k ih =>
    change ⌜(⊤ : Proposition L) ⋏ Semiformula.weight k⌝ = _
    simp [ih]

lemma quote_padding (φ : Proposition L) (k : ℕ) :
    (⌜φ.padding k⌝ : V) = ⌜φ⌝ ^⋏ qqVerums (k : V) := by
  change ⌜φ ⋏ Semiformula.weight k⌝ = _
  simp [quote_weight]

namespace Sentence

lemma quote_padding (σ : Sentence L) (k : ℕ) :
    (⌜σ.padding k⌝ : V) = ⌜σ⌝ ^⋏ qqVerums (k : V) := by
  simpa [Sentence.quote_def] using
    LO.FirstOrder.Arithmetic.Bootstrapping.quote_padding (V := V) (Rewriting.emb σ) k

end Sentence

end LO.FirstOrder.Arithmetic.Bootstrapping
