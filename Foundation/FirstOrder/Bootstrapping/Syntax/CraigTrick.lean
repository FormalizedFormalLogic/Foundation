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
