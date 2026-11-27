module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Formula.Coding
public import Foundation.FirstOrder.Arithmetic.R0.Representation

/-!
# Computability of logical connectives on sentences
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder.Sentence

open Arithmetic Bootstrapping

variable {L : Language} [L.Encodable] [L.LORDefinable] [L.Primcodable]

lemma computable_neg : Computable (fun σ : Sentence L ↦ ∼σ) :=
  computable_iff_sigma1_simulate (f := neg (V := ℕ) L) (by definability)
    fun σ ↦ by simp [← Sentence.quote_eq_encode_nat, Sentence.quote_def, Semiformula.quote_def]

lemma computable₂_imp : Computable₂ (fun σ τ : Sentence L ↦ σ 🡒 τ) :=
  (Semiformula.primrec₂_or.to_comp.comp (computable_neg.comp Computable.fst) Computable.snd).of_eq
    fun _ ↦ by simp [Semiformula.imp_eq]

end FFL.FirstOrder.Sentence
