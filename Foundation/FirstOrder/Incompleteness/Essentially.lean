import Foundation.FirstOrder.Incompleteness.First

namespace LO.FirstOrder


namespace ArithmeticAxiom

variable {T : ArithmeticAxiom} {i : ℕ}

open Classical
open Encodable

protected def computableExpansion.next (T : ArithmeticAxiom) (σ : ArithmeticSentence) : ArithmeticAxiom := if Entailment.Consistent (insert σ T) then (insert σ T) else (insert (∼σ) T)

protected def computableExpansion.indexed (T : ArithmeticAxiom) : ℕ → ArithmeticAxiom
  | 0 => T
  | i + 1 =>
    match (decode i) with
    | some σ => computableExpansion.next (computableExpansion.indexed T i) σ
    | none => computableExpansion.indexed T i

local notation:max T"[" i "]" => computableExpansion.indexed T i

namespace computableExpansion

lemma indexed_mem_either : σ ∈ T[(encode σ) + 1] ∨ ∼σ ∈ T[(encode σ) + 1] := by
  simp only [encodek, computableExpansion.indexed, computableExpansion.next];
  split <;> tauto;

lemma indexed_provable_either : T[(encode σ) + 1] ⊢! σ ∨ T[(encode σ) + 1] ⊢! ∼σ := by
  rcases indexed_mem_either (T := T) (σ := σ) with (h | h);
  . left;
    apply Entailment.Axiomatized.provable_axm;
    simpa;
  . right;
    apply Entailment.Axiomatized.provable_axm;
    simpa;

lemma indexed_consistent_next : Entailment.Consistent T[i] → Entailment.Consistent T[i + 1] := by
  simp only [computableExpansion.indexed, computableExpansion.next];
  intro h;
  split;
  . split;
    . simpa;
    . sorry;
  . assumption;

lemma indexed_consistent [Entailment.Consistent T] : Entailment.Consistent T[i] := by
  induction i with
  | zero => simpa [computableExpansion.indexed];
  | succ i hi => apply indexed_consistent_next hi;

lemma indexed_weakerThan_next : T[i] ⪯ T[i + 1] := by
  simp only [computableExpansion.indexed, computableExpansion.next];
  split;
  . split <;>
    . apply Entailment.Axiomatized.weakerThanOfSubset;
      simp;
  . tauto;

lemma indexed_weakerThan_original : T ⪯ T[i] := by
  induction i with
  | zero => simp [computableExpansion.indexed];
  | succ i hi =>
    calc
      T ⪯ T[i]     := by simpa;
      _ ⪯ T[i + 1] := indexed_weakerThan_next;

end computableExpansion

def computableExpansion (T : ArithmeticAxiom) : ArithmeticAxiom := ⋃ i, T[i]

local notation:max T"∞" => computableExpansion T

namespace computableExpansion

instance weakerThan_indexed : T[i] ⪯ T∞ := by
  apply Entailment.Axiomatized.weakerThanOfSubset;
  intro σ hσ;
  simp only [computableExpansion, Set.mem_iUnion];
  use i;

instance weakerThan_original : T ⪯ T∞ := by
  nth_rw 1 [(show T = T[0] by rfl)];
  apply weakerThan_indexed;

lemma consistent_of_consistent : Entailment.Consistent T → Entailment.Consistent T∞ := by
  simp [Entailment.consistent_iff_exists_unprovable]
  intro σ hσ;
  use σ;
  sorry;

instance [Entailment.Consistent T] : Entailment.Consistent T∞ := by
  apply consistent_of_consistent;
  infer_instance;

lemma complete : Entailment.Complete T∞ := by
  intro σ;
  rcases indexed_provable_either with (h | h);
  . left; apply weakerThan_indexed.pbl h;
  . right; apply weakerThan_indexed.pbl h;

end computableExpansion

end ArithmeticAxiom



lemma Arithmetic.iff_essentially_incomplete_essentially_undecidable (T : ArithmeticAxiom) :
  -- TODO: [Theory.Δ₁ U.toTheory] should be rewrited to r.e.
  (∀ U : ArithmeticAxiom, T ⪯ U → [Entailment.Consistent U] → [Theory.Δ₁ U.toTheory] → ¬Entailment.Complete (U : Axiom ℒₒᵣ))
  ↔
  (∀ U : ArithmeticAxiom, T ⪯ U → [Entailment.Consistent U] → ¬ComputablePred (fun n : ℕ ↦ ∃ σ : ArithmeticSentence, n = ⌜σ⌝ ∧ U ⊢! σ))
  := by
  constructor;
  . intro h S _ _;
    sorry;
  . contrapose!;
    rintro ⟨U, _, _, _, hU⟩;
    use U.computableExpansion;
    refine ⟨?_, ?_, ?_⟩;
    . calc
        T ⪯ U := by assumption;
        _ ⪯ U.computableExpansion := inferInstance;
    . infer_instance;
    . sorry;

end LO.FirstOrder
