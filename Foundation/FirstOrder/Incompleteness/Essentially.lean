module

public import Foundation.FirstOrder.Incompleteness.Church
public import Foundation.Logic.Decidability
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Formula.Computable

/-!
# Essential undecidability and essential incompleteness

## References

- [Kur23, Theorem 2.7]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

namespace FFL.FirstOrder

open Encodable FFL.Entailment Arithmetic Bootstrapping

namespace Theory

/-- A consistent, complete r.e. theory is decidable. -/
lemma computablePred_theory_of_complete {L : Language} [L.Encodable] [L.LORDefinable]
    [L.Primcodable] [L.DecidableEq] {T : Theory L} [T.RE] [Consistent T]
    (h : Entailment.Complete T) : ComputablePred (· ∈ T.theory) := by
  have hc : REPred fun σ : Sentence L ↦ T ⊬ σ :=
    ((rePred_provable (T := T)).comp Sentence.computable_neg).of_eq fun σ ↦ by
      have : ¬(T ⊢ σ ∧ T ⊢ ∼σ) := fun h ↦ not_consistent_iff_inconsistent.mpr
        (inconsistent_of_provable_of_unprovable h.1 h.2) inferInstance
      have := h.con σ
      tauto
  exact ComputablePred.computable_iff_re_compl_re'.mpr ⟨rePred_provable, hc⟩

section completion

variable {L : Language} [L.Encodable] (U : Theory L)

open Classical in
/-- Extend `c` by the sentence coded by `n` or by its negation, whichever keeps `U + c`
consistent. -/
noncomputable def completionStep (c : Sentence L) (n : ℕ) : Sentence L :=
  (decode (α := Sentence L) n).casesOn c fun φ ↦ if U ⊢ c 🡒 ∼φ then c ⋏ ∼φ else c ⋏ φ

noncomputable def completionChain : ℕ → Sentence L
  | 0 => ⊤
  | n + 1 => U.completionStep (completionChain n) n

/-- A complete extension of `U`, decidable whenever `U` is. -/
def completion : Theory L := {σ | U ⊢ U.completionChain (encode σ + 1) 🡒 σ}

variable {U}

lemma completionChain_succ (n : ℕ) :
    U.completionChain (n + 1) = U.completionStep (U.completionChain n) n := rfl

lemma completionChain_imp_of_le {m n : ℕ} (h : m ≤ n) :
    U ⊢ U.completionChain n 🡒 U.completionChain m := by
  induction n, h using Nat.le_induction with
  | base => cl_prover
  | succ n _ ih =>
    have : U ⊢ U.completionChain (n + 1) 🡒 U.completionChain n := by
      rw [completionChain_succ, completionStep]
      rcases decode (α := Sentence L) n with _ | φ
      · cl_prover
      · dsimp only
        split <;> cl_prover
    cl_prover [ih, this]

lemma completionChain_unrefutable [Consistent U] (n : ℕ) : U ⊬ ∼U.completionChain n := by
  induction n with
  | zero => exact fun h ↦ Consistent.not_bot (𝓢 := U) (by cl_prover [h])
  | succ n ih =>
    rw [completionChain_succ, completionStep]
    rcases decode (α := Sentence L) n with _ | φ
    · exact ih
    · dsimp only
      split
      next hφ => exact fun h ↦ ih (by cl_prover [h, hφ])
      next hφ => exact fun h ↦ hφ (by cl_prover [h])

lemma completionChain_decides (σ : Sentence L) :
    U ⊢ U.completionChain (encode σ + 1) 🡒 σ ∨ U ⊢ U.completionChain (encode σ + 1) 🡒 ∼σ := by
  rw [completionChain_succ, completionStep, encodek]
  dsimp only
  split
  · right; cl_prover
  · left; cl_prover

instance : U ⪯ U.completion := WeakerThan.ofAxm! fun {σ} hσ ↦
  by_axm (show σ ∈ U.completion from (C_of_conseq (by_axm hσ) : U ⊢ _ 🡒 σ))

instance [Consistent U] : Entailment.Complete U.completion :=
  complete_def.mpr fun σ ↦ by
    rcases completionChain_decides (U := U) σ with h | h
    · exact .inl (by_axm h)
    · apply Or.inr ∘ by_axm
      rcases completionChain_decides (U := U) (∼σ) with h' | h'
      · exact h'
      · obtain ⟨m, hm₁, hm₂⟩ : ∃ m, encode σ + 1 ≤ m ∧ encode (∼σ) + 1 ≤ m :=
          ⟨_, le_max_left .., le_max_right ..⟩
        have h₁ := completionChain_imp_of_le (U := U) hm₁
        have h₂ := completionChain_imp_of_le (U := U) hm₂
        have : U ⊢ ∼U.completionChain m := by cl_prover [h, h', h₁, h₂]
        exact absurd this (completionChain_unrefutable _)

instance [L.DecidableEq] [Consistent U] : Consistent U.completion := by
  apply consistent_compact.mpr
  intro 𝓕 h𝓕 hfin
  obtain ⟨m, hm⟩ := (((Set.adjunctiveSet_finite_iff 𝓕).mp hfin).image
    fun σ ↦ encode σ + 1).bddAbove
  have : Consistent (adjoin (U.completionChain m) U) := consistent_iff_unprovable_bot.mpr
    fun h ↦ by
      have : U ⊢ U.completionChain m 🡒 ⊥ := deduction_iff.mp h
      exact completionChain_unrefutable (U := U) m (by cl_prover [this])
  apply Consistent.of_le this
  apply WeakerThan.ofAxm!
  intro σ hσ
  have h₁ : U ⊢ U.completionChain (encode σ + 1) 🡒 σ := h𝓕 hσ
  have h₂ := completionChain_imp_of_le (U := U) (hm ⟨σ, hσ, rfl⟩)
  exact deduction_iff.mpr (by cl_prover [h₁, h₂])

variable [L.LORDefinable] [L.Primcodable]

lemma computable_completionChain (hU : ComputablePred fun σ : Sentence L ↦ U ⊢ σ) :
    Computable U.completionChain := by
  obtain ⟨_, hD⟩ := hU
  have hStep : Computable₂ U.completionStep := by
    have : Computable₂ fun (p : Sentence L × ℕ) (φ : Sentence L) ↦
        bif decide (U ⊢ p.1 🡒 ∼φ) then p.1 ⋏ ∼φ else p.1 ⋏ φ := by
      have hc : Computable fun q : (Sentence L × ℕ) × Sentence L ↦ q.1.1 :=
        Computable.fst.comp Computable.fst
      have hn : Computable fun q : (Sentence L × ℕ) × Sentence L ↦ ∼q.2 :=
        Sentence.computable_neg.comp Computable.snd
      exact Computable.cond (hD.comp (Sentence.computable₂_imp.comp hc hn))
        (Semiformula.primrec₂_and.to_comp.comp hc hn)
        (Semiformula.primrec₂_and.to_comp.comp hc Computable.snd)
    exact (Computable.option_casesOn (Computable.decode.comp Computable.snd)
      Computable.fst this).of_eq fun p ↦ by
        simp only [completionStep]
        cases decode (α := Sentence L) p.2 <;> simp
  exact (Computable.nat_rec (f := id) (g := fun _ ↦ (⊤ : Sentence L))
    (h := fun _ p ↦ U.completionStep p.2 p.1) Computable.id (Computable.const _)
    (hStep.comp (Computable.snd.comp Computable.snd) (Computable.fst.comp Computable.snd))).of_eq
    fun n ↦ by induction n <;> simp_all [completionChain]

lemma computablePred_completion (hU : ComputablePred fun σ : Sentence L ↦ U ⊢ σ) :
    ComputablePred (· ∈ U.completion) := by
  obtain ⟨_, hD⟩ := hU
  exact ⟨Classical.decPred _, (hD.comp <| Sentence.computable₂_imp.comp
    ((computable_completionChain ⟨_, hD⟩).comp (Computable.succ.comp Computable.encode))
    Computable.id).of_eq fun σ ↦ by simp only [completion, Set.mem_ofPred_eq]; congr⟩

end completion

section essentially

variable {L : Language} [L.Encodable] [L.LORDefinable] [L.Primcodable] [L.DecidableEq]

/-- A theory is essentially undecidable if and only if it is essentially incomplete.

- [Kur23, Theorem 2.7]
-/
theorem essentiallyUndecidable_iff_essentiallyIncomplete {T : Theory L} :
    EssentiallyUndecidable T (fun _ ↦ True) ↔ EssentiallyIncomplete T Theory.RE := by
  constructor
  · rintro ⟨h⟩
    constructor
    intro U hTU hU _
    by_contra hc
    exact h U hTU hU trivial
      ⟨computablePred_theory_of_complete (not_incomplete_iff_complete.mp hc)⟩
  · rintro ⟨h⟩
    constructor
    intro U hTU _ _ ⟨hd⟩
    exact not_complete_iff_incomplete.mpr
      (h _ (hTU.trans inferInstance) inferInstance ⟨(computablePred_completion hd).to_re⟩)
      inferInstance

end essentially

end Theory

end FFL.FirstOrder
