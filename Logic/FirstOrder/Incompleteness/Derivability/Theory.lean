import Logic.Logic.System
import Logic.FirstOrder.Basic.Formula
import Logic.AutoProver.Prover

open LO.System

namespace LO.FirstOrder.Theory

open Subformula

variable
  {L : Language.{u}}
  [∀ k, DecidableEq (L.Func k)] [∀ k, DecidableEq (L.Rel k)] [System (Sentence L)] [Gentzen (Sentence L)] [LawfulTwoSided (Sentence L)]
  (T : Theory L)

class Complete where
  complete : System.Complete T

class Incomplete where
  incomplete : ¬System.Complete T

lemma false_of_complete_incomplete [c : Complete T] [i: Incomplete T] : False := by
  exact i.incomplete c.complete

class Consistent where
  consistent : System.Consistent T

class Inconsistent where
  inconsistent : ¬System.Consistent T

lemma false_of_consistent_inconsistent [c : Consistent T] [i: Inconsistent T] : False := by
  exact i.inconsistent c.consistent

section PropositionalCalculus

variable {T : Theory L}
instance : Subtheory T (T ∪ {σ}) where
  sub := by
    intro σ' h;
    exact weakening h (by simp)

@[simp]
lemma weakening [hs : Subtheory T₀ T] : (T₀ ⊢! σ) → (T ⊢! σ) := by
  simp;
  intro H;
  exact ⟨hs.sub H⟩;

lemma provable_falsum_of_inconsistent {T : Theory L} : Theory.Inconsistent T → T ⊢! ⊥ := by
  intro h; by_contra A
  have : Consistent T := ⟨⟨fun b => A ⟨b⟩⟩⟩;
  exact false_of_consistent_inconsistent T;

@[simp]
lemma broken_consistent [hc : Theory.Consistent T] (hp : T ⊢! σ) (hr : T ⊢! ~σ) : False := by
  have : T ⊢! ⊥ := by prover [hp, hr];
  exact hc.consistent.false this.some;

lemma consistent_or {T} {σ : Sentence L} : Theory.Inconsistent (T ∪ {σ}) → T ⊢! ~σ := by
  intro h
  have := provable_falsum_of_inconsistent h;
  have : T ⊢! σ ⟶ ⊥ := sorry; -- deduction.mpr (provable_falsum_of_inconsistent h)
  exact by prover [this];

@[simp]
lemma axm : T ∪ {σ} ⊢! σ := sorry

lemma imply_dilemma (h₁ : T ⊢! σ ⟶ π ⟶ ρ) (h₂ : T ⊢! σ ⟶ π) : T ⊢! σ ⟶ ρ := by prover [h₁, h₂];

lemma elim_and_left_dilemma (h₁ : T ⊢! (σ ⋏ π) ⟶ ρ) (h₂ : T ⊢! σ ⟶ π) : (T ⊢! σ ⟶ ρ) := by prover [h₁, h₂];

end PropositionalCalculus

end LO.FirstOrder.Theory
