import Logic.Logic.System
import Logic.Logic.HilbertStyle
import Logic.FirstOrder.Basic.Formula

open LO.System

namespace LO.FirstOrder.Theory

open Subformula

variable
  {L : Language.{u}}
  [∀ k, DecidableEq (L.func k)] [∀ k, DecidableEq (L.rel k)] [System (Sentence L)]
  (T : Theory L)

class Complete where
  complete : System.Complete T

class Incomplete where
  incomplete : ¬System.Complete T

class Consistent where
  consistent : System.Consistent T

class Inconsistent where
  inconsistent : ¬System.Consistent T

@[simp]
lemma false_of_consistent_inconsistent [c : Consistent T] [i: Inconsistent T] : False := by
  exact i.inconsistent c.consistent

section PropositionalCalculus

open System.Intuitionistic System.Deduction

variable {T : Theory L}
variable [Intuitionistic (Sentence L)]
variable [Deduction (Sentence L)]

instance : BotDef (Sentence L) where
  bot_def := by simp;

instance : DoubleNeg (Sentence L) where
  double_neg := by simp;

instance : ImpDef (Sentence L) where
  imp_def := by simp [imp_eq];

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
  exact hc.consistent.false (no_contradiction hp hr).some;

lemma consistent_or {T} {σ : Sentence L} : Theory.Inconsistent (T ∪ {σ}) → T ⊢! ~σ := by
  intro h
  have : T ⊢! σ ⟶ ⊥ := deduction.mpr (provable_falsum_of_inconsistent h)
  exact neg₁ T σ ⊤ ⨀ (hyp_right (Intuitionistic.verum _) _) ⨀ this

@[simp]
lemma axm : T ∪ {σ} ⊢! σ := deduction.mp (imp_id _)

lemma imply_intro {σ π} : (T ⊢! σ) → ((T ⊢! σ) → (T ⊢! π)) → (T ⊢! σ ⟶ π) := λ H₁ H₂ => hyp_right (H₂ H₁) _

lemma imply_dilemma : T ⊢! σ ⟶ (π ⟶ ρ) → T ⊢! (σ ⟶ π) → T ⊢! (σ ⟶ ρ) := by
  intro H₁ H₂;
  exact deduction.mpr $ (deduction.mp H₁) ⨀ (deduction.mp H₂);

lemma elim_and_left_dilemma : (T ⊢! (σ ⋏ π) ⟶ ρ) → (T ⊢! σ ⟶ π) → (T ⊢! σ ⟶ ρ) := by
  intro H₁ H₂;
  apply deduction.mpr;
  exact (weakening H₁) ⨀ (and_split axm $ deduction.mp H₂);

end PropositionalCalculus

end LO.FirstOrder.Theory
