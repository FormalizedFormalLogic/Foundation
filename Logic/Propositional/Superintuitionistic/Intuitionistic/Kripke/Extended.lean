import Logic.Vorspiel.BinaryRelations
import Logic.Propositional.Superintuitionistic.Intuitionistic.Kripke.Semantics

namespace LO.Propositional.Superintuitionistic

open Intuitionistic Kripke

variable {α β}

@[simp]
def Formula.Intuitionistic.Kripke.ExSatisfies (P : Frame α → Prop) (M : Model α β) (w : α) (p : Formula β) : Prop := (P M.frame) → (Intuitionistic.Kripke.Satisfies M w p)
notation w " ⊩ᴾ[" P "," M "] " p => Formula.Intuitionistic.Kripke.ExSatisfies P M w p

@[simp] lemma Formula.Intuitionistic.Kripke.ExSatisfies.iff_int {p : Formula β} : (w ⊩ᴾ[λ _ => True, M] p) ↔ (w ⊩ⁱ[M] p) := by simp;


@[simp]
def Theory.Intuitionistic.Kripke.ExSatisfies (P : Kripke.Frame α → Prop) (M : Kripke.Model α β) (w : α) (Γ : Theory β) := ∀ p ∈ Γ, (w ⊩ᴾ[P, M] p)
notation w " ⊩ᴾ[" P "," M "] " Γ => Theory.Intuitionistic.Kripke.ExSatisfies P M w Γ

lemma Theory.Intuitionistic.Kripke.ExSatisfies.iff_int {Γ : Theory β} : (w ⊩ᴾ[λ _ => True, M] Γ) ↔ (w ⊩ⁱ[M] Γ) := by simp; rfl;


@[simp]
def Formula.Intuitionistic.Kripke.ExModels (P : Kripke.Frame α → Prop) (M : Kripke.Model α β) (p : Formula β) : Prop := ∀ w, (w ⊩ᴾ[P, M] p)
notation M " ⊧ᴾ[" P "] " p => Formula.Intuitionistic.Kripke.ExModels P M p

@[simp] lemma Formula.Intuitionistic.Kripke.ExModels.iff_int {p : Formula β} : (M ⊧ᴾ[λ _ => True] p) ↔ (M ⊧ⁱ p) := by simp; rfl;


@[simp]
def Formula.Intuitionistic.Kripke.ExValid (P : ∀ {α}, Kripke.Frame α → Prop) (p : Formula β) : Prop := ∀ {α}, ∀ (M : Kripke.Model α β), (M ⊧ᴾ[P] p)
notation "⊧ᴾ[" P "] " p => Formula.Intuitionistic.Kripke.ExValid P p

@[simp] lemma Formula.Intuitionistic.Kripke.ExValid.iff_int {p : Formula β} : (⊧ᴾ[(λ _ => True)] p) ↔ (⊧ⁱ p) := by
  simp [Formula.Intuitionistic.Kripke.Valid];
  rfl;

@[simp]
def Formula.Intuitionistic.Kripke.ExConsequence (P : ∀ {α : Type u}, Kripke.Frame α → Prop) (Γ : Theory β) (p : Formula β) : Prop := ∀ {α : Type u}, ∀ (M : Kripke.Model α β) w, (w ⊩ᴾ[P, M] Γ) → (w ⊩ᴾ[P, M] p)
notation:50 Γ " ⊨ᴾ[" P "] " p => Formula.Intuitionistic.Kripke.ExConsequence P Γ p

@[simp] lemma Formula.Intuitionistic.Kripke.Consequence.iff_int : (Γ ⊨ᴾ[(λ _ => True)] p) ↔ (Γ ⊨ⁱ p) := by simp; rfl;

section LEM

def _root_.Full (rel : α → α → Prop) := ∀ ⦃x y : α⦄, rel x y ↔ x = y

lemma _root_.full_of_refl_antisymm_eucl {rel : α → α → Prop} (hRefl : Reflexive rel) (hAntisymm : AntiSymmetric rel) (hEucl : Euclidean rel) : Full rel := by
  intro x y;
  constructor;
  . intro hxy;
    have hxx := hRefl x;
    have hyx := hEucl hxy hxx;
    exact hAntisymm hxy hyx;
  . intro exy; simp_all; apply hRefl;

example : ⊧ᴾ[Full] (p ⋎ ~p) := by
  intro _ M w hf;
  by_cases h : w ⊩ⁱ[M] p;
  case pos => left; assumption;
  case neg =>
    right;
    simp [NegDefinition.neg];
    intro w' hw';
    have := hf.mp hw';
    simp_all;

end LEM

end LO.Propositional.Superintuitionistic
