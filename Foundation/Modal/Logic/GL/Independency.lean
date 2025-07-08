import Foundation.Modal.Maximal.Unprovability
import Foundation.Modal.Kripke.Logic.GL.MDP


namespace LO.Modal

open LO.Entailment LO.Entailment.FiniteContext LO.Modal.Entailment
open Propositional

variable [DecidableEq α]


abbrev independency (φ : Formula α) := ∼□φ ⋏ ∼□(∼φ)

abbrev higherIndependency (φ : Formula α) : ℕ → Formula α
  | 0 => φ
  | n + 1 => independency (higherIndependency φ n)


namespace Logic.GL

variable {n : ℕ} {φ : Formula ℕ}

lemma unprovable_notbox : Hilbert.GL ⊬ ∼□φ := by
  by_contra hC;
  have : Hilbert.GL ⊢! ∼□φ ➝ ∼□⊥ := contra! (imply_box_distribute'! efq!)
  have : Hilbert.GL ⊢! ∼□⊥ := this ⨀ hC;
  have : Hilbert.Cl ⊢! (⊥ ➝ ⊥) ➝ ⊥ := by simpa using provable_verTranslated_Cl this;
  have := Hilbert.Cl.soundness this (λ _ => False);
  tauto;

lemma unprovable_independency : Hilbert.GL ⊬ independency φ := by
  by_contra hC;
  exact unprovable_notbox $ K!_left hC;

lemma unprovable_not_independency_of_consistency : Hilbert.GL ⊬ ∼(independency (∼□⊥)) := by
  by_contra hC;
  rcases modal_disjunctive (A!_of_ANNNN! $ ANN!_of_NK! hC) with (h | h);
  . exact unprovable_notbox h;
  . have : Hilbert.GL ⊢! ⊥ := unnec! $ of_NN! h;
    apply Consistent.not_bot inferInstance this;

/-
theorem undecidable_independency_of_consistency : Independent Hilbert.GL (independency (∼□⊥)) := by
  constructor;
  . exact unprovable_independency;
  . exact unprovable_not_independency_of_consistency;
-/


lemma unprovable_higherIndependency_of_consistency : Hilbert.GL ⊬ higherIndependency (∼□⊥) n := by
  induction n with
  | zero => exact unprovable_notbox;
  | succ n ih => exact unprovable_independency;

lemma unprovable_not_higherIndependency_of_consistency : Hilbert.GL ⊬ ∼(higherIndependency (∼□⊥) n) := by
  by_contra hC;
  induction n with
  | zero =>
    have : Hilbert.GL ⊢! ⊥ := unnec! $ of_NN! hC;
    apply Consistent.not_bot inferInstance this;
  | succ n ih =>
    rcases modal_disjunctive (A!_of_ANNNN! $ ANN!_of_NK! hC) with (h | h);
    . exact unprovable_higherIndependency_of_consistency h;
    . exact ih h;

/-
theorem undecidable_higherIndependency_of_consistency : Independent Hilbert.GL (higherIndependency (∼□⊥) n) := by
  constructor;
  . exact unprovable_higherIndependency_of_consistency;
  . exact unprovable_not_higherIndependency_of_consistency;
-/

end Logic.GL

end LO.Modal
