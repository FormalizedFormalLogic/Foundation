import Foundation.Modal.Hilbert.Maximal.Unprovability
import Foundation.Modal.Kripke.Hilbert.GL.MDP

namespace LO.Modal

open Entailment
open Propositional

variable [DecidableEq α]

abbrev independency (φ : Formula α) := ∼□φ ⋏ ∼□(∼φ)

abbrev higherIndependency (φ : Formula α) : ℕ → Formula α
  | 0 => φ
  | n + 1 => independency (higherIndependency φ n)

namespace Hilbert.GL

variable {φ : Formula ℕ}

lemma unprovable_notbox : Hilbert.GL ⊬ ∼□φ := by
  by_contra hC;
  have : Hilbert.GL ⊢! ∼□φ ➝ ∼□⊥ := contra₀'! (imply_box_distribute'! efq!)
  have : Hilbert.GL ⊢! ∼□⊥ := this ⨀ hC;
  have : Hilbert.Cl ⊢! (⊥ ➝ ⊥) ➝ ⊥ := by simpa using provable_verTranslated_Cl this;
  have := Hilbert.Cl.Classical.soundness this ⟨(λ _ => False)⟩;
  tauto;

lemma unprovable_independency : Hilbert.GL ⊬ independency φ := by
  by_contra hC;
  exact unprovable_notbox $ φ!_of_kφψ! hC;

lemma unprovable_not_independency_of_consistency : Hilbert.GL ⊬ ∼(independency (∼□⊥)) := by
  by_contra hC;
  rcases modal_disjunctive (dne_or! $ demorgan₄'! hC) with (h | h);
  . exact unprovable_notbox h;
  . exact Consistent.not_bot (inferInstance) $ unnec! $ φ!_of_nnφ! h

theorem undecidable_independency_of_consistency : Undecidable Hilbert.GL (independency (∼□⊥)) := by
  constructor;
  . exact unprovable_independency;
  . exact unprovable_not_independency_of_consistency;

variable {n : ℕ}

lemma unprovable_higherIndependency_of_consistency : Hilbert.GL ⊬ higherIndependency (∼□⊥) n := by
  induction n with
  | zero => exact unprovable_notbox;
  | succ n ih => exact unprovable_independency;

lemma unprovable_not_higherIndependency_of_consistency : Hilbert.GL ⊬ ∼(higherIndependency (∼□⊥) n) := by
  by_contra hC;
  induction n with
  | zero =>
    exact Consistent.not_bot (inferInstance) $ unnec! $ φ!_of_nnφ! hC;
  | succ n ih =>
    rcases modal_disjunctive (dne_or! $ demorgan₄'! hC) with (h | h);
    . exact unprovable_higherIndependency_of_consistency h;
    . exact ih h;

theorem undecidable_higherIndependency_of_consistency : Undecidable Hilbert.GL (higherIndependency (∼□⊥) n) := by
  constructor;
  . exact unprovable_higherIndependency_of_consistency;
  . exact unprovable_not_higherIndependency_of_consistency;

end Hilbert.GL

end LO.Modal
