module
import Foundation.Propositional.Kripke2.Basic
import Foundation.Propositional.Kripke2.FTheory
import Mathlib.Tactic.TFAE


namespace LO.Propositional

open Formula (atom)
open Kripke2
open Formula.Kripke2

namespace Kripke2

variable {F : Kripke2.Frame} {φ ψ χ : Formula ℕ}

namespace Frame

protected abbrev IsTransitive (F : Kripke2.Frame) := _root_.IsTrans _ F.Rel
@[simp, grind →] lemma trans [F.IsTransitive] : ∀ {x y z : F}, x ≺ y → y ≺ z → x ≺ z := by apply IsTrans.trans

end Frame


@[simp high, grind .]
lemma valid_axiomTra₁_of_IsTransitive [F.IsTransitive] : F ⊧ Axioms.Tra1 φ ψ χ := by
  intro V x y Rxy h₁ z Ryz h₂ v Rzv h₃;
  apply h₁;
  . apply F.trans Ryz Rzv;
  . assumption;

lemma IsTransitive_of_valid_axiomTra₁ (h : F ⊧ Axioms.Tra1 #0 #1 #2) : F.IsTransitive := by
  constructor;
  intro x y z Rxy Ryz;
  apply @h (λ w a => match a with | 0 => y ≺ w | 1 => x ≺ w | 2 => x ≺ w | _ => False) F.root x F.rooted ?_ y Rxy ?_ z Ryz ?_;
  all_goals tauto;

@[simp high, grind .]
lemma valid_axiomTra₂_of_IsTransitive [F.IsTransitive] : F ⊧ Axioms.Tra2 φ ψ χ := by
  intro V x y Rxy h₁ z Ryz h₂ v Rzv h₃;
  apply h₂;
  . assumption;
  . apply h₁;
    . apply F.trans Ryz Rzv;
    . assumption;

lemma IsTransitive_of_valid_axiomTra₂ (h : F ⊧ Axioms.Tra2 #0 #1 #2) : F.IsTransitive := by
  constructor;
  intro x y z Rxy Ryz;
  apply @h (λ w a => match a with | 0 => w = z | 1 => x ≺ w | 2 => x ≺ w | _ => False) F.root x F.rooted ?_ y Rxy ?_ z Ryz ?_;
  all_goals tauto;

lemma TFAE_IsTransitive : [
  F.IsTransitive,
  F ⊧ Axioms.Tra1 #0 #1 #2,
  F ⊧ Axioms.Tra2 #0 #1 #2,
].TFAE := by
  tfae_have 1 → 2 := by apply valid_axiomTra₁_of_IsTransitive;
  tfae_have 1 → 3 := by apply valid_axiomTra₂_of_IsTransitive;
  tfae_have 2 → 1 := IsTransitive_of_valid_axiomTra₁
  tfae_have 3 → 1 := IsTransitive_of_valid_axiomTra₂
  tfae_finish;

instance [Entailment.F L] [Entailment.HasAxiomTra1 L] [Entailment.Disjunctive L] : Frame.IsTransitive (canonicalModel L).toFrame where
  trans := by
    rintro T U V RTU RUV φ ψ hφψ hφ;
    apply RUV (RTU ?_ (show ⊤ ∈ U.theory by simp)) hφ;
    apply T.imp_closed (φ := φ ➝ ψ);
    . exact Entailment.Corsi.axiomTra1;
    . simpa;

end Kripke2

end LO.Propositional
