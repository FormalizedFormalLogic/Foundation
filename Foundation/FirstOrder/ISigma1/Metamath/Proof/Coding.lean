
import Foundation.FirstOrder.ISigma1.Metamath.Term.Coding
import Foundation.FirstOrder.ISigma1.Metamath.Proof.Typed
import Mathlib.Combinatorics.Colex

namespace LO.ISigma1.Metamath

open Encodable FirstOrder

lemma mem_iff_mem_bitIndices {x s : ℕ} : x ∈ s ↔ x ∈ s.bitIndices := by
  induction s using Nat.binaryRec generalizing x
  case z => simp
  case f b s ih =>
    cases b <;> simp
    · cases' x with x <;> simp [ih]
    · cases' x with x <;> simp [ih]

variable {L : Language} [L.Encodable] [L.LORDefinable]

lemma IsSemiterm.sound {n t : ℕ} (ht : IsSemiterm L n t) : ∃ T : FirstOrder.SyntacticSemiterm L n, ⌜T⌝ = t := by
  induction t using Nat.strongRec
  case ind t ih =>
    rcases ht.case with (⟨z, hz, rfl⟩ | ⟨x, rfl⟩ | ⟨k, f, v, hf, hv, rfl⟩)
    · exact ⟨#⟨z, hz⟩, by simp [Semiterm.quote_bvar]⟩
    · exact ⟨&x, by simp [Semiterm.quote_fvar]⟩
    · have : ∀ i : Fin k, ∃ t : FirstOrder.SyntacticSemiterm L n, ⌜t⌝ = v.[i] := fun i ↦
        ih v.[i] (nth_lt_qqFunc_of_lt (by simp [hv.lh])) (hv.nth i.prop)
      choose v' hv' using this
      have : ∃ F, encode F = f := isFunc_quote_quote (V := ℕ) (L := L) (x := f) (k := k) |>.mp (by simp [hf])
      rcases this with ⟨f, rfl⟩
      refine ⟨FirstOrder.Semiterm.func f v', ?_⟩
      suffices ⌜fun i ↦ ⌜v' i⌝⌝ = v by simpa [Semiterm.quote_func, quote_func_def]
      apply nth_ext' k (by simp) (by simp [hv.lh])
      intro i hi; simpa [hv'] using quote_nth_fin (fun i : Fin k ↦ v.[i]) ⟨i, hi⟩

lemma IsSemiformula.sound {n φ : ℕ} (h : IsSemiformula L n φ) : ∃ F : FirstOrder.SyntacticSemiformula L n, ⌜F⌝ = φ := by
  induction φ using Nat.strongRec generalizing n
  case ind φ ih =>
    rcases IsSemiformula.case_iff.mp h with
      (⟨k, r, v, hr, hv, rfl⟩ | ⟨k, r, v, hr, hv, rfl⟩ | rfl | rfl |
       ⟨φ, ψ, hp, hq, rfl⟩ | ⟨φ, ψ, hp, hq, rfl⟩ | ⟨φ, hp, rfl⟩ | ⟨φ, hp, rfl⟩)
    · have : ∀ i : Fin k, ∃ t : FirstOrder.SyntacticSemiterm L n, ⌜t⌝ = v.[i] := fun i ↦ (hv.nth i.prop).sound
      choose v' hv' using this
      have : ∃ R, encode R = r := isRel_quote_quote (V := ℕ) (L := L) (x := r) (k := k) |>.mp (by simp [hr])
      rcases this with ⟨R, rfl⟩
      refine ⟨Semiformula.rel R v', ?_⟩
      suffices ⌜fun i ↦ ⌜v' i⌝⌝ = v by simpa [Semiformula.quote_rel, quote_rel_def]
      apply nth_ext' k (by simp) (by simp [hv.lh])
      intro i hi; simpa [hv'] using quote_nth_fin (fun i : Fin k ↦ v.[i]) ⟨i, hi⟩
    · have : ∀ i : Fin k, ∃ t : FirstOrder.SyntacticSemiterm L n, ⌜t⌝ = v.[i] := fun i ↦ (hv.nth i.prop).sound
      choose v' hv' using this
      have : ∃ R, encode R = r := isRel_quote_quote (V := ℕ) (L := L) (x := r) (k := k) |>.mp (by simp [hr])
      rcases this with ⟨R, rfl⟩
      refine ⟨Semiformula.nrel R v', ?_⟩
      suffices ⌜fun i ↦ ⌜v' i⌝⌝ = v by simpa [Semiformula.quote_nrel, quote_rel_def]
      apply nth_ext' k (by simp) (by simp [hv.lh])
      intro i hi; simpa [hv'] using quote_nth_fin (fun i : Fin k ↦ v.[i]) ⟨i, hi⟩
    · exact ⟨⊤, by simp⟩
    · exact ⟨⊥, by simp⟩
    · rcases ih φ (by simp) hp with ⟨φ, rfl⟩
      rcases ih ψ (by simp) hq with ⟨ψ, rfl⟩
      exact ⟨φ ⋏ ψ, by simp⟩
    · rcases ih φ (by simp) hp with ⟨φ, rfl⟩
      rcases ih ψ (by simp) hq with ⟨ψ, rfl⟩
      exact ⟨φ ⋎ ψ, by simp⟩
    · rcases ih φ (by simp) hp with ⟨φ, rfl⟩
      exact ⟨∀' φ, by simp⟩
    · rcases ih φ (by simp) hp with ⟨φ, rfl⟩
      exact ⟨∃' φ, by simp⟩

end LO.ISigma1.Metamath
