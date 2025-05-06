import Foundation.Propositional.Kripke.Completeness
import Foundation.Vorspiel.List.Chain
import Mathlib.Data.PNat.Basic
import Foundation.Propositional.BoundDepth

lemma List.ne_get_con_get_con_of_ne {l : List α}
  (h : ∀ i j : Fin l.length, i ≠ j → (l.get i) ≠ (l.get j))
  (hx : x ∉ l)
  : ∀ i j, i ≠ j → (x :: l).get i ≠ (x :: l).get j := by
  rintro ⟨i, hi⟩ ⟨j, hj⟩ hij;
  match i, j with
  | 0, 0 => contradiction;
  | 0, j + 1 =>
    revert hx;
    contrapose!;
    intro h;
    apply List.mem_of_getElem;
    exact h.symm;
  | i + 1, 0 =>
    revert hx;
    contrapose!;
    intro h;
    apply List.mem_of_getElem;
    exact h;
  | i + 1,j + 1 =>
    apply h;
    simpa using hij;


namespace LO.Propositional

namespace Kripke

open Kripke
open Formula.Kripke

section definability

variable {F : Kripke.Frame}

open Formula (atom)
open Classical

/-- Frame has at most `n`-chain. -/
def Frame.IsDepthLt (F : Frame) (n : ℕ) := ∀ l : List F.World, l.length = n + 1 ∧ l.Chain' F → ∃ i j : Fin l.length, i ≠ j ∧ l.get i = l.get j

lemma not_isDepthLt'_of_not_validate_BoundDepth' {M : Model} {x : M.World} {n : ℕ} (h : ¬x ⊧ Axioms.BoundDepth' n)
  : ∃ l : List M.World, l.length = n + 2 ∧ l.Chain' (· ≺ ·) ∧ (l.head? = some x) ∧ ∀ i j : Fin l.length, i ≠ j → l.get i ≠ l.get j := by
  induction n generalizing x with
  | zero =>
    have ⟨h₁, h₂⟩ := Satisfies.not_or_def.mp h;
    replace ⟨y, Rxy, h₂⟩ := Satisfies.not_neg_def.mp h₂;
    use [x, y];
    refine ⟨?_, ?_, ?_, ?_⟩;
    . simp;
    . simpa;
    . simp;
    . simp only [List.length_cons, List.length_nil, Nat.reduceAdd, ne_eq, List.get_eq_getElem];
      intro i j hij;
      by_contra hC;
      match i, j with
      | 0, 0 => contradiction;
      | 1, 1 => contradiction;
      | 0, 1 =>
        simp only [Fin.isValue, Fin.val_zero, List.getElem_cons_zero, Fin.val_one, List.getElem_cons_succ] at hC;
        subst hC;
        contradiction;
      | 1, 0 =>
        simp only [Fin.isValue, Fin.val_zero, List.getElem_cons_zero, Fin.val_one, List.getElem_cons_succ] at hC;
        subst hC;
        contradiction;
  | succ n ih =>
    have ⟨h₁, h₂⟩ := Satisfies.not_or_def.mp h;
    replace ⟨y, Rxy, h₂, h₃⟩ := Satisfies.not_imp_def.mp h₂;
    obtain ⟨l, hl₁, hl₂, hl₃, hl₄⟩ := @ih y h₃;
    use (x :: l);
    refine ⟨?_, ?_, ?_, ?_⟩;
    . simpa;
    . apply List.Chain'.cons';
      . exact hl₂;
      . simpa [hl₃];
    . simp;
    . apply List.ne_get_con_get_con_of_ne;
      . exact hl₄;
      . by_contra hC;
        have : l ≠ [] :=  List.length_pos_iff_ne_nil.mp (by omega);
        have Rhx : (l.head _) ≺ x := List.rel_head_of_chain'_preorder hl₂ (by assumption) x hC;
        have ehy : (l.head _) = y := List.head_eq_iff_head?_eq_some (by assumption) |>.mpr hl₃;
        subst ehy;
        have exy := _root_.antisymm Rxy Rhx;
        subst exy;
        contradiction;

lemma not_isDepthLt_of_not_validate_BoundDepth' {n : ℕ} (h : ¬F ⊧ Axioms.BoundDepth' n)
  : ¬F.IsDepthLt (n + 1) := by
  obtain ⟨M, x, rfl, h₂⟩ := ValidOnFrame.exists_model_world_of_not h;
  obtain ⟨l, hl⟩ := not_isDepthLt'_of_not_validate_BoundDepth' h₂;
  dsimp [Frame.IsDepthLt];
  push_neg;
  use l;
  tauto;

lemma validate_BoundDepth'_of_isDepthLt {n : ℕ} : F.IsDepthLt (n + 1) → F ⊧ Axioms.BoundDepth' n := by
  contrapose!;
  intro h;
  exact not_isDepthLt_of_not_validate_BoundDepth' h;

lemma validate_BoundDepth_of_isDepthLt {n : ℕ+} : F.IsDepthLt n → F ⊧ Axioms.BoundDepth n := by
  simpa using validate_BoundDepth'_of_isDepthLt (n := n.natPred);

lemma isDepthLt_of_validate_BoundDepth {n : ℕ+} : F ⊧ Axioms.BoundDepth n → F.IsDepthLt n := by sorry;

end definability



section canonical

variable {S} [Entailment (Formula ℕ) S]
variable {𝓢 : S} [Entailment.Consistent 𝓢] [Entailment.Int 𝓢]

open Formula.Kripke
open Entailment
     Entailment.FiniteContext
open canonicalModel
open SaturatedConsistentTableau
open Classical

namespace Canonical

open Formula

lemma isDepthLt' (h : 𝓢 ⊢! (Axioms.BoundDepth' n)) :
  ∀ l : List (canonicalFrame 𝓢).World, l.length = n + 2 ∧ (l.head? = some (canonicalFrame 𝓢).default) ∧ l.Chain' (· ≺ ·) → ∃ i j : Fin l.length, i ≠ j ∧ l.get i = l.get j := by
  rintro l ⟨hl₁, hl₂, hl₃⟩;
  induction n with
  | zero =>
    simp at hl₁;
    let i₀ : Fin l.length := ⟨0, by omega⟩;
    let i₁ : Fin l.length := ⟨1, by omega⟩;
    use i₀, i₁;
    constructor;
    . simp [i₀, i₁];
    . generalize l.get i₀ = x₀;
      generalize l.get i₁ = x₁;
      sorry;
      /-
      have Rx₀₁ : x₀ ≺ x₁ := by
        sorry;
      by_contra hC;
      have := (iff_valid_on_canonicalModel_deducible.mpr h) x₀;
      simp [Axioms.BoundDepth', Axioms.BoundDepth] at this;
      rcases this with (h | h);
      . simp [Semantics.Realize, Satisfies, canonicalModel] at h;
        simp [Semantics.Realize] at h;
      . have := Satisfies.neg_def.mp h Rx₀₁

        sorry;
      -/
  | succ n ih =>
    sorry;

end Canonical

end canonical



end Kripke

end LO.Propositional
