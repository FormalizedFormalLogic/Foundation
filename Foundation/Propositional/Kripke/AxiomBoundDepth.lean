import Foundation.Propositional.Kripke.Completeness
import Foundation.Vorspiel.List.Chain
import Mathlib.Data.PNat.Basic
import Foundation.Propositional.BoundDepth

namespace LO.Propositional

namespace Kripke

open Kripke
open Formula.Kripke

section definability

variable {F : Kripke.Frame}

open Formula (atom)
open Classical

/-- Frame has at most `n`-chain. -/
def Frame.IsDepthLt (F : Frame) (n : ℕ) := ∀ l : List F.World, l.length = n + 1 ∧ l.Chain' F → ¬l.Nodup

private lemma not_isDepthLt'_of_not_validate_BoundDepth' {M : Model} {x : M.World} {n : ℕ} (h : ¬x ⊧ Axioms.BoundDepth' n)
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

private lemma not_isDepthLt_of_not_validate_BoundDepth' {n : ℕ} (h : ¬F ⊧ Axioms.BoundDepth' n)
  : ¬F.IsDepthLt (n + 1) := by
  obtain ⟨M, x, rfl, h₂⟩ := ValidOnFrame.exists_model_world_of_not h;
  obtain ⟨l, hl₁, hl₂, _, hl₃⟩ := not_isDepthLt'_of_not_validate_BoundDepth' h₂;
  dsimp [Frame.IsDepthLt];
  push_neg;
  use l;
  refine ⟨⟨?_, ?_⟩, ?_⟩;
  . simpa using hl₁;
  . assumption;
  . apply List.nodup_iff_get_ne_get.mpr hl₃;

private lemma validate_BoundDepth'_of_isDepthLt {n : ℕ} : F.IsDepthLt (n + 1) → F ⊧ Axioms.BoundDepth' n := by
  contrapose!;
  intro h;
  exact not_isDepthLt_of_not_validate_BoundDepth' h;

lemma validate_BoundDepth_of_isDepthLt {n : ℕ+} : F.IsDepthLt n → F ⊧ Axioms.BoundDepth n := by
  simpa using validate_BoundDepth'_of_isDepthLt (n := n.natPred);


abbrev cascadeVal (l : List F.World) (n) (hl : l.length = n + 1 := by omega) : Valuation F := ⟨
  λ w a =>
    letI i : Fin l.length := ⟨(l.length - 1) - a, by omega⟩;
    letI x : F.World := l[i]
    x ≺ w
  ,
  by
    simp only [Fin.getElem_fin];
    intro x y Rxy a Rlx;
    exact _root_.trans Rlx Rxy;
⟩

/-
lemma cascadeVal_sat {l : List F.World} {hl : 0 < l.length} (a : Fin l.length) :
  letI i : Fin l.length := ⟨l.length - (a + 1), by omega⟩;
  Satisfies ⟨F, cascadeVal l hl⟩ (l[i]) (.atom a) := by
  apply _root_.refl;

lemma wowwow
  (hl₁ : 1 < l.length) (hl₂ : l.Chain' (· ≺ ·)) :
  letI x : F.World := l.tail.head (List.ne_nil_of_length_pos (by simpa));
  Satisfies ⟨F, cascadeVal l (by omega)⟩ x (Axioms.BoundDepth' n) →
  Satisfies ⟨F, cascadeVal l.tail (by simpa)⟩ x (Axioms.BoundDepth' n) := by
  induction n with
  | zero =>
    simp [Axioms.BoundDepth', Satisfies];
    have e : l[l.length - 1 - 1 + 1] = l[l.length - 1] := by

      sorry;
    rintro (h | h);
    . left;
      rw [e];
      apply _root_.trans ?_ h;
      apply _root_.refl;
    . right;
      intro x Rhx;
      have := h Rhx;
      revert this;
      contrapose!;
      rw [e];
      tauto;
  | succ n ih =>
    simp_all [Satisfies]
    rintro (h | h);
    . left;
      sorry;
    . right;
      intro x Rhx h₂;
      apply Satisfies.formula_hereditary Rhx $ ih ?_
      apply h;
      . apply _root_.refl;
      . sorry;
-/

lemma isDepthLt_of_validate_BoundDepth'_aux {n : ℕ}
  {l : List F.World}
  (hl₁ : l.length = n + 2) (hl₂ : l.Chain' (· ≺ ·)) :
  letI M : Model := ⟨F, (cascadeVal l (n + 1))⟩;
  letI x₀ : M.World := l.head (List.ne_nil_of_length_pos (by omega));
  Satisfies M x₀ (Axioms.BoundDepth' n) → ¬l.Nodup := by
  intro h;
  induction n generalizing l with
  | zero =>
    apply List.nodup_iff_get_ne_get.not.mpr;
    push_neg;
    let i₀ : Fin l.length := ⟨0, by omega⟩;
    let i₁ : Fin l.length := ⟨1, by omega⟩;
    use i₀, i₁;
    constructor;
    . simp [i₀, i₁];
    . replace h := Satisfies.or_def.mp h;
      rcases h with h | h;
      . replace h : l[1] ≺ l[0] := by
          simpa [Semantics.Realize, Satisfies, hl₁, List.head_eq_getElem_zero] using h;
        apply _root_.antisymm ?_ h;
        apply List.Chain'.of_lt hl₂;
        simp;
      . exfalso;
        apply Satisfies.neg_def.mp h (w' := l[i₁]) $ by
          apply List.rel_head_of_chain'_preorder hl₂;
          simp;
        simp [Semantics.Realize, Satisfies, i₁, hl₁];
  | succ n ih =>
    replace h := Satisfies.or_def.mp h;
    rcases h with h | h;
    . apply List.nodup_iff_get_ne_get.not.mpr;
      push_neg;
      use ⟨0, by omega⟩, ⟨1, by omega⟩;
      constructor
      . simp;
      . simp only [Fin.getElem_fin];
        apply _root_.antisymm (r := F.Rel');
        . apply List.Chain'.of_lt hl₂;
          simp;
        . simpa [Semantics.Realize, Satisfies, hl₁, List.head_eq_getElem_zero] using h;
    . suffices ¬l.tail.Nodup by exact List.not_noDup_of_not_tail_noDup this;
      apply ih (l := l.tail);
      . exact List.Chain'.tail hl₂;
      . have := h (w' := l.tail.head ?_) ?_ ?_;
        . sorry;
        . apply List.ne_nil_of_length_pos
          simp [hl₁];
        . suffices l[0] ≺ l[1] by simpa [List.head_eq_getElem_zero];
          apply List.Chain'.of_lt hl₂;
          simp;
        . simp [Satisfies, hl₁]
      . simpa;

lemma isDepthLt_of_validate_BoundDepth' {n : ℕ} (h : F ⊧ Axioms.BoundDepth' n) : F.IsDepthLt (n + 1) := by
  rintro l ⟨l₁, l₂⟩;
  apply isDepthLt_of_validate_BoundDepth'_aux (n := n) l₁ l₂;
  apply h;

lemma isDepthLt_of_validate_BoundDepth {n : ℕ+} : F ⊧ Axioms.BoundDepth n → F.IsDepthLt n := by
  convert isDepthLt_of_validate_BoundDepth' (n := n.natPred);
  simp;

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
    . generalize ex₀ : l.get i₀ = x₀;
      generalize ex₁ : l.get i₁ = x₁;
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
