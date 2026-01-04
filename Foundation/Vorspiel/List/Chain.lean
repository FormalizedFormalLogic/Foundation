import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Range
import Foundation.Vorspiel.Fin.Supplemental

lemma Nat.zero_lt_of_not_zero {n : ℕ} (hn : n ≠ 0) : 0 < n := by omega;


namespace List

variable {α}
variable {l : List α} {x y : α}


section

variable [DecidableEq α]

def finIdxOf (l : List α) (hx : x ∈ l) : Fin l.length := ⟨l.idxOf x, idxOf_lt_length_of_mem hx⟩

@[simp] lemma get_finIdxOf {hx : x ∈ l} : l.get (l.finIdxOf hx) = x := by simp [finIdxOf]

lemma neq_findIdxOf_of_neq {hx : x ∈ l} {hy : y ∈ l} (exy : x ≠ y) : l.finIdxOf hx ≠ l.finIdxOf hy := by
  simp only [finIdxOf, ne_eq, Fin.mk.injEq];
  apply List.idxOf_inj _ |>.not.mpr <;> grind;

end


section

lemma range.le_isChain_succ : List.IsChain (· < ·) (List.range (n + 1)) := by
  apply List.isChain_range_succ (· < ·) n |>.mpr;
  omega;

@[simp]
lemma range.le_isChain : List.IsChain (· < ·) (List.range n) := by
  match n with
  | 0 => simp;
  | n + 1 => apply le_isChain_succ;

lemma finRange.le_isChain_succ : List.IsChain (· < ·) (List.finRange (n + 1)) := by
  rw [finRange_succ];
  induction n with
  | zero => simp [finRange]
  | succ n ih =>
    rw [List.finRange_succ, List.map]
    apply List.isChain_append_cons_cons (α := Fin (n + 2)) (l₁ := []) |>.mpr;
    refine ⟨?_, ?_, ?_⟩;
    . tauto;
    . tauto;
    . have := @List.isChain_map_of_isChain
        (α := Fin (n + 1)) (β := Fin (n + 2)) (R := (· < ·)) (S := (· < ·))
        (f := Fin.succ)
        (by simp)
        (l := 0 :: (map Fin.succ (finRange n)))
      apply this;
      exact ih;

@[simp]
lemma finRange.le_isChain : List.IsChain (· < ·) (List.finRange n) := by
  match n with
  | 0 => simp [List.finRange_zero]
  | n + 1 => apply finRange.le_isChain_succ;

end


namespace IsChain

variable {R} [IsTrans α R] {l : List α} {i j : Fin l.length}

lemma of_lt (h : List.IsChain R l) (hij : i < j) : R (l.get i) (l.get j) :=
  List.pairwise_iff_get.mp (List.isChain_iff_pairwise.mp h) _ _ hij

lemma connected_of_trans' (h : List.IsChain R l) (eij : i ≠ j) : R (l.get i) (l.get j) ∨ R (l.get j) (l.get i) := by
  rcases Nat.lt_trichotomy i j with (_ | _ | _);
  . left; exact of_lt h $ by omega;
  . omega;
  . right; exact of_lt h $ by omega;

lemma connected_of_trans [DecidableEq α] (h : List.IsChain R l) (hx : x ∈ l) (hy : y ∈ l) (exy : x ≠ y) : R x y ∨ R y x := by
  have : x = l.get (l.finIdxOf hx) := List.get_finIdxOf.symm;
  have : y = l.get (l.finIdxOf hy) := List.get_finIdxOf.symm;
  convert IsChain.connected_of_trans' (i := l.finIdxOf hx) (j := l.finIdxOf hy) h $ List.neq_findIdxOf_of_neq exy;

lemma noDup_of_irrefl_trans (h : List.IsChain R l) [IsIrrefl _ R] : l.Nodup := by
  apply List.nodup_iff_getElem?_ne_getElem?.mpr;
  intro i j hij hj;
  let i' : Fin l.length := ⟨i, by omega⟩;
  let j' : Fin l.length := ⟨j, by omega⟩;
  by_contra hC;
  replace hC : l.get i' = l.get j' := by simpa [
    (show l[i]? = l.get i' by exact List.getElem?_eq_getElem (by omega)),
    (show l[j]? = l.get j' by exact List.getElem?_eq_getElem (by omega))
  ] using hC;
  have : R (l.get i') (l.get j') := of_lt h (by simpa);
  rw [hC] at this;
  exact IsIrrefl.irrefl _ this;

end IsChain


lemma mem_head?_eq_head : a ∈ l.head? → ∃ h, a = l.head h := by
  match l with
  | [] => simp;
  | y::ys =>
    simp [head?_cons, head_cons];
    tauto;

lemma concat_head?_eq_head (lh : l ≠ []) : (l.concat a).head? = some (l.head lh) := by
  match l with
  | [] => contradiction;
  | _::_ => simp;

lemma isChain_concat :  List.IsChain R (l.concat a) ↔ List.IsChain R l ∧ ∀ x ∈ l.getLast?, R x a := by
  rw [List.concat_eq_append]
  constructor;
  . intro h;
    simpa using List.isChain_append.mp h;
  . rintro ⟨h₁, h₂⟩;
    apply List.isChain_append.mpr;
    refine ⟨h₁, ?_, ?_⟩;
    . simp;
    . intro x hx;
      have : R x a := h₂ x hx;
      simpa;

lemma isChain_concat_of_not_nil (hl : l ≠ []) : List.IsChain R (l.concat a) ↔ List.IsChain R l ∧ R (l.getLast hl) a := by
  apply Iff.trans List.isChain_concat;
  suffices (∀ x ∈ l.getLast?, R x a) ↔ R (l.getLast hl) a by tauto;
  constructor;
  . intro h;
    apply h (l.getLast hl);
    apply List.getLast_mem_getLast?;
  . rintro h x hx;
    convert h;
    simp_all [Option.some.injEq, List.getLast?_eq_some_getLast hl];

section

variable [DecidableEq α]

lemma rel_head_of_isChain_trans [IsTrans _ R] (h : List.IsChain R l) (lh : l ≠ []) : ∀ x ∈ l, x ≠ l.head lh → R (l.head lh) x := by
  intro x hx₁ hx₂;
  let i : Fin l.length := ⟨0, List.length_pos_of_ne_nil lh⟩;
  let j : Fin l.length := List.finIdxOf _ hx₁;
  convert List.IsChain.of_lt h (i := i) (j := j) ?_;
  . apply List.head_eq_getElem_zero;
  . apply List.get_finIdxOf.symm;
  . apply lt_of_le_of_ne;
    . apply Nat.zero_le;
    . by_contra hC;
      apply hx₂;
      dsimp [i, j] at hC;
      convert List.head_eq_getElem_zero lh |>.symm;
      have := List.get_finIdxOf (hx := hx₁) |>.symm;
      rwa [←hC] at this;

lemma rel_head_of_isChain_preorder [IsPreorder _ R] (h : List.IsChain R l) (lh : l ≠ []) : ∀ x ∈ l, R (l.head lh) x := by
  intro x hx;
  by_cases e : x = l.head lh;
  . subst e;
    apply refl;
  . apply rel_head_of_isChain_trans h lh <;> assumption;

lemma rel_getLast_of_isChain_trans [IsTrans _ R] (h : List.IsChain R l) (lh : l ≠ []) : ∀ x ∈ l, x ≠ l.getLast lh → R x (l.getLast lh) := by
  intro x hx₁ hx₂;
  have : NeZero l.length := ⟨List.length_eq_zero_iff.not.mpr lh⟩;
  let i : Fin l.length := List.finIdxOf l hx₁;
  let j : Fin l.length := Fin.last';
  convert List.IsChain.of_lt h (i := i) (j := j) ?_;
  . apply List.get_finIdxOf.symm;
  . apply List.getLast_eq_getElem;
  . apply lt_of_le_of_ne;
    . exact Fin.lt_last';
    . by_contra hC;
      apply hx₂;
      dsimp [i, j] at hC;
      convert List.getLast_eq_getElem lh |>.symm;
      have := List.get_finIdxOf (hx := hx₁) |>.symm;
      rwa [hC] at this;

lemma rel_getLast_of_isChain_preorder [IsPreorder _ R] (h : List.IsChain R l) (lh : l ≠ []) : ∀ x ∈ l, R x (l.getLast lh) := by
  intro x hx;
  by_cases e : x = l.getLast lh;
  . subst e;
    apply refl;
  . apply rel_getLast_of_isChain_trans h lh <;> assumption;

end

def embedding_of_exists_noDup {l : List α} (hl₁ : l.Nodup) (hl₂ : l.length = n) : Fin n ↪ α := by
  refine ⟨λ ⟨i, hi⟩ => l.get ⟨i, by omega⟩, ?_⟩;
  . rintro ⟨i, hi⟩ ⟨j, hj⟩ hij;
    simpa using (List.nodup_iff_injective_get (l := l) |>.mp hl₁) hij;

end List
