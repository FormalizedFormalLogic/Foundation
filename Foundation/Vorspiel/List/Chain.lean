import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Range


lemma Nat.zero_lt_of_not_zero {n : ℕ} (hn : n ≠ 0) : 0 < n := by omega;


namespace List

variable {α}
variable {l : List α} {x y : α}


section

variable [DecidableEq α]

def finIdxOf (l : List α) (hx : x ∈ l) : Fin l.length := ⟨l.idxOf x, idxOf_lt_length hx⟩

@[simp] lemma get_finIdxOf {hx : x ∈ l} : l.get (l.finIdxOf hx) = x := by simp [finIdxOf]

lemma neq_findIdxOf_of_neq {hx : x ∈ l} {hy : y ∈ l} (exy : x ≠ y) : l.finIdxOf hx ≠ l.finIdxOf hy := by
  simp only [finIdxOf, ne_eq, Fin.mk.injEq];
  apply List.idxOf_inj hx hy |>.not.mpr;
  exact exy;

end


section

lemma range.le_chain'_succ : List.Chain' (· < ·) (List.range (n + 1)) := by
  apply List.chain'_range_succ (· < ·) n |>.mpr;
  omega;

@[simp]
lemma range.le_chain' : List.Chain' (· < ·) (List.range n) := by
  match n with
  | 0 => simp [List.range_zero]
  | n + 1 => apply le_chain'_succ;

lemma finRange.le_chain'_succ : List.Chain' (· < ·) (List.finRange (n + 1)) := by
  rw [finRange_succ];
  induction n with
  | zero => simp [finRange]
  | succ n ih =>
    rw [List.finRange_succ, List.map]
    apply List.chain'_append_cons_cons (α := Fin (n + 2)) (l₁ := []) |>.mpr;
    refine ⟨?_, ?_, ?_⟩;
    . tauto;
    . tauto;
    . have := @List.chain'_map_of_chain'
        (α := Fin (n + 1)) (β := Fin (n + 2)) (R := (· < ·)) (S := (· < ·))
        (f := Fin.succ)
        (by simp)
        (l := 0 :: (map Fin.succ (finRange n)))
      apply this;
      exact ih;

@[simp]
lemma finRange.le_chain' : List.Chain' (· < ·) (List.finRange n) := by
  match n with
  | 0 => simp [List.finRange_zero]
  | n + 1 => apply finRange.le_chain'_succ;

end


namespace Chain'

variable {R} [IsTrans α R] {l : List α} {i j : Fin l.length}

lemma of_lt (h : List.Chain' R l) (hij : i < j) : R (l.get i) (l.get j) :=
  List.pairwise_iff_get.mp (List.chain'_iff_pairwise.mp h) _ _ hij

lemma connected_of_trans' (h : List.Chain' R l) (eij : i ≠ j) : R (l.get i) (l.get j) ∨ R (l.get j) (l.get i) := by
  rcases Nat.lt_trichotomy i j with (_ | _ | _);
  . left; exact of_lt h $ by omega;
  . omega;
  . right; exact of_lt h $ by omega;

lemma connected_of_trans [DecidableEq α] (h : List.Chain' R l) (hx : x ∈ l) (hy : y ∈ l) (exy : x ≠ y) : R x y ∨ R y x := by
  have : x = l.get (l.finIdxOf hx) := List.get_finIdxOf.symm;
  have : y = l.get (l.finIdxOf hy) := List.get_finIdxOf.symm;
  convert Chain'.connected_of_trans' (i := l.finIdxOf hx) (j := l.finIdxOf hy) h $ List.neq_findIdxOf_of_neq exy;

lemma noDup_of_irrefl_trans (h : List.Chain' R l) [IsIrrefl _ R] : l.Nodup := by
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

end Chain'

end List
