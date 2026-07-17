module

public import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Traces of finite permutations
-/

@[expose] public section

namespace Equiv.Perm

variable {α β : Type*} [DecidableEq α] [DecidableEq β] [Fintype α] [Fintype β]

/-- The least positive time at which the orbit of `inl a` returns to the visible interface `α`. -/
def returnTime
    (f : Perm (α ⊕ β)) (a : α) : ℕ :=
  Nat.find (p := fun n ↦ 0 < n ∧ ∃ b, (f ^ n) (.inl a) = .inl b) <| by
    refine ⟨orderOf f, orderOf_pos f, a, ?_⟩
    simp

/-- Follow `f` from `inl a`, feeding every `β` output back as input, until the first `α` output. -/
def traceFun
    (f : Perm (α ⊕ β)) (a : α) : α :=
  ((f ^ returnTime f a) (.inl a)).getLeft?.getD a

lemma traceFun_spec
    (f : Perm (α ⊕ β)) (a : α) :
    (f ^ returnTime f a) (.inl a) = .inl (traceFun f a) := by
  have hex : ∃ n, 0 < n ∧ ∃ b, (f ^ n) (.inl a) = .inl b := by
    refine ⟨orderOf f, orderOf_pos f, a, ?_⟩
    simp
  have hreturn :
      0 < returnTime f a ∧ ∃ b, (f ^ returnTime f a) (.inl a) = .inl b := by
    unfold returnTime
    exact Nat.find_spec hex
  obtain ⟨b, hb⟩ := hreturn.2
  simp [traceFun, hb]

/-- The number of cycles of `f` contained entirely in the feedback type `β`.

Fixed points in `β` are counted as cycles of length one. -/
def closedCycles
    (f : Perm (α ⊕ β)) : ℕ :=
  let p : α ⊕ β → Prop := fun x ↦ ∀ a, ¬f.SameCycle x (.inl a)
  let h : ∀ x, p (f x) ↔ p x := by simp [p]
  (f.subtypePerm h).partition.parts.card

/-- The trace of a finite permutation, ignoring cycles contained entirely in the feedback type. -/
def trace
    (f : Perm (α ⊕ β)) : Perm α := by
  have traceFun_inv_apply (g : Perm (α ⊕ β)) (a : α) :
      traceFun g⁻¹ (traceFun g a) = a := by
    let n := returnTime g a
    let b := traceFun g a
    let m := returnTime g⁻¹ b
    let c := traceFun g⁻¹ b
    have hex (g : Perm (α ⊕ β)) (x : α) :
        ∃ k, 0 < k ∧ ∃ y, (g ^ k) (.inl x) = .inl y := by
      refine ⟨orderOf g, orderOf_pos g, x, ?_⟩
      simp
    have hreturn (g : Perm (α ⊕ β)) (x : α) :
        0 < returnTime g x ∧ ∃ y, (g ^ returnTime g x) (.inl x) = .inl y := by
      unfold returnTime
      exact Nat.find_spec (hex g x)
    have hminimal (g : Perm (α ⊕ β)) (x : α) {k : ℕ}
        (hk : k < returnTime g x) :
        ¬(0 < k ∧ ∃ y, (g ^ k) (.inl x) = .inl y) := by
      unfold returnTime at hk
      exact Nat.find_min (hex g x) hk
    have hn : 0 < n := (hreturn g a).1
    have hgn : (g ^ n) (.inl a) = .inl b := traceFun_spec g a
    have hbm : (g⁻¹ ^ m) (.inl b) = .inl c := traceFun_spec g⁻¹ b
    have hback : (g⁻¹ ^ n) (.inl b) = .inl a := by
      rw [← hgn]
      calc
        (g⁻¹ ^ n) ((g ^ n) (.inl a)) = (g ^ n)⁻¹ ((g ^ n) (.inl a)) := by rw [inv_pow]
        _ = .inl a := by rw [inv_def]; exact (g ^ n).symm_apply_apply (.inl a)
    have hmn : m ≤ n := by
      unfold m returnTime
      exact Nat.find_min' (hex g⁻¹ b) ⟨hn, a, hback⟩
    have hmn' : m = n := by
      apply le_antisymm hmn
      by_contra h
      have hmnlt : m < n := by omega
      have hpow : g⁻¹ ^ m * g ^ n = g ^ (n - m) := by
        rw [pow_sub g hmn, inv_pow]
        exact (Commute.pow_pow_self g m n).inv_left.eq
      have hearly : (g ^ (n - m)) (.inl a) = .inl c := by
        rw [← hpow, mul_apply, hgn, hbm]
      exact hminimal g a (Nat.sub_lt hn (hreturn g⁻¹ b).1)
        ⟨Nat.sub_pos_of_lt hmnlt, c, hearly⟩
    rw [hmn'] at hbm
    exact Sum.inl_injective (hbm.symm.trans hback)
  exact {
    toFun := traceFun f
    invFun := traceFun f⁻¹
    left_inv := traceFun_inv_apply f
    right_inv := fun a ↦ by simpa using traceFun_inv_apply f⁻¹ a }

@[simp] lemma trace_inv
    (f : Perm (α ⊕ β)) : trace f⁻¹ = (trace f)⁻¹ := rfl

def partition_card_eq_partition_card_add_closedCycles (f : Perm (α ⊕ β)) :
    f.partition.parts.card = f.trace.partition.parts.card + f.closedCycles := by
  sorry

end Equiv.Perm
