module

public import Mathlib.Data.Nat.Bits
public import Mathlib.Data.Nat.Lattice
public import Mathlib.Data.Nat.Pairing
public import Mathlib.Tactic.Cases

@[expose]
public section

namespace Nat
variable {α : ℕ → Sort u}

def cases (hzero : α 0) (hsucc : ∀ n, α (n + 1)) : ∀ n, α n
  | 0     => hzero
  | n + 1 => hsucc n

infixr:70 " :>ₙ " => cases

@[simp] lemma cases_zero (hzero : α 0) (hsucc : ∀ n, α (n + 1)) :
    (hzero :>ₙ hsucc) 0 = hzero := rfl

@[simp] lemma cases_succ (hzero : α 0) (hsucc : ∀ n, α (n + 1)) (n : ℕ) :
    (hzero :>ₙ hsucc) (n + 1) = hsucc n := rfl

@[simp] lemma ne_step_max (n m : ℕ) : n ≠ max n m + 1 :=
  ne_of_lt $ Nat.lt_succ_of_le $ by simp

@[simp] lemma ne_step_max' (n m : ℕ) : n ≠ max m n + 1 :=
  ne_of_lt $ Nat.lt_succ_of_le $ by simp

lemma rec_eq {α : Sort*} (a : α) (f₁ f₂ : ℕ → α → α) (n : ℕ) (H : ∀ m < n, ∀ a, f₁ m a = f₂ m a) :
    (n.rec a f₁ : α) = n.rec a f₂ := by
  induction' n with n ih <;> simp
  · have : (n.rec a f₁ : α) = n.rec a f₂ := ih (fun m hm a =>  H m (Nat.lt.step hm) a)
    simpa [this] using H n (Nat.lt.base n) (n.rec a f₂)

lemma least_number (P : ℕ → Prop) (hP : ∃ x, P x) : ∃ x, P x ∧ ∀ z < x, ¬P z := by
  rcases hP with ⟨n, hn⟩
  induction' n using Nat.strongRec with n ih
  by_cases H : ∃ m < n, P m
  · rcases H with ⟨m, hm, hPm⟩
    exact ih m hm hPm
  · exact ⟨n, hn, by simpa using H⟩

def toFin (n : ℕ) : ℕ → Option (Fin n) := fun x => if hx : x < n then some ⟨x, hx⟩ else none


@[grind =>]
lemma zero_lt_of_not_zero {n : ℕ} (hn : n ≠ 0) : 0 < n := by omega;


lemma one_le_of_bodd {n : ℕ} (h : n.bodd = true) : 1 ≤ n :=
  by induction n <;> simp at h ⊢

lemma pair_le_pair_of_le {a₁ a₂ b₁ b₂ : ℕ} (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) : a₁.pair b₁ ≤ a₂.pair b₂ := by
  rcases lt_or_eq_of_le ha with (ha | rfl) <;> rcases lt_or_eq_of_le hb with (hb | rfl)
  · exact le_of_lt (lt_trans (Nat.pair_lt_pair_left b₁ ha) (Nat.pair_lt_pair_right a₂ hb))
  · exact le_of_lt (Nat.pair_lt_pair_left b₁ ha)
  · exact le_of_lt (Nat.pair_lt_pair_right a₁ hb)
  · rfl

end Nat
