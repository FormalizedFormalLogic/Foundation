module

public import Foundation.FirstOrder.SetTheory.Z
public import Foundation.FirstOrder.SetTheory.Universe

/-!
# Rayo's number

The lemmas below are elementary consequences of finite formula coding and the
von Neumann representation of natural numbers.
-/

@[expose] public section

namespace FFL.FirstOrder.SetTheory

noncomputable def definableNumbers (N : ℕ) : Set ℕ :=
  {m | ∃ φ : Semisentence ℒₛₑₜ 1, Encodable.encode φ < N ∧ DefinedFunction₀ (m : Universe.{0}) φ}

/-- Rayo's number at `N` is the least natural number strictly greater than every natural
number definable by a set-theoretic formula whose code is smaller than `N`. -/
noncomputable def rayo (N : ℕ) : ℕ := ⨆ n ∈ definableNumbers N, n + 1

noncomputable def rayoNumber : ℕ := rayo (10^100)

private lemma nat_mem_of_lt {m n : ℕ} (h : m < n) :
    (m : Universe.{0}) ∈ (n : Universe.{0}) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [num_succ_def, mem_succ_iff]
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | rfl
    . exact Or.inr (ih h)
    . exact Or.inl rfl

private lemma nat_injective : Function.Injective (fun n : ℕ ↦ (n : Universe.{0})) := by
  intro m n h
  change (m : Universe) = (n : Universe) at h
  rcases lt_trichotomy m n with h₁ | h₁ | h₁
  . exact False.elim <| mem_irrefl _ (h ▸ nat_mem_of_lt h₁)
  . exact h₁
  . exact False.elim <| mem_irrefl _ (h.symm ▸ nat_mem_of_lt h₁)

lemma definableNumbers_finite (N : ℕ) : (definableNumbers N).Finite := by
  have h₁ : {φ : Semisentence ℒₛₑₜ 1 | Encodable.encode φ < N}.Finite :=
    (Set.finite_lt_nat N).preimage Encodable.encode_injective.injOn
  have h₂ (φ : Semisentence ℒₛₑₜ 1) :
      {m : ℕ | DefinedFunction₀ (m : Universe.{0}) φ}.Subsingleton := by
    intro m hm n hn
    exact nat_injective <| (hn.iff fun _ ↦ (m : Universe)).mp <|
      (hm.iff fun _ ↦ (m : Universe)).mpr rfl
  apply Set.Finite.subset (h₁.biUnion fun φ _ ↦ (h₂ φ).finite)
  rintro m ⟨φ, hφ, hm⟩
  exact Set.mem_iUnion₂.mpr ⟨φ, hφ, hm⟩

private lemma nat_defined (n : ℕ) :
    ∃ φ : Semisentence ℒₛₑₜ 1, DefinedFunction₀ (n : Universe.{0}) φ := by
  induction n with
  | zero => exact ⟨isEmpty, ⟨fun v ↦ by
      simpa [isEmpty, IsEmpty, zero_def] using (isEmpty_iff_eq_empty (x := v 0))
    ⟩⟩
  | succ n ih =>
    obtain ⟨φ, hφ⟩ := ih
    exact ⟨“x. ∃ y, !φ y ∧ !succ.dfn x y”, ⟨fun v ↦ by simp [num_succ_def]⟩⟩

variable {N : ℕ}

lemma rayo_gt {φ : Semisentence ℒₛₑₜ 1} {m : ℕ}
    (h : Encodable.encode φ < N) (hm : DefinedFunction₀ (m : Universe.{0}) φ) : m < rayo N := by
  obtain ⟨b, hb⟩ := ((definableNumbers_finite N).image (fun n ↦ n + 1)).bddAbove
  apply Nat.lt_of_succ_le
  apply le_ciSup₂ (f := fun n (_ : n ∈ definableNumbers N) ↦ n + 1) _ m ⟨φ, h, hm⟩
  use b
  intro x hx
  obtain ⟨n, hn, rfl⟩ := Set.mem_iUnion.mp hx
  exact hb ⟨n, hn, rfl⟩

lemma rayo_monotone {N M : ℕ} (h : N ≤ M) : rayo N ≤ rayo M := by
  apply ciSup_le'
  intro n
  apply ciSup_le'
  rintro ⟨φ, hφ, hn⟩
  exact rayo_gt (hφ.trans_le h) hn

lemma rayo_unbounded (m : ℕ) : ∃ N, m < rayo N := by
  obtain ⟨φ, hφ⟩ := nat_defined m
  exact ⟨Encodable.encode φ + 1, rayo_gt (Nat.lt_succ_self _) hφ⟩

lemma rayo_le_iff : rayo N ≤ k ↔ ∀ m ∈ definableNumbers N, m < k := by
  constructor
  . rintro h m ⟨ψ, hψ, hm⟩
    exact (rayo_gt hψ hm).trans_le h
  . intro h
    exact ciSup_le' fun m ↦ ciSup_le' fun hm ↦ Nat.succ_le_of_lt (h m hm)

lemma rayo_not_mem_definableNumbers : rayo N ∉ definableNumbers N := by
  rintro ⟨ψ, hψ, hm⟩; exact (lt_irrefl _) (rayo_gt hψ hm)

end FFL.FirstOrder.SetTheory
