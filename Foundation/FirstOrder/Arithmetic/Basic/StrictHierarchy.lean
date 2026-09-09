module

public import Foundation.FirstOrder.Arithmetic.Prenex

/-!
# Strict arithmetical hierarchy and prenex normal form

`StrictHierarchy Γ s φ` singles out the prenex `Γ`-formulas of level `s` with a `Δ₀` matrix
beneath alternating quantifier blocks, and relates them to the ordinary cumulative hierarchy and
to `Prenex Γ s ξ n` codes.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

variable {L : Language} [L.LT] {ξ : Type*}

/-- `StrictHierarchy Γ s φ` says that `φ` is a prenex `Γ`-formula of level `s`, with a `Δ₀`
matrix beneath alternating quantifier blocks.

- [HP98, 0.30, Lemma I.1.69] -/
inductive StrictHierarchy : Polarity → ℕ → {n : ℕ} → Semiformula L ξ n → Prop
  | zero {Γ n} {φ : Semiformula L ξ n} : Hierarchy 𝚺 0 φ → StrictHierarchy Γ 0 φ
  | ofAlt {Γ s n} {φ : Semiformula L ξ n} :
      StrictHierarchy Γ.alt s φ → StrictHierarchy Γ (s + 1) φ
  | exs {s n} {φ : Semiformula L ξ (n + 1)} :
      StrictHierarchy 𝚺 (s + 1) φ → StrictHierarchy 𝚺 (s + 1) (∃¹ φ)
  | all {s n} {φ : Semiformula L ξ (n + 1)} :
      StrictHierarchy 𝚷 (s + 1) φ → StrictHierarchy 𝚷 (s + 1) (∀¹ φ)

namespace StrictHierarchy

-- Recursive lemmas over `StrictHierarchy` bind `Γ s n φ` in their own signature rather than
-- via `variable`: otherwise the equation compiler cannot generalize them.

/-- - [HP98, 0.30] -/
lemma hierarchy {Γ s n} {φ : Semiformula L ξ n} : StrictHierarchy Γ s φ → Hierarchy Γ s φ
  | zero h => h.of_zero
  | ofAlt h => (hierarchy h).accum _
  | exs h => (hierarchy h).exs
  | all h => (hierarchy h).all

/-- - [HP98, 0.30] -/
lemma neg {Γ s n} {φ : Semiformula L ξ n} :
    StrictHierarchy Γ s φ → StrictHierarchy Γ.alt s (∼φ)
  | zero h => zero (by exact (Hierarchy.neg h).of_zero)
  | ofAlt h => ofAlt (by simpa using neg h)
  | exs h => by simpa using (neg h).all
  | all h => by simpa using (neg h).exs

/-- - [HP98, 0.30] -/
lemma rew {Γ s n₁ n₂} {ξ₁ ξ₂ : Type*} {φ : Semiformula L ξ₁ n₁} (ω : Rew L ξ₁ n₁ ξ₂ n₂) :
    StrictHierarchy Γ s φ → StrictHierarchy Γ s (ω ▹ φ)
  | zero h => zero (Hierarchy.rew ω h)
  | ofAlt h => ofAlt (rew ω h)
  | exs h => by simpa using (rew ω.q h).exs
  | all h => by simpa using (rew ω.q h).all

/-- - [HP98, 0.30] -/
lemma of_rew {Γ s n₂} {ξ₂ : Type*} {ψ : Semiformula L ξ₂ n₂} :
    StrictHierarchy Γ s ψ →
      ∀ {ξ₁ : Type*} {n₁ : ℕ} {ω : Rew L ξ₁ n₁ ξ₂ n₂} {φ : Semiformula L ξ₁ n₁},
        ω ▹ φ = ψ → StrictHierarchy Γ s φ
  | zero h => fun e ↦ zero (by rw [← e] at h; simpa using h)
  | ofAlt h => fun e ↦ ofAlt (of_rew h e)
  | exs h => fun e ↦ by
      rcases (Semiformula.eq_exs_iff _).mp e with ⟨φ', hφ', rfl⟩
      exact exs (of_rew h hφ')
  | all h => fun e ↦ by
      rcases (Semiformula.eq_all_iff _).mp e with ⟨φ', hφ', rfl⟩
      exact all (of_rew h hφ')

/-- - [HP98, 0.30] -/
@[simp] lemma rew_iff {Γ s n₁ n₂} {ξ₁ ξ₂ : Type*} {ω : Rew L ξ₁ n₁ ξ₂ n₂}
    {φ : Semiformula L ξ₁ n₁} : StrictHierarchy Γ s (ω ▹ φ) ↔ StrictHierarchy Γ s φ :=
  ⟨fun h ↦ of_rew h rfl, rew ω⟩

/-- - [HP98, 0.30] -/
lemma toPrenex {Γ j s n} {φ : Semiformula L ξ (n + s)} (h : StrictHierarchy (Γ.altItr s) j φ) :
    StrictHierarchy Γ (j + s) (φ.toPrenex Γ s) := by
  induction s generalizing n j with
  | zero => simpa using h
  | succ s ih =>
    rw [Polarity.altItr_succ] at h
    show StrictHierarchy Γ (j + (s + 1)) (Polarity.quantItr Γ (s + 1) φ)
    rw [Polarity.quantItr_succ', show j + (s + 1) = j + 1 + s by omega]
    rcases hΓ : Γ.altItr s with _ | _
    . apply ih
      rw [hΓ] at h ⊢
      exact (ofAlt h).exs
    . apply ih
      rw [hΓ] at h ⊢
      exact (ofAlt h).all

/-- - [HP98, 0.30] -/
lemma toPrenex_of_deltaZero {Γ s n} {φ : Semiformula L ξ (n + s)} (h : Hierarchy 𝚺 0 φ) :
    StrictHierarchy Γ s (φ.toPrenex Γ s) := by simpa using toPrenex (Γ := Γ) (zero h)

/-- - [HP98, 0.30] -/
lemma mono {Γ s s' n} {φ : Semiformula L ξ n} (h : StrictHierarchy Γ s φ) (hs : s ≤ s') :
    StrictHierarchy Γ s' φ := by
  induction h generalizing s' with
  | @zero Γ₀ n₀ φ₀ h =>
    have key : ∀ t Γ', StrictHierarchy Γ' t φ₀ := by
      intro t
      induction t with
      | zero => intro Γ'; exact zero h
      | succ t ih => intro Γ'; exact ofAlt (ih Γ'.alt)
    exact key s' Γ₀
  | @ofAlt Γ₀ s₀ n₀ φ₀ h ih =>
    obtain ⟨t, rfl⟩ : ∃ t, s' = t + 1 := ⟨s' - 1, by omega⟩
    exact ofAlt (ih (s' := t) (by omega))
  | @exs s₀ n₀ φ₀ h ih =>
    obtain ⟨t, rfl⟩ : ∃ t, s' = t + 1 := ⟨s' - 1, by omega⟩
    exact exs (ih (s' := t + 1) (by omega))
  | @all s₀ n₀ φ₀ h ih =>
    obtain ⟨t, rfl⟩ : ∃ t, s' = t + 1 := ⟨s' - 1, by omega⟩
    exact all (ih (s' := t + 1) (by omega))

end StrictHierarchy

section
variable {Γ : Polarity} {s n : ℕ} {ξ : Type*}

/-- - [HP98, 0.30] -/
@[simp, grind .]
lemma Prenex.val_strictHierarchy {φ : Prenex Γ s ξ n} : StrictHierarchy Γ s φ.val :=
  StrictHierarchy.toPrenex_of_deltaZero φ.matrix.sigma_prop

end

/-- Over a theory extending `𝗜𝚺 s`, every `Hierarchy Γ s` formula is provably equivalent to a
prenex `Γ`-formula of level `s`.

- [HP98, 0.30, Theorem I.2.5(3), Lemma I.2.9] -/
theorem exists_strictHierarchy_of_hierarchy {Γ : Polarity} {s n : ℕ}
    (T : ArithmeticTheory) [𝗜𝚺 s ⪯ T] {φ : ArithmeticSemisentence n} (h : Hierarchy Γ s φ) :
    ∃ ψ : ArithmeticSemisentence n, StrictHierarchy Γ s ψ ∧ T ⊢ ∀¹* (φ 🡘 ψ) := by
  obtain ⟨φ', hφ'⟩ := exists_prenex_of_hierarchy T h
  exact ⟨φ'.val, Prenex.val_strictHierarchy, hφ'⟩

end FFL.FirstOrder.Arithmetic
