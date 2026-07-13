module

public import Foundation.FirstOrder.Arithmetic.Basic.Hierarchy

@[expose] public section
namespace LO.FirstOrder.Arithmetic

variable {L : Language} [L.LT]

/-- A genuinely prenex (non-cumulative) Σ_n/Π_n class; level 1 is based on all of Σ₁/Π₁. -/
inductive StrictHierarchy : Polarity → ℕ → {n : ℕ} → Semiformula L ξ n → Prop
  | base {Γ φ} : Hierarchy Γ 1 φ → StrictHierarchy Γ 1 φ
  | exs {s n} {φ : Semiformula L ξ (n + 1)} :
      StrictHierarchy 𝚷 (s + 1) φ → StrictHierarchy 𝚺 (s + 2) (∃⁰ φ)
  | all {s n} {φ : Semiformula L ξ (n + 1)} :
      StrictHierarchy 𝚺 (s + 1) φ → StrictHierarchy 𝚷 (s + 2) (∀⁰ φ)

namespace StrictHierarchy

-- Note: `hierarchy`, `neg`, and `rew` below are defined by recursive pattern matching on
-- `StrictHierarchy`. Lean's equation compiler needs the indices `Γ`, `s`, `φ` (and hence `n`)
-- to be freshly bound directly in each declaration's own signature in order to generalize them
-- correctly across the recursive calls; reusing a shared `variable` here breaks that
-- generalization. So we keep these three self-contained and share `variable`s only for the
-- remaining (non-recursive) lemmas below.

lemma hierarchy {Γ s} {φ : Semiformula L ξ n} : StrictHierarchy Γ s φ → Hierarchy Γ s φ
  | base h => h
  | exs h => (hierarchy h).sigma
  | all h => (hierarchy h).pi

lemma neg {Γ s} {φ : Semiformula L ξ n} : StrictHierarchy Γ s φ → StrictHierarchy Γ.alt s (∼φ)
  | base h => base h.neg
  | exs h => by simpa using (neg h).all
  | all h => by simpa using (neg h).exs

lemma rew {Γ s} {φ : Semiformula L ξ₁ n₁} (ω : Rew L ξ₁ n₁ ξ₂ n₂) :
    StrictHierarchy Γ s φ → StrictHierarchy Γ s (ω ▹ φ)
  | base h => base (h.rew ω)
  | exs h => by simpa using (rew ω.q h).exs
  | all h => by simpa using (rew ω.q h).all

variable {ξ : Type*} {n : ℕ} {Γ : Polarity} {s : ℕ} {φ : Semiformula L ξ n}

@[simp] lemma neg_iff :
    StrictHierarchy Γ s (∼φ) ↔ StrictHierarchy Γ.alt s φ :=
  ⟨fun h => by simpa using neg h, fun h => by simpa using neg h⟩

lemma sigma_of_sigma_ex {φ : Semiformula L ξ (n + 1)} :
    StrictHierarchy 𝚺 (s + 2) (∃⁰ φ) → StrictHierarchy 𝚷 (s + 1) φ := by
  generalize hr : ∃⁰ φ = r
  generalize hb : (𝚺 : Polarity) = Γ
  intro H
  cases H <;> simp_all

@[simp] lemma exs_iff {φ : Semiformula L ξ (n + 1)} :
    StrictHierarchy 𝚺 (s + 2) (∃⁰ φ) ↔ StrictHierarchy 𝚷 (s + 1) φ :=
  ⟨sigma_of_sigma_ex, exs⟩

lemma pi_of_pi_all {φ : Semiformula L ξ (n + 1)} :
    StrictHierarchy 𝚷 (s + 2) (∀⁰ φ) → StrictHierarchy 𝚺 (s + 1) φ := by
  generalize hr : ∀⁰ φ = r
  generalize hb : (𝚷 : Polarity) = Γ
  intro H
  cases H <;> simp_all

@[simp] lemma all_iff {φ : Semiformula L ξ (n + 1)} :
    StrictHierarchy 𝚷 (s + 2) (∀⁰ φ) ↔ StrictHierarchy 𝚺 (s + 1) φ :=
  ⟨pi_of_pi_all, all⟩

lemma sigma_succ_elim :
    StrictHierarchy 𝚺 (s + 2) φ → ∃ ψ : Semiformula L ξ (n + 1), φ = ∃⁰ ψ ∧ StrictHierarchy 𝚷 (s + 1) ψ := by
  generalize hb : (𝚺 : Polarity) = Γ
  intro H
  cases H <;> simp_all

lemma pi_succ_elim :
    StrictHierarchy 𝚷 (s + 2) φ → ∃ ψ : Semiformula L ξ (n + 1), φ = ∀⁰ ψ ∧ StrictHierarchy 𝚺 (s + 1) ψ := by
  generalize hb : (𝚷 : Polarity) = Γ
  intro H
  cases H <;> simp_all

end StrictHierarchy

end LO.FirstOrder.Arithmetic
