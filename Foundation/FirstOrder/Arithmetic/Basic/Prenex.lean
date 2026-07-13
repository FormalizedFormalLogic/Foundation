module

public import Foundation.FirstOrder.Arithmetic.Basic.Hierarchy

@[expose] public section
namespace LO.FirstOrder.Arithmetic

variable {L : Language} [L.LT]

/-- 厳密な（冠頭）Σ_n/Π_n クラス．レベル1は Σ₁/Π₁ 全体を基底とする -/
inductive StrictHierarchy : Polarity → ℕ → {n : ℕ} → Semiformula L ξ n → Prop
  | base {Γ φ} : Hierarchy Γ 1 φ → StrictHierarchy Γ 1 φ
  | exs {s n} {φ : Semiformula L ξ (n + 1)} :
      StrictHierarchy 𝚷 (s + 1) φ → StrictHierarchy 𝚺 (s + 2) (∃⁰ φ)
  | all {s n} {φ : Semiformula L ξ (n + 1)} :
      StrictHierarchy 𝚺 (s + 1) φ → StrictHierarchy 𝚷 (s + 2) (∀⁰ φ)

namespace StrictHierarchy

lemma hierarchy {Γ s} {φ : Semiformula L ξ n} : StrictHierarchy Γ s φ → Hierarchy Γ s φ
  | base h => h
  | exs h => (hierarchy h).sigma
  | all h => (hierarchy h).pi

lemma neg {Γ s} {φ : Semiformula L ξ n} : StrictHierarchy Γ s φ → StrictHierarchy Γ.alt s (∼φ)
  | base h => base h.neg
  | exs h => by simpa using (neg h).all
  | all h => by simpa using (neg h).exs

@[simp] lemma neg_iff {Γ s} {φ : Semiformula L ξ n} :
    StrictHierarchy Γ s (∼φ) ↔ StrictHierarchy Γ.alt s φ :=
  ⟨fun h => by simpa using neg h, fun h => by simpa using neg h⟩

lemma rew {φ : Semiformula L ξ₁ n₁} (ω : Rew L ξ₁ n₁ ξ₂ n₂) :
    StrictHierarchy Γ s φ → StrictHierarchy Γ s (ω ▹ φ)
  | base h => base (h.rew ω)
  | exs h => by simpa using (rew ω.q h).exs
  | all h => by simpa using (rew ω.q h).all

set_option linter.flexible false in
lemma sigma_of_sigma_ex {φ : Semiformula L ξ (n + 1)} :
    StrictHierarchy 𝚺 (s + 2) (∃⁰ φ) → StrictHierarchy 𝚷 (s + 1) φ := by
  generalize hr : ∃⁰ φ = r
  generalize hb : (𝚺 : Polarity) = Γ
  intro H
  cases H <;> simp_all

@[simp] lemma exs_iff {φ : Semiformula L ξ (n + 1)} :
    StrictHierarchy 𝚺 (s + 2) (∃⁰ φ) ↔ StrictHierarchy 𝚷 (s + 1) φ :=
  ⟨sigma_of_sigma_ex, exs⟩

set_option linter.flexible false in
lemma pi_of_pi_all {φ : Semiformula L ξ (n + 1)} :
    StrictHierarchy 𝚷 (s + 2) (∀⁰ φ) → StrictHierarchy 𝚺 (s + 1) φ := by
  generalize hr : ∀⁰ φ = r
  generalize hb : (𝚷 : Polarity) = Γ
  intro H
  cases H <;> simp_all

@[simp] lemma all_iff {φ : Semiformula L ξ (n + 1)} :
    StrictHierarchy 𝚷 (s + 2) (∀⁰ φ) ↔ StrictHierarchy 𝚺 (s + 1) φ :=
  ⟨pi_of_pi_all, all⟩

end StrictHierarchy

end LO.FirstOrder.Arithmetic
