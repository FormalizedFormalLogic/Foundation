module

public import Foundation.FirstOrder.Arithmetic.Basic.Hierarchy

/-!
# Strict arithmetical hierarchy

`StrictHierarchy Γ s φ` is the genuinely prenex (non-cumulative) subclass of `Hierarchy Γ s φ`:
`strictΣ₀ = strictΠ₀ = Δ₀`, `strictΣₛ₊₁ = ∃¹ strictΠₛ`, `strictΠₛ₊₁ = ∀¹ strictΣₛ`.

The base case (`zero`) could be generalized to an arbitrary formula set `S` by replacing it with
`base : φ ∈ S → StrictHierarchy Γ 0 φ`; this generalization is not carried out here.
-/

@[expose] public section
namespace LO.FirstOrder.Arithmetic

variable {L : Language} [L.LT]

inductive StrictHierarchy : Polarity → ℕ → {n : ℕ} → Semiformula L ξ n → Prop
  | zero {Γ φ} : Hierarchy 𝚺 0 φ → StrictHierarchy Γ 0 φ
  | sigma {s n} {φ : Semiformula L ξ (n + 1)} :
      StrictHierarchy 𝚷 s φ → StrictHierarchy 𝚺 (s + 1) (∃¹ φ)
  | pi {s n} {φ : Semiformula L ξ (n + 1)} :
      StrictHierarchy 𝚺 s φ → StrictHierarchy 𝚷 (s + 1) (∀¹ φ)

namespace StrictHierarchy

-- Note: `hierarchy`, `neg`, and `rew` below are defined by recursive pattern matching on
-- `StrictHierarchy`. Lean's equation compiler needs the indices `Γ`, `s`, `φ` (and hence `n`)
-- to be freshly bound directly in each declaration's own signature in order to generalize them
-- correctly across the recursive calls; reusing a shared `variable` here breaks that
-- generalization. So we keep these three self-contained and share `variable`s only for the
-- remaining (non-recursive) lemmas below.

lemma hierarchy {Γ s} {φ : Semiformula L ξ n} : StrictHierarchy Γ s φ → Hierarchy Γ s φ
  | zero h => h.of_zero
  | sigma h => (hierarchy h).sigma
  | pi h => (hierarchy h).pi

lemma neg {Γ s} {φ : Semiformula L ξ n} : StrictHierarchy Γ s φ → StrictHierarchy Γ.alt s (∼φ)
  | zero h => zero h.neg.of_zero
  | sigma h => by simpa using (neg h).pi
  | pi h => by simpa using (neg h).sigma

lemma rew {Γ s} {φ : Semiformula L ξ₁ n₁} (ω : Rew L ξ₁ n₁ ξ₂ n₂) :
    StrictHierarchy Γ s φ → StrictHierarchy Γ s (ω ▹ φ)
  | zero h => zero (h.rew ω)
  | sigma h => by simpa using (rew ω.q h).sigma
  | pi h => by simpa using (rew ω.q h).pi

variable {ξ : Type*} {n : ℕ} {Γ : Polarity} {s : ℕ} {φ : Semiformula L ξ n}

@[simp] lemma neg_iff :
    StrictHierarchy Γ s (∼φ) ↔ StrictHierarchy Γ.alt s φ :=
  ⟨fun h => by simpa using neg h, fun h => by simpa using neg h⟩

lemma zero_iff : StrictHierarchy Γ 0 φ ↔ Hierarchy 𝚺 0 φ :=
  ⟨fun h => Hierarchy.zero_iff.mp h.hierarchy, zero⟩

lemma zero_eq_alt : StrictHierarchy Γ 0 φ → StrictHierarchy Γ.alt 0 φ := by
  simp [zero_iff];

lemma sigma_of_sigma_ex {φ : Semiformula L ξ (n + 1)} :
    StrictHierarchy 𝚺 (s + 1) (∃¹ φ) → StrictHierarchy 𝚷 s φ := by
  generalize hr : ∃¹ φ = r;
  generalize hb : (𝚺 : Polarity) = Γ;
  intro H;
  cases H <;> simp_all;

@[simp] lemma exs_iff {φ : Semiformula L ξ (n + 1)} :
    StrictHierarchy 𝚺 (s + 1) (∃¹ φ) ↔ StrictHierarchy 𝚷 s φ :=
  ⟨sigma_of_sigma_ex, sigma⟩

lemma pi_of_pi_all {φ : Semiformula L ξ (n + 1)} :
    StrictHierarchy 𝚷 (s + 1) (∀¹ φ) → StrictHierarchy 𝚺 s φ := by
  generalize hr : ∀¹ φ = r;
  generalize hb : (𝚷 : Polarity) = Γ;
  intro H;
  cases H <;> simp_all;

@[simp] lemma all_iff {φ : Semiformula L ξ (n + 1)} :
    StrictHierarchy 𝚷 (s + 1) (∀¹ φ) ↔ StrictHierarchy 𝚺 s φ :=
  ⟨pi_of_pi_all, pi⟩

lemma sigma_succ_elim :
    StrictHierarchy 𝚺 (s + 1) φ → ∃ ψ : Semiformula L ξ (n + 1), φ = ∃¹ ψ ∧ StrictHierarchy 𝚷 s ψ := by
  generalize hb : (𝚺 : Polarity) = Γ;
  intro H;
  cases H <;> simp_all;

lemma pi_succ_elim :
    StrictHierarchy 𝚷 (s + 1) φ → ∃ ψ : Semiformula L ξ (n + 1), φ = ∀¹ ψ ∧ StrictHierarchy 𝚺 s ψ := by
  generalize hb : (𝚷 : Polarity) = Γ;
  intro H;
  cases H <;> simp_all;

end StrictHierarchy

end LO.FirstOrder.Arithmetic
