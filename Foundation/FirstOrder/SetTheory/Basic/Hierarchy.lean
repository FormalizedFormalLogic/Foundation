module

public import Foundation.FirstOrder.SetTheory.Basic.Model
public import Foundation.FirstOrder.Basic.BoundingHierarchy

@[expose] public section
/-!
# The Lévy hierarchy

This file specializes the reusable bounding hierarchy to set theory,
where bounded quantifiers are those bounded by membership.
-/

namespace LO.FirstOrder.SetTheory

variable {L : Language} [L.Mem]

/-- The reusable bounding relation specialized to membership. -/
abbrev LevyBounding : Semiformula.Operator L 2 :=
  (Semiformula.Operator.Mem.mem : Semiformula.Operator L 2)

/--
The set-theoretic Levy hierarchy, implemented by the generic bounding hierarchy
with bounded quantifiers recognized through membership.
-/
abbrev Hierarchy : Polarity → ℕ → {n : ℕ} → Semiformula L ξ n → Prop :=
  BoundingHierarchy.Hierarchy (R := LevyBounding (L := L))

def DeltaZero (φ : Semiformula L ξ n) : Prop :=
  Hierarchy 𝚺 0 φ

namespace Hierarchy

export BoundingHierarchy.Hierarchy
  (verum falsum rel nrel and or and_iff
   or_iff conj_iff zero_eq_alt pi_zero_iff_sigma_zero zero_iff alt_zero_iff_zero
   neg neg_iff imp_iff pi_of_pi_all all_iff
   allItr_iff sigma_of_sigma_ex sigma_iff exsItr_iff rew rew_iff exsClosure of_open
   iff_iff iff_iff₀ matrix_conj_iff remove_forall remove_exists padding_iff
   list_conj₂_iff list_disj₂_iff list_conj'_iff list_disj'_iff
   finset_conj'_iff finset_disj'_iff finset_uconj_iff finset_udisj_iff
   exsItr allItr)

lemma exs {s n} {φ : Semiformula L ξ (n + 1)} :
    Hierarchy 𝚺 (s + 1) φ → Hierarchy 𝚺 (s + 1) (∃⁰ φ) :=
  BoundingHierarchy.Hierarchy.exs

lemma all {s n} {φ : Semiformula L ξ (n + 1)} :
    Hierarchy 𝚷 (s + 1) φ → Hierarchy 𝚷 (s + 1) (∀⁰ φ) :=
  BoundingHierarchy.Hierarchy.all

lemma sigma {s n} {φ : Semiformula L ξ (n + 1)} :
    Hierarchy 𝚷 s φ → Hierarchy 𝚺 (s + 1) (∃⁰ φ) :=
  BoundingHierarchy.Hierarchy.sigma

lemma pi {s n} {φ : Semiformula L ξ (n + 1)} :
    Hierarchy 𝚺 s φ → Hierarchy 𝚷 (s + 1) (∀⁰ φ) :=
  BoundingHierarchy.Hierarchy.pi

lemma dummy_sigma {s n} {φ : Semiformula L ξ (n + 1)} :
    Hierarchy 𝚷 (s + 1) φ → Hierarchy 𝚺 (s + 1 + 1) (∀⁰ φ) :=
  BoundingHierarchy.Hierarchy.dummy_sigma

lemma dummy_pi {s n} {φ : Semiformula L ξ (n + 1)} :
    Hierarchy 𝚺 (s + 1) φ → Hierarchy 𝚷 (s + 1 + 1) (∃⁰ φ) :=
  BoundingHierarchy.Hierarchy.dummy_pi

lemma accum {Γ} {s : ℕ} {φ : Semiformula L ξ n} :
    Hierarchy Γ s φ → ∀ Γ', Hierarchy Γ' (s + 1) φ :=
  BoundingHierarchy.Hierarchy.accum (R := LevyBounding (L := L))

lemma strict_mono {Γ s} {φ : Semiformula L ξ n}
    (hp : Hierarchy Γ s φ) (Γ') {s'} (h : s < s') : Hierarchy Γ' s' φ :=
  BoundingHierarchy.Hierarchy.strict_mono (R := LevyBounding (L := L)) hp Γ' h

lemma mono {Γ} {s s' : ℕ} {φ : Semiformula L ξ n}
    (hp : Hierarchy Γ s φ) (h : s ≤ s') : Hierarchy Γ s' φ :=
  BoundingHierarchy.Hierarchy.mono (R := LevyBounding (L := L)) hp h

lemma of_zero {Γ Γ'} {s : ℕ} {φ : Semiformula L ξ n}
    (hp : Hierarchy Γ 0 φ) : Hierarchy Γ' s φ :=
  BoundingHierarchy.Hierarchy.of_zero (R := LevyBounding (L := L)) hp

lemma zero_iff_delta_zero {Γ} {φ : Semiformula L ξ n} :
    Hierarchy Γ 0 φ ↔ DeltaZero φ := by
  simpa [DeltaZero, BoundingHierarchy.DeltaZero] using
    (BoundingHierarchy.Hierarchy.zero_iff_delta_zero
      (R := LevyBounding (L := L)) (Γ := Γ) (φ := φ))

lemma ball {Γ s n} {φ : Semiformula L ξ (n + 1)} {t : Semiterm L ξ (n + 1)} :
    t.Positive → Hierarchy Γ s φ → Hierarchy Γ s (∀⁰[“x. x ∈ !!t”] φ) :=
  BoundingHierarchy.Hierarchy.ball (R := LevyBounding (L := L))

lemma bexs {Γ s n} {φ : Semiformula L ξ (n + 1)} {t : Semiterm L ξ (n + 1)} :
    t.Positive → Hierarchy Γ s φ → Hierarchy Γ s (∃⁰[“x. x ∈ !!t”] φ) :=
  BoundingHierarchy.Hierarchy.bexs (R := LevyBounding (L := L))

section

variable {L : Language}

@[simp] lemma equal [L.Eq] [L.Mem] {t u : Semiterm L ξ n} : Hierarchy Γ s “!!t = !!u” := by
  simp [Semiformula.Operator.operator, Matrix.fun_eq_vec_two,
    Semiformula.Operator.Eq.sentence_eq]

@[simp] lemma mem [L.Mem] {t u : Semiterm L ξ n} : Hierarchy Γ s “!!t ∈ !!u” := by
  simp [Semiformula.Operator.operator, Matrix.fun_eq_vec_two,
    Semiformula.Operator.Mem.sentence_eq]

end

@[simp] lemma ball_iff {Γ s n} {φ : Semiformula L ξ (n + 1)} {t : Semiterm L ξ (n + 1)}
    (ht : t.Positive) :
    Hierarchy Γ s (∀⁰[“x. x ∈ !!t”] φ) ↔ Hierarchy Γ s φ :=
  BoundingHierarchy.Hierarchy.ball_iff (R := LevyBounding (L := L)) ht

@[simp] lemma bexs_iff {Γ s n} {φ : Semiformula L ξ (n + 1)} {t : Semiterm L ξ (n + 1)}
    (ht : t.Positive) :
    Hierarchy Γ s (∃⁰[“x. x ∈ !!t”] φ) ↔ Hierarchy Γ s φ :=
  BoundingHierarchy.Hierarchy.bexs_iff (R := LevyBounding (L := L)) ht

@[simp] lemma ballMem_iff {Γ s n} {φ : Semiformula L ξ (n + 1)} {t : Semiterm L ξ n} :
    Hierarchy Γ s (φ.ballMem t) ↔ Hierarchy Γ s φ := by simp [Semiformula.ballMem]

@[simp] lemma bexsMem_iff {Γ s n} {φ : Semiformula L ξ (n + 1)} {t : Semiterm L ξ n} :
    Hierarchy Γ s (φ.bexsMem t) ↔ Hierarchy Γ s φ := by simp [Semiformula.bexsMem]

end Hierarchy

section SetLanguage

lemma sigma₁_induction {P : (n : ℕ) → SetTheorySemiformula ξ n → Prop}
    (hVerum : ∀ n, P n ⊤)
    (hFalsum : ∀ n, P n ⊥)
    (hEQ : ∀ n t₁ t₂, P n (.rel Language.Eq.eq ![t₁, t₂]))
    (hNEQ : ∀ n t₁ t₂, P n (.nrel Language.Eq.eq ![t₁, t₂]))
    (hMem : ∀ n t₁ t₂, P n (.rel Language.Mem.mem ![t₁, t₂]))
    (hNMem : ∀ n t₁ t₂, P n (.nrel Language.Mem.mem ![t₁, t₂]))
    (hAnd : ∀ n φ ψ, Hierarchy 𝚺 1 φ → Hierarchy 𝚺 1 ψ → P n φ → P n ψ → P n (φ ⋏ ψ))
    (hOr : ∀ n φ ψ, Hierarchy 𝚺 1 φ → Hierarchy 𝚺 1 ψ → P n φ → P n ψ → P n (φ ⋎ ψ))
    (hBall : ∀ n t φ, Hierarchy 𝚺 1 φ → P (n + 1) φ → P n (∀⁰[“#0 ∈ !!(Rew.bShift t)”] φ))
    (hExs : ∀ n φ, Hierarchy 𝚺 1 φ → P (n + 1) φ → P n (∃⁰ φ)) (n φ) :
    Hierarchy 𝚺 1 φ → P n φ :=
  BoundingHierarchy.Hierarchy.sigma₁_induction
    (R := LevyBounding (L := ℒₛₑₜ)) (P := P)
    hVerum hFalsum
    (by
      intro n k r v
      cases r
      · change P n (.rel Language.Eq.eq v)
        simpa [←Matrix.fun_eq_vec_two] using hEQ n (v 0) (v 1)
      · change P n (.rel Language.Mem.mem v)
        simpa [←Matrix.fun_eq_vec_two] using hMem n (v 0) (v 1))
    (by
      intro n k r v
      cases r
      · change P n (.nrel Language.Eq.eq v)
        simpa [←Matrix.fun_eq_vec_two] using hNEQ n (v 0) (v 1)
      · change P n (.nrel Language.Mem.mem v)
        simpa [←Matrix.fun_eq_vec_two] using hNMem n (v 0) (v 1))
    hAnd hOr
    (by
      intro n t φ hφ hp
      simpa [LevyBounding, Semiformula.Operator.mem_def] using hBall n t φ hφ hp)
    hExs
    (by
      intro n t
      simpa [LevyBounding, Semiformula.Operator.mem_def] using hMem (n + 1) #0 (Rew.bShift t))
    n φ

lemma sigma₁_induction' {n φ} (hp : Hierarchy 𝚺 1 φ)
    {P : (n : ℕ) → SetTheorySemiformula ξ n → Prop}
    (hVerum : ∀ n, P n ⊤)
    (hFalsum : ∀ n, P n ⊥)
    (hEQ : ∀ n t₁ t₂, P n (.rel Language.Eq.eq ![t₁, t₂]))
    (hNEQ : ∀ n t₁ t₂, P n (.nrel Language.Eq.eq ![t₁, t₂]))
    (hMem : ∀ n t₁ t₂, P n (.rel Language.Mem.mem ![t₁, t₂]))
    (hNMem : ∀ n t₁ t₂, P n (.nrel Language.Mem.mem ![t₁, t₂]))
    (hAnd : ∀ n φ ψ, Hierarchy 𝚺 1 φ → Hierarchy 𝚺 1 ψ → P n φ → P n ψ → P n (φ ⋏ ψ))
    (hOr : ∀ n φ ψ, Hierarchy 𝚺 1 φ → Hierarchy 𝚺 1 ψ → P n φ → P n ψ → P n (φ ⋎ ψ))
    (hBall : ∀ n t φ, Hierarchy 𝚺 1 φ → P (n + 1) φ → P n (∀⁰[“#0 ∈ !!(Rew.bShift t)”] φ))
    (hExs : ∀ n φ, Hierarchy 𝚺 1 φ → P (n + 1) φ → P n (∃⁰ φ)) : P n φ :=
  sigma₁_induction hVerum hFalsum hEQ hNEQ hMem hNMem hAnd hOr hBall hExs n φ hp

end SetLanguage

end SetTheory

end FirstOrder

end LO
