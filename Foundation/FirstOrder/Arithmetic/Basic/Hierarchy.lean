module

public import Foundation.FirstOrder.Arithmetic.Basic.Model
public import Foundation.FirstOrder.Basic.OperatorHierarchy

@[expose] public section
/-!
# The arithmetical hierarchy

This file specializes the reusable operator-bounded hierarchy to arithmetic,
where bounded quantifiers are those bounded by `<`.
-/
namespace LO.FirstOrder.Arithmetic

variable {L : Language} [L.LT]

/- The reusable operator-bounded hierarchy specialized to `<`. -/
abbrev ArithmeticOperator : Semiformula.Operator L 2 :=
  (Semiformula.Operator.LT.lt : Semiformula.Operator L 2)

/-- The generic operator-bounded hierarchy specialized to `<`. -/
abbrev OperatorArithmeticHierarchy : Polarity → ℕ → {n : ℕ} → Semiformula L ξ n → Prop :=
  OperatorHierarchy.Hierarchy (R := ArithmeticOperator (L := L))

/--
The arithmetical hierarchy, implemented by the generic operator hierarchy with
bounded quantifiers recognized through `<`.
-/
abbrev Hierarchy : Polarity → ℕ → {n : ℕ} → Semiformula L ξ n → Prop :=
  OperatorArithmeticHierarchy

def DeltaZero (φ : Semiformula L ξ n) : Prop := Hierarchy 𝚺 0 φ

namespace Hierarchy

export OperatorHierarchy.Hierarchy
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
  OperatorHierarchy.Hierarchy.exs

lemma all {s n} {φ : Semiformula L ξ (n + 1)} :
    Hierarchy 𝚷 (s + 1) φ → Hierarchy 𝚷 (s + 1) (∀⁰ φ) :=
  OperatorHierarchy.Hierarchy.all

lemma sigma {s n} {φ : Semiformula L ξ (n + 1)} :
    Hierarchy 𝚷 s φ → Hierarchy 𝚺 (s + 1) (∃⁰ φ) :=
  OperatorHierarchy.Hierarchy.sigma

lemma pi {s n} {φ : Semiformula L ξ (n + 1)} :
    Hierarchy 𝚺 s φ → Hierarchy 𝚷 (s + 1) (∀⁰ φ) :=
  OperatorHierarchy.Hierarchy.pi

lemma dummy_sigma {s n} {φ : Semiformula L ξ (n + 1)} :
    Hierarchy 𝚷 (s + 1) φ → Hierarchy 𝚺 (s + 1 + 1) (∀⁰ φ) :=
  OperatorHierarchy.Hierarchy.dummy_sigma

lemma dummy_pi {s n} {φ : Semiformula L ξ (n + 1)} :
    Hierarchy 𝚺 (s + 1) φ → Hierarchy 𝚷 (s + 1 + 1) (∃⁰ φ) :=
  OperatorHierarchy.Hierarchy.dummy_pi

lemma accum {Γ} {s : ℕ} {φ : Semiformula L ξ n} :
    Hierarchy Γ s φ → ∀ Γ', Hierarchy Γ' (s + 1) φ :=
  OperatorHierarchy.Hierarchy.accum (R := ArithmeticOperator (L := L))

lemma strict_mono {Γ s} {φ : Semiformula L ξ n}
    (hp : Hierarchy Γ s φ) (Γ') {s'} (h : s < s') : Hierarchy Γ' s' φ :=
  OperatorHierarchy.Hierarchy.strict_mono (R := ArithmeticOperator (L := L)) hp Γ' h

lemma mono {Γ} {s s' : ℕ} {φ : Semiformula L ξ n}
    (hp : Hierarchy Γ s φ) (h : s ≤ s') : Hierarchy Γ s' φ :=
  OperatorHierarchy.Hierarchy.mono (R := ArithmeticOperator (L := L)) hp h

lemma of_zero {Γ Γ'} {s : ℕ} {φ : Semiformula L ξ n}
    (hp : Hierarchy Γ 0 φ) : Hierarchy Γ' s φ :=
  OperatorHierarchy.Hierarchy.of_zero (R := ArithmeticOperator (L := L)) hp

lemma zero_iff_delta_zero {Γ} {φ : Semiformula L ξ n} :
    Hierarchy Γ 0 φ ↔ DeltaZero φ := by
  simpa [DeltaZero, OperatorHierarchy.DeltaZero] using
    (OperatorHierarchy.Hierarchy.zero_iff_delta_zero
      (R := ArithmeticOperator (L := L)) (Γ := Γ) (φ := φ))

lemma ball {Γ s n} {φ : Semiformula L ξ (n + 1)} {t : Semiterm L ξ (n + 1)} :
    t.Positive → Hierarchy Γ s φ → Hierarchy Γ s (∀⁰[“x. x < !!t”] φ) :=
  OperatorHierarchy.Hierarchy.ball (R := ArithmeticOperator (L := L))

lemma bexs {Γ s n} {φ : Semiformula L ξ (n + 1)} {t : Semiterm L ξ (n + 1)} :
    t.Positive → Hierarchy Γ s φ → Hierarchy Γ s (∃⁰[“x. x < !!t”] φ) :=
  OperatorHierarchy.Hierarchy.bexs (R := ArithmeticOperator (L := L))

section

variable {L : Language}

@[simp] lemma equal [L.Eq] [L.LT] {t u : Semiterm L ξ n} : Hierarchy Γ s “!!t = !!u” := by
  simp [Semiformula.Operator.operator, Matrix.fun_eq_vec_two,
    Semiformula.Operator.Eq.sentence_eq]

@[simp] lemma lt [L.LT] {t u : Semiterm L ξ n} : Hierarchy Γ s “!!t < !!u” := by
  simp [Semiformula.Operator.operator, Matrix.fun_eq_vec_two,
    Semiformula.Operator.LT.sentence_eq]

@[simp] lemma le [L.Eq] [L.LT] {t u : Semiterm L ξ n} : Hierarchy Γ s “!!t ≤ !!u” := by
  simp [Semiformula.Operator.operator, Matrix.fun_eq_vec_two,
    Semiformula.Operator.Eq.sentence_eq, Semiformula.Operator.LT.sentence_eq,
    Semiformula.Operator.LE.sentence_eq]

end

@[simp] lemma ball_iff {Γ s n} {φ : Semiformula L ξ (n + 1)} {t : Semiterm L ξ (n + 1)}
    (ht : t.Positive) :
    Hierarchy Γ s (∀⁰[“x. x < !!t”] φ) ↔ Hierarchy Γ s φ :=
  OperatorHierarchy.Hierarchy.ball_iff (R := ArithmeticOperator (L := L)) ht

@[simp] lemma bexs_iff {Γ s n} {φ : Semiformula L ξ (n + 1)} {t : Semiterm L ξ (n + 1)}
    (ht : t.Positive) :
    Hierarchy Γ s (∃⁰[“x. x < !!t”] φ) ↔ Hierarchy Γ s φ :=
  OperatorHierarchy.Hierarchy.bexs_iff (R := ArithmeticOperator (L := L)) ht

@[simp] lemma ballLT_iff {Γ s n} {φ : Semiformula L ξ (n + 1)} {t : Semiterm L ξ n} :
    Hierarchy Γ s (φ.ballLT t) ↔ Hierarchy Γ s φ := by simp [Semiformula.ballLT]

@[simp] lemma bexsLT_iff {Γ s n} {φ : Semiformula L ξ (n + 1)} {t : Semiterm L ξ n} :
    Hierarchy Γ s (φ.bexsLT t) ↔ Hierarchy Γ s φ := by simp [Semiformula.bexsLT]

@[simp] lemma ballLTSucc_iff [L.Zero] [L.One] [L.Add] {Γ s n}
    {φ : Semiformula L ξ (n + 1)} {t : Semiterm L ξ n} :
    Hierarchy Γ s (φ.ballLTSucc t) ↔ Hierarchy Γ s φ := by simp [Semiformula.ballLTSucc]

@[simp] lemma bexsLTSucc_iff [L.Zero] [L.One] [L.Add] {Γ s n}
    {φ : Semiformula L ξ (n + 1)} {t : Semiterm L ξ n} :
    Hierarchy Γ s (φ.bexsLTSucc t) ↔ Hierarchy Γ s φ := by simp [Semiformula.bexsLTSucc]

end Hierarchy

section LOR

lemma sigma₁_induction {P : (n : ℕ) → ArithmeticSemiformula ξ n → Prop}
    (hVerum : ∀ n, P n ⊤)
    (hFalsum : ∀ n, P n ⊥)
    (hEQ : ∀ n t₁ t₂, P n (.rel Language.Eq.eq ![t₁, t₂]))
    (hNEQ : ∀ n t₁ t₂, P n (.nrel Language.Eq.eq ![t₁, t₂]))
    (hLT : ∀ n t₁ t₂, P n (.rel Language.LT.lt ![t₁, t₂]))
    (hNLT : ∀ n t₁ t₂, P n (.nrel Language.LT.lt ![t₁, t₂]))
    (hAnd : ∀ n φ ψ, Hierarchy 𝚺 1 φ → Hierarchy 𝚺 1 ψ → P n φ → P n ψ → P n (φ ⋏ ψ))
    (hOr : ∀ n φ ψ, Hierarchy 𝚺 1 φ → Hierarchy 𝚺 1 ψ → P n φ → P n ψ → P n (φ ⋎ ψ))
    (hBall : ∀ n t φ, Hierarchy 𝚺 1 φ → P (n + 1) φ → P n (∀⁰[“#0 < !!(Rew.bShift t)”] φ))
    (hExs : ∀ n φ, Hierarchy 𝚺 1 φ → P (n + 1) φ → P n (∃⁰ φ)) (n φ) :
    Hierarchy 𝚺 1 φ → P n φ :=
  OperatorHierarchy.Hierarchy.sigma₁_induction
    (R := ArithmeticOperator (L := ℒₒᵣ)) (P := P)
    hVerum hFalsum
    (by
      intro n k r v
      cases r
      · change P n (.rel Language.Eq.eq v)
        simpa [←Matrix.fun_eq_vec_two] using hEQ n (v 0) (v 1)
      · change P n (.rel Language.LT.lt v)
        simpa [←Matrix.fun_eq_vec_two] using hLT n (v 0) (v 1))
    (by
      intro n k r v
      cases r
      · change P n (.nrel Language.Eq.eq v)
        simpa [←Matrix.fun_eq_vec_two] using hNEQ n (v 0) (v 1)
      · change P n (.nrel Language.LT.lt v)
        simpa [←Matrix.fun_eq_vec_two] using hNLT n (v 0) (v 1))
    hAnd hOr
    (by
      intro n t φ hφ hp
      simpa [ArithmeticOperator, Semiformula.Operator.lt_def] using hBall n t φ hφ hp)
    hExs
    (by
      intro n t
      simpa [ArithmeticOperator, Semiformula.Operator.lt_def] using hLT (n + 1) #0 (Rew.bShift t))
    n φ

lemma sigma₁_induction' {n φ} (hp : Hierarchy 𝚺 1 φ)
    {P : (n : ℕ) → ArithmeticSemiformula ξ n → Prop}
    (hVerum : ∀ n, P n ⊤)
    (hFalsum : ∀ n, P n ⊥)
    (hEQ : ∀ n t₁ t₂, P n (.rel Language.Eq.eq ![t₁, t₂]))
    (hNEQ : ∀ n t₁ t₂, P n (.nrel Language.Eq.eq ![t₁, t₂]))
    (hLT : ∀ n t₁ t₂, P n (.rel Language.LT.lt ![t₁, t₂]))
    (hNLT : ∀ n t₁ t₂, P n (.nrel Language.LT.lt ![t₁, t₂]))
    (hAnd : ∀ n φ ψ, Hierarchy 𝚺 1 φ → Hierarchy 𝚺 1 ψ → P n φ → P n ψ → P n (φ ⋏ ψ))
    (hOr : ∀ n φ ψ, Hierarchy 𝚺 1 φ → Hierarchy 𝚺 1 ψ → P n φ → P n ψ → P n (φ ⋎ ψ))
    (hBall : ∀ n t φ, Hierarchy 𝚺 1 φ → P (n + 1) φ → P n (∀⁰[“#0 < !!(Rew.bShift t)”] φ))
    (hExs : ∀ n φ, Hierarchy 𝚺 1 φ → P (n + 1) φ → P n (∃⁰ φ)) : P n φ :=
  sigma₁_induction hVerum hFalsum hEQ hNEQ hLT hNLT hAnd hOr hBall hExs n φ hp

end LOR

end Arithmetic

abbrev ArithmeticTheory.SoundOnHierarchy (T : ArithmeticTheory) (Γ : Polarity) (k : ℕ) := T.SoundOn (Arithmetic.Hierarchy Γ k)

lemma ArithmeticTheory.soundOnHierarchy (T : ArithmeticTheory) (Γ : Polarity) (k : ℕ) [T.SoundOnHierarchy Γ k] :
    T ⊢ σ → Arithmetic.Hierarchy Γ k σ → ℕ↓[ℒₒᵣ] ⊧ σ := SoundOn.sound

instance (T : ArithmeticTheory) [T.SoundOnHierarchy 𝚺 1] : Entailment.Consistent T :=
  T.consistent_of_sound (Arithmetic.Hierarchy 𝚺 1) (by simp)

instance (T : ArithmeticTheory) [T.SoundOnHierarchy 𝚷 2] : Entailment.Consistent T :=
  T.consistent_of_sound (Arithmetic.Hierarchy 𝚷 2) (by simp)

end FirstOrder

end LO
