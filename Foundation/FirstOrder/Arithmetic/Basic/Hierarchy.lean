module

public import Foundation.FirstOrder.Arithmetic.Basic.Model

@[expose] public section

namespace LO.FirstOrder.Arithmetic

variable {L : Language} [L.LT]

abbrev BoundingOperator : Semiformula.Operator L 2 :=
  (Semiformula.Operator.LT.lt : Semiformula.Operator L 2)

abbrev Hierarchy : Polarity → ℕ → {n : ℕ} → Semiformula L ξ n → Prop :=
  BoundingHierarchy (R := BoundingOperator (L := L))

def DeltaZero (φ : Semiformula L ξ n) : Prop := Hierarchy 𝚺 0 φ

namespace Hierarchy

abbrev rec := @BoundingHierarchy.rec (R := BoundingOperator (L := L))

abbrev recOn := @BoundingHierarchy.recOn (R := BoundingOperator (L := L))

abbrev casesOn := @BoundingHierarchy.casesOn (R := BoundingOperator (L := L))

abbrev below := @BoundingHierarchy.below (R := BoundingOperator (L := L))

abbrev brecOn := @BoundingHierarchy.brecOn (R := BoundingOperator (L := L))

section Constructors

universe u v

variable {L : Language.{u}} [L.LT] {ξ : Type v}

@[simp, match_pattern] abbrev verum (Γ s n) : Hierarchy Γ s (⊤ : Semiformula L ξ n) :=
  BoundingHierarchy.verum Γ s n

@[simp, match_pattern] abbrev falsum (Γ s n) : Hierarchy Γ s (⊥ : Semiformula L ξ n) :=
  BoundingHierarchy.falsum Γ s n

@[simp, match_pattern] abbrev rel (Γ s) {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ x) :
    Hierarchy Γ s (Semiformula.rel r v) :=
  BoundingHierarchy.rel Γ s r v

@[simp, match_pattern] abbrev nrel (Γ s) {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ x) :
    Hierarchy Γ s (Semiformula.nrel r v) :=
  BoundingHierarchy.nrel Γ s r v

@[match_pattern] abbrev and {Γ s n} {φ ψ : Semiformula L ξ n} :
    Hierarchy Γ s φ → Hierarchy Γ s ψ → Hierarchy Γ s (φ ⋏ ψ) :=
  BoundingHierarchy.and

@[match_pattern] abbrev or {Γ s n} {φ ψ : Semiformula L ξ n} :
    Hierarchy Γ s φ → Hierarchy Γ s ψ → Hierarchy Γ s (φ ⋎ ψ) :=
  BoundingHierarchy.or

@[match_pattern] abbrev ball {Γ s n} {φ : Semiformula L ξ (n + 1)}
    {t : Semiterm L ξ (n + 1)} :
    t.Positive → Hierarchy Γ s φ → Hierarchy Γ s (∀¹[“x. x < !!t”] φ) :=
  BoundingHierarchy.ball (R := BoundingOperator (L := L))

@[match_pattern] abbrev bexs {Γ s n} {φ : Semiformula L ξ (n + 1)}
    {t : Semiterm L ξ (n + 1)} :
    t.Positive → Hierarchy Γ s φ → Hierarchy Γ s (∃¹[“x. x < !!t”] φ) :=
  BoundingHierarchy.bexs (R := BoundingOperator (L := L))

@[match_pattern] abbrev exs {s n} {φ : Semiformula L ξ (n + 1)} :
    Hierarchy 𝚺 (s + 1) φ → Hierarchy 𝚺 (s + 1) (∃¹ φ) :=
  BoundingHierarchy.exs

@[match_pattern] abbrev all {s n} {φ : Semiformula L ξ (n + 1)} :
    Hierarchy 𝚷 (s + 1) φ → Hierarchy 𝚷 (s + 1) (∀¹ φ) :=
  BoundingHierarchy.all

@[match_pattern] abbrev sigma {s n} {φ : Semiformula L ξ (n + 1)} :
    Hierarchy 𝚷 s φ → Hierarchy 𝚺 (s + 1) (∃¹ φ) :=
  BoundingHierarchy.sigma

@[match_pattern] abbrev pi {s n} {φ : Semiformula L ξ (n + 1)} :
    Hierarchy 𝚺 s φ → Hierarchy 𝚷 (s + 1) (∀¹ φ) :=
  BoundingHierarchy.pi

@[match_pattern] abbrev dummy_sigma {s n} {φ : Semiformula L ξ (n + 1)} :
    Hierarchy 𝚷 (s + 1) φ → Hierarchy 𝚺 (s + 1 + 1) (∀¹ φ) :=
  BoundingHierarchy.dummy_sigma

@[match_pattern] abbrev dummy_pi {s n} {φ : Semiformula L ξ (n + 1)} :
    Hierarchy 𝚺 (s + 1) φ → Hierarchy 𝚷 (s + 1 + 1) (∃¹ φ) :=
  BoundingHierarchy.dummy_pi

end Constructors

@[simp] lemma and_iff {φ ψ : Semiformula L ξ n} :
    Hierarchy Γ s (φ ⋏ ψ) ↔ Hierarchy Γ s φ ∧ Hierarchy Γ s ψ :=
  BoundingHierarchy.and_iff (R := BoundingOperator (L := L))

@[simp] lemma or_iff {φ ψ : Semiformula L ξ n} :
    Hierarchy Γ s (φ ⋎ ψ) ↔ Hierarchy Γ s φ ∧ Hierarchy Γ s ψ :=
  BoundingHierarchy.or_iff (R := BoundingOperator (L := L))

@[simp] lemma conj_iff {φ : Fin m → Semiformula L ξ n} :
    Hierarchy Γ s (Matrix.conj φ) ↔ ∀ i, Hierarchy Γ s (φ i) :=
  BoundingHierarchy.conj_iff (R := BoundingOperator (L := L))

lemma zero_eq_alt {φ : Semiformula L ξ n} :
    Hierarchy Γ 0 φ → Hierarchy Γ.alt 0 φ :=
  BoundingHierarchy.zero_eq_alt (R := BoundingOperator (L := L))

lemma pi_zero_iff_sigma_zero {φ : Semiformula L ξ n} :
    Hierarchy 𝚷 0 φ ↔ Hierarchy 𝚺 0 φ :=
  BoundingHierarchy.pi_zero_iff_sigma_zero (R := BoundingOperator (L := L))

lemma zero_iff {Γ Γ'} {φ : Semiformula L ξ n} :
    Hierarchy Γ 0 φ ↔ Hierarchy Γ' 0 φ :=
  BoundingHierarchy.zero_iff (R := BoundingOperator (L := L))

lemma zero_iff_delta_zero {Γ} {φ : Semiformula L ξ n} :
    Hierarchy Γ 0 φ ↔ DeltaZero φ := by
  simpa [DeltaZero, BoundingHierarchy.DeltaZero] using
    (BoundingHierarchy.zero_iff_delta_zero
      (R := BoundingOperator (L := L)) (Γ := Γ) (φ := φ))

@[simp] lemma alt_zero_iff_zero {φ : Semiformula L ξ n} :
    Hierarchy Γ.alt 0 φ ↔ Hierarchy Γ 0 φ :=
  BoundingHierarchy.alt_zero_iff_zero (R := BoundingOperator (L := L))

lemma accum {Γ} {s : ℕ} {φ : Semiformula L ξ n} :
    Hierarchy Γ s φ → ∀ Γ', Hierarchy Γ' (s + 1) φ :=
  BoundingHierarchy.accum (R := BoundingOperator (L := L))

lemma strict_mono {Γ s} {φ : Semiformula L ξ n}
    (hp : Hierarchy Γ s φ) (Γ') {s'} (h : s < s') : Hierarchy Γ' s' φ :=
  BoundingHierarchy.strict_mono (R := BoundingOperator (L := L)) hp Γ' h

lemma mono {Γ} {s s' : ℕ} {φ : Semiformula L ξ n}
    (hp : Hierarchy Γ s φ) (h : s ≤ s') : Hierarchy Γ s' φ :=
  BoundingHierarchy.mono (R := BoundingOperator (L := L)) hp h

lemma of_zero {b b'} {s : ℕ} {φ : Semiformula L ξ n}
    (hp : Hierarchy b 0 φ) : Hierarchy b' s φ :=
  BoundingHierarchy.of_zero (R := BoundingOperator (L := L)) hp

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

lemma neg {φ : Semiformula L ξ n} :
    Hierarchy Γ s φ → Hierarchy Γ.alt s (∼φ) :=
  BoundingHierarchy.neg (R := BoundingOperator (L := L))

@[simp] lemma neg_iff {φ : Semiformula L ξ n} :
    Hierarchy Γ s (∼φ) ↔ Hierarchy Γ.alt s φ :=
  BoundingHierarchy.neg_iff (R := BoundingOperator (L := L))

@[simp] lemma imp_iff {φ ψ : Semiformula L ξ n} :
    Hierarchy Γ s (φ 🡒 ψ) ↔ Hierarchy Γ.alt s φ ∧ Hierarchy Γ s ψ :=
  BoundingHierarchy.imp_iff (R := BoundingOperator (L := L))

@[simp] lemma ball_iff {Γ s n} {φ : Semiformula L ξ (n + 1)} {t : Semiterm L ξ (n + 1)}
    (ht : t.Positive) :
    Hierarchy Γ s (∀¹[“x. x < !!t”] φ) ↔ Hierarchy Γ s φ :=
  BoundingHierarchy.ball_iff (R := BoundingOperator (L := L)) ht

@[simp] lemma bexs_iff {Γ s n} {φ : Semiformula L ξ (n + 1)} {t : Semiterm L ξ (n + 1)}
    (ht : t.Positive) :
    Hierarchy Γ s (∃¹[“x. x < !!t”] φ) ↔ Hierarchy Γ s φ :=
  BoundingHierarchy.bexs_iff (R := BoundingOperator (L := L)) ht

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

lemma pi_of_pi_all {φ : Semiformula L ξ (n + 1)} :
    Hierarchy 𝚷 s (∀¹ φ) → Hierarchy 𝚷 s φ :=
  BoundingHierarchy.pi_of_pi_all (R := BoundingOperator (L := L))

@[simp] lemma all_iff {φ : Semiformula L ξ (n + 1)} :
    Hierarchy 𝚷 (s + 1) (∀¹ φ) ↔ Hierarchy 𝚷 (s + 1) φ :=
  BoundingHierarchy.all_iff (R := BoundingOperator (L := L))

@[simp] lemma allItr_iff {φ : Semiformula L ξ (n + k)} :
    Hierarchy 𝚷 (s + 1) (∀¹^[k] φ) ↔ Hierarchy 𝚷 (s + 1) φ :=
  BoundingHierarchy.allItr_iff (R := BoundingOperator (L := L))

lemma sigma_of_sigma_ex {φ : Semiformula L ξ (n + 1)} :
    Hierarchy 𝚺 s (∃¹ φ) → Hierarchy 𝚺 s φ :=
  BoundingHierarchy.sigma_of_sigma_ex (R := BoundingOperator (L := L))

@[simp] lemma sigma_iff {φ : Semiformula L ξ (n + 1)} :
    Hierarchy 𝚺 (s + 1) (∃¹ φ) ↔ Hierarchy 𝚺 (s + 1) φ :=
  BoundingHierarchy.sigma_iff (R := BoundingOperator (L := L))

@[simp] lemma exsItr_iff {φ : Semiformula L ξ (n + k)} :
    Hierarchy 𝚺 (s + 1) (∃¹^[k] φ) ↔ Hierarchy 𝚺 (s + 1) φ :=
  BoundingHierarchy.exsItr_iff (R := BoundingOperator (L := L))

lemma rew (ω : Rew L ξ₁ n₁ ξ₂ n₂) {φ : Semiformula L ξ₁ n₁} :
    Hierarchy Γ s φ → Hierarchy Γ s (ω ▹ φ) :=
  BoundingHierarchy.rew (R := BoundingOperator (L := L)) ω

@[simp] lemma rew_iff {ω : Rew L ξ₁ n₁ ξ₂ n₂} {φ : Semiformula L ξ₁ n₁} :
    Hierarchy Γ s (ω ▹ φ) ↔ Hierarchy Γ s φ :=
  BoundingHierarchy.rew_iff (R := BoundingOperator (L := L))

lemma exsClosure : {n : ℕ} → {φ : Semiformula L ξ n} →
    Hierarchy 𝚺 (s + 1) φ → Hierarchy 𝚺 (s + 1) (exsClosure φ) :=
  BoundingHierarchy.exsClosure (R := BoundingOperator (L := L))

lemma of_open {φ : Semiformula L ξ n} : φ.Open → Hierarchy Γ s φ :=
  BoundingHierarchy.of_open (R := BoundingOperator (L := L))

lemma iff_iff {φ ψ : Semiformula L ξ n} :
    Hierarchy b s (φ 🡘 ψ) ↔
      (Hierarchy b s φ ∧ Hierarchy b.alt s φ ∧
        Hierarchy b s ψ ∧ Hierarchy b.alt s ψ) :=
  BoundingHierarchy.iff_iff (R := BoundingOperator (L := L))

@[simp] lemma iff_iff₀ {φ ψ : Semiformula L ξ n} :
    Hierarchy b 0 (φ 🡘 ψ) ↔ Hierarchy b 0 φ ∧ Hierarchy b 0 ψ :=
  BoundingHierarchy.iff_iff₀ (R := BoundingOperator (L := L))

@[simp] lemma matrix_conj_iff {b s n} {φ : Fin m → Semiformula L ξ n} :
    Hierarchy b s (Matrix.conj fun j ↦ φ j) ↔ ∀ j, Hierarchy b s (φ j) :=
  BoundingHierarchy.matrix_conj_iff (R := BoundingOperator (L := L))

lemma remove_forall {φ : Semiformula L ξ (n + 1)} :
    Hierarchy b s (∀¹ φ) → Hierarchy b s φ :=
  BoundingHierarchy.remove_forall (R := BoundingOperator (L := L))

lemma remove_exists {φ : Semiformula L ξ (n + 1)} :
    Hierarchy b s (∃¹ φ) → Hierarchy b s φ :=
  BoundingHierarchy.remove_exists (R := BoundingOperator (L := L))

@[simp] lemma padding_iff {Γ s n} {φ : Semiformula L ξ n} :
    Hierarchy Γ s (φ.padding k) ↔ Hierarchy Γ s φ :=
  BoundingHierarchy.padding_iff (R := BoundingOperator (L := L))

@[simp] lemma list_conj₂_iff {Γ s n} {l : List (Semiformula L ξ n)} :
    Hierarchy Γ s (⋀l) ↔ ∀ φ ∈ l, Hierarchy Γ s φ :=
  BoundingHierarchy.list_conj₂_iff (R := BoundingOperator (L := L))

@[simp] lemma list_disj₂_iff {Γ s n} {l : List (Semiformula L ξ n)} :
    Hierarchy Γ s (⋁l) ↔ ∀ φ ∈ l, Hierarchy Γ s φ :=
  BoundingHierarchy.list_disj₂_iff (R := BoundingOperator (L := L))

@[simp] lemma list_conj'_iff {Γ s n} {l : List ι} {φ : ι → Semiformula L ξ n} :
    Hierarchy Γ s (l.conj' φ) ↔ ∀ i ∈ l, Hierarchy Γ s (φ i) :=
  BoundingHierarchy.list_conj'_iff (R := BoundingOperator (L := L))

@[simp] lemma list_disj'_iff {Γ s n} {l : List ι} {φ : ι → Semiformula L ξ n} :
    Hierarchy Γ s (l.disj' φ) ↔ ∀ i ∈ l, Hierarchy Γ s (φ i) :=
  BoundingHierarchy.list_disj'_iff (R := BoundingOperator (L := L))

@[simp] lemma finset_conj'_iff {Γ s n} {t : Finset ι} {φ : ι → Semiformula L ξ n} :
    Hierarchy Γ s (t.conj' φ) ↔ ∀ i ∈ t, Hierarchy Γ s (φ i) :=
  BoundingHierarchy.finset_conj'_iff (R := BoundingOperator (L := L))

@[simp] lemma finset_disj'_iff {Γ s n} {t : Finset ι} {φ : ι → Semiformula L ξ n} :
    Hierarchy Γ s (t.disj' φ) ↔ ∀ i ∈ t, Hierarchy Γ s (φ i) :=
  BoundingHierarchy.finset_disj'_iff (R := BoundingOperator (L := L))

@[simp] lemma finset_uconj_iff {Γ s n} [Fintype ι] {φ : ι → Semiformula L ξ n} :
    Hierarchy Γ s (Finset.uconj φ) ↔ ∀ i, Hierarchy Γ s (φ i) :=
  BoundingHierarchy.finset_uconj_iff (R := BoundingOperator (L := L))

@[simp] lemma finset_udisj_iff {Γ s n} [Fintype ι] {φ : ι → Semiformula L ξ n} :
    Hierarchy Γ s (Finset.udisj φ) ↔ ∀ i, Hierarchy Γ s (φ i) :=
  BoundingHierarchy.finset_udisj_iff (R := BoundingOperator (L := L))

@[simp] lemma exsItr {n k} {φ : Semiformula L ξ (n + k)} :
    Hierarchy 𝚺 (s + 1) (∃¹^[k] φ) ↔ Hierarchy 𝚺 (s + 1) φ :=
  BoundingHierarchy.exsItr (R := BoundingOperator (L := L))

@[simp] lemma allItr {n k} {φ : Semiformula L ξ (n + k)} :
    Hierarchy 𝚷 (s + 1) (∀¹^[k] φ) ↔ Hierarchy 𝚷 (s + 1) φ :=
  BoundingHierarchy.allItr (R := BoundingOperator (L := L))

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
    (hBall : ∀ n t φ, Hierarchy 𝚺 1 φ → P (n + 1) φ → P n (∀¹[“#0 < !!(Rew.bShift t)”] φ))
    (hExs : ∀ n φ, Hierarchy 𝚺 1 φ → P (n + 1) φ → P n (∃¹ φ)) (n φ) :
    Hierarchy 𝚺 1 φ → P n φ :=
  BoundingHierarchy.sigma₁_induction
    (R := BoundingOperator (L := ℒₒᵣ)) (P := P)
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
      simpa [BoundingOperator, Semiformula.Operator.lt_def] using hBall n t φ hφ hp)
    hExs
    (by
      intro n t
      simpa [BoundingOperator, Semiformula.Operator.lt_def] using hLT (n + 1) #0 (Rew.bShift t))
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
    (hBall : ∀ n t φ, Hierarchy 𝚺 1 φ → P (n + 1) φ → P n (∀¹[“#0 < !!(Rew.bShift t)”] φ))
    (hExs : ∀ n φ, Hierarchy 𝚺 1 φ → P (n + 1) φ → P n (∃¹ φ)) : P n φ :=
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
