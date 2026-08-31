module

public import Foundation.FirstOrder.SetTheory.Basic.Model

@[expose] public section

namespace LO.FirstOrder.SetTheory

variable {L : Language} [L.Mem]

abbrev BoundingOperator : Semiformula.Operator L 2 :=
  (Semiformula.Operator.Mem.mem : Semiformula.Operator L 2)

abbrev Hierarchy : Polarity → ℕ → {n : ℕ} → Semiformula L ξ n → Prop :=
  BoundingHierarchy (R := BoundingOperator (L := L))

def DeltaZero (φ : Semiformula L ξ n) : Prop :=
  Hierarchy 𝚺 0 φ

namespace Hierarchy

section Constructors

universe u v

variable {L : Language.{u}} [L.Mem] {ξ : Type v}

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
    t.Positive → Hierarchy Γ s φ → Hierarchy Γ s (∀¹[“x. x ∈ !!t”] φ) :=
  BoundingHierarchy.ball (R := BoundingOperator (L := L))

@[match_pattern] abbrev bexs {Γ s n} {φ : Semiformula L ξ (n + 1)}
    {t : Semiterm L ξ (n + 1)} :
    t.Positive → Hierarchy Γ s φ → Hierarchy Γ s (∃¹[“x. x ∈ !!t”] φ) :=
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

lemma of_zero {Γ Γ'} {s : ℕ} {φ : Semiformula L ξ n}
    (hp : Hierarchy Γ 0 φ) : Hierarchy Γ' s φ :=
  BoundingHierarchy.of_zero (R := BoundingOperator (L := L)) hp

section

variable {L : Language}

@[simp] lemma equal [L.Eq] [L.Mem] {t u : Semiterm L ξ n} : Hierarchy Γ s “!!t = !!u” := by
  simp [Semiformula.Operator.operator, Matrix.fun_eq_vec_two,
    Semiformula.Operator.Eq.sentence_eq]

@[simp] lemma mem [L.Mem] {t u : Semiterm L ξ n} : Hierarchy Γ s “!!t ∈ !!u” := by
  simp [Semiformula.Operator.operator, Matrix.fun_eq_vec_two,
    Semiformula.Operator.Mem.sentence_eq]

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
    Hierarchy Γ s (∀¹[“x. x ∈ !!t”] φ) ↔ Hierarchy Γ s φ :=
  BoundingHierarchy.ball_iff (R := BoundingOperator (L := L)) ht

@[simp] lemma bexs_iff {Γ s n} {φ : Semiformula L ξ (n + 1)} {t : Semiterm L ξ (n + 1)}
    (ht : t.Positive) :
    Hierarchy Γ s (∃¹[“x. x ∈ !!t”] φ) ↔ Hierarchy Γ s φ :=
  BoundingHierarchy.bexs_iff (R := BoundingOperator (L := L)) ht

@[simp] lemma ballMem_iff {Γ s n} {φ : Semiformula L ξ (n + 1)} {t : Semiterm L ξ n} :
    Hierarchy Γ s (φ.ballMem t) ↔ Hierarchy Γ s φ := by simp [Semiformula.ballMem]

@[simp] lemma bexsMem_iff {Γ s n} {φ : Semiformula L ξ (n + 1)} {t : Semiterm L ξ n} :
    Hierarchy Γ s (φ.bexsMem t) ↔ Hierarchy Γ s φ := by simp [Semiformula.bexsMem]

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
    Hierarchy Γ s (φ 🡘 ψ) ↔
      (Hierarchy Γ s φ ∧ Hierarchy Γ.alt s φ ∧
        Hierarchy Γ s ψ ∧ Hierarchy Γ.alt s ψ) :=
  BoundingHierarchy.iff_iff (R := BoundingOperator (L := L))

@[simp] lemma iff_iff₀ {φ ψ : Semiformula L ξ n} :
    Hierarchy Γ 0 (φ 🡘 ψ) ↔ Hierarchy Γ 0 φ ∧ Hierarchy Γ 0 ψ :=
  BoundingHierarchy.iff_iff₀ (R := BoundingOperator (L := L))

@[simp] lemma matrix_conj_iff {Γ s n} {φ : Fin m → Semiformula L ξ n} :
    Hierarchy Γ s (Matrix.conj fun j ↦ φ j) ↔ ∀ j, Hierarchy Γ s (φ j) :=
  BoundingHierarchy.matrix_conj_iff (R := BoundingOperator (L := L))

lemma remove_forall {φ : Semiformula L ξ (n + 1)} :
    Hierarchy Γ s (∀¹ φ) → Hierarchy Γ s φ :=
  BoundingHierarchy.remove_forall (R := BoundingOperator (L := L))

lemma remove_exists {φ : Semiformula L ξ (n + 1)} :
    Hierarchy Γ s (∃¹ φ) → Hierarchy Γ s φ :=
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
    (hBall : ∀ n t φ, Hierarchy 𝚺 1 φ → P (n + 1) φ → P n (∀¹[“#0 ∈ !!(Rew.bShift t)”] φ))
    (hExs : ∀ n φ, Hierarchy 𝚺 1 φ → P (n + 1) φ → P n (∃¹ φ)) (n φ) :
    Hierarchy 𝚺 1 φ → P n φ :=
  BoundingHierarchy.sigma₁_induction
    (R := BoundingOperator (L := ℒₛₑₜ)) (P := P)
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
      simpa [BoundingOperator, Semiformula.Operator.mem_def] using hBall n t φ hφ hp)
    hExs
    (by
      intro n t
      simpa [BoundingOperator, Semiformula.Operator.mem_def] using hMem (n + 1) #0 (Rew.bShift t))
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
    (hBall : ∀ n t φ, Hierarchy 𝚺 1 φ → P (n + 1) φ → P n (∀¹[“#0 ∈ !!(Rew.bShift t)”] φ))
    (hExs : ∀ n φ, Hierarchy 𝚺 1 φ → P (n + 1) φ → P n (∃¹ φ)) : P n φ :=
  sigma₁_induction hVerum hFalsum hEQ hNEQ hMem hNMem hAnd hOr hBall hExs n φ hp

end SetLanguage

end SetTheory

end FirstOrder

end LO
