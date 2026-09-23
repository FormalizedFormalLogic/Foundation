module

public import Foundation.FirstOrder.Syntax.Classical.Padding
public import Foundation.FirstOrder.Arithmetic.Basic.Model
public import Foundation.FirstOrder.Syntax.Classical.BoundingHierarchy

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

variable {L : Language} [L.LT]

abbrev Hierarchy : Polarity → ℕ → {n : ℕ} → Semiformula L ξ n → Prop :=
  ℬ[<, L].Hierarchy

abbrev DeltaZero (φ : Semiformula L ξ n) : Prop :=
  ℬ[<, L].Closure φ

namespace Hierarchy

abbrev rec := @Bounding.Hierarchy.rec (ℬ := ℬ[<, L])

abbrev recOn := @Bounding.Hierarchy.recOn (ℬ := ℬ[<, L])

abbrev casesOn := @Bounding.Hierarchy.casesOn (ℬ := ℬ[<, L])

abbrev below := @Bounding.Hierarchy.below (ℬ := ℬ[<, L])

abbrev brecOn := @Bounding.Hierarchy.brecOn (ℬ := ℬ[<, L])

section Constructors

universe u v

variable {L : Language.{u}} [L.LT] {ξ : Type v}

abbrev bounded (Γ s n) {φ : Semiformula L ξ n} :
    ℬ[<, L].Closure φ → Hierarchy Γ s φ :=
  Bounding.Hierarchy.bounded Γ s n

@[simp] abbrev verum (Γ s n) : Hierarchy Γ s (⊤ : Semiformula L ξ n) :=
  Bounding.Hierarchy.verum Γ s n

@[simp] abbrev falsum (Γ s n) : Hierarchy Γ s (⊥ : Semiformula L ξ n) :=
  Bounding.Hierarchy.falsum Γ s n

@[simp] abbrev rel (Γ s) {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ x) :
    Hierarchy Γ s (Semiformula.rel r v) :=
  Bounding.Hierarchy.rel Γ s r v

@[simp] abbrev nrel (Γ s) {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ x) :
    Hierarchy Γ s (Semiformula.nrel r v) :=
  Bounding.Hierarchy.nrel Γ s r v

@[match_pattern] abbrev and {Γ s n} {φ ψ : Semiformula L ξ n} :
    Hierarchy Γ s φ → Hierarchy Γ s ψ → Hierarchy Γ s (φ ⋏ ψ) :=
  Bounding.Hierarchy.and

@[match_pattern] abbrev or {Γ s n} {φ ψ : Semiformula L ξ n} :
    Hierarchy Γ s φ → Hierarchy Γ s ψ → Hierarchy Γ s (φ ⋎ ψ) :=
  Bounding.Hierarchy.or

@[match_pattern] abbrev ball {Γ s n} {φ : Semiformula L ξ (n + 1)}
    {t : Semiterm L ξ (n + 1)} :
    t.Positive → Hierarchy Γ s φ → Hierarchy Γ s (∀¹[“x. x < !!t”] φ) :=
  Bounding.Hierarchy.ball (R := Semiformula.Operator.LT.lt) (by rfl)

@[match_pattern] abbrev bexs {Γ s n} {φ : Semiformula L ξ (n + 1)}
    {t : Semiterm L ξ (n + 1)} :
    t.Positive → Hierarchy Γ s φ → Hierarchy Γ s (∃¹[“x. x < !!t”] φ) :=
  Bounding.Hierarchy.bexs (R := Semiformula.Operator.LT.lt) (by rfl)

@[match_pattern] abbrev exs {s n} {φ : Semiformula L ξ (n + 1)} :
    Hierarchy 𝚺 (s + 1) φ → Hierarchy 𝚺 (s + 1) (∃¹ φ) :=
  Bounding.Hierarchy.exs

@[match_pattern] abbrev all {s n} {φ : Semiformula L ξ (n + 1)} :
    Hierarchy 𝚷 (s + 1) φ → Hierarchy 𝚷 (s + 1) (∀¹ φ) :=
  Bounding.Hierarchy.all

@[match_pattern] abbrev sigma {s n} {φ : Semiformula L ξ (n + 1)} :
    Hierarchy 𝚷 s φ → Hierarchy 𝚺 (s + 1) (∃¹ φ) :=
  Bounding.Hierarchy.sigma

@[match_pattern] abbrev pi {s n} {φ : Semiformula L ξ (n + 1)} :
    Hierarchy 𝚺 s φ → Hierarchy 𝚷 (s + 1) (∀¹ φ) :=
  Bounding.Hierarchy.pi

@[match_pattern] abbrev dummy_sigma {s n} {φ : Semiformula L ξ (n + 1)} :
    Hierarchy 𝚷 (s + 1) φ → Hierarchy 𝚺 (s + 1 + 1) (∀¹ φ) :=
  Bounding.Hierarchy.dummy_sigma

@[match_pattern] abbrev dummy_pi {s n} {φ : Semiformula L ξ (n + 1)} :
    Hierarchy 𝚺 (s + 1) φ → Hierarchy 𝚷 (s + 1 + 1) (∃¹ φ) :=
  Bounding.Hierarchy.dummy_pi

end Constructors

@[simp] lemma and_iff {φ ψ : Semiformula L ξ n} :
    Hierarchy Γ s (φ ⋏ ψ) ↔ Hierarchy Γ s φ ∧ Hierarchy Γ s ψ :=
  Bounding.Hierarchy.and_iff

@[simp] lemma or_iff {φ ψ : Semiformula L ξ n} :
    Hierarchy Γ s (φ ⋎ ψ) ↔ Hierarchy Γ s φ ∧ Hierarchy Γ s ψ :=
  Bounding.Hierarchy.or_iff

@[simp] lemma conj_iff {φ : Fin m → Semiformula L ξ n} :
    Hierarchy Γ s (Matrix.conj φ) ↔ ∀ i, Hierarchy Γ s (φ i) :=
  Bounding.Hierarchy.conj_iff

lemma zero_eq_alt {φ : Semiformula L ξ n} :
    Hierarchy Γ 0 φ → Hierarchy Γ.alt 0 φ :=
  Bounding.Hierarchy.zero_eq_alt

lemma pi_zero_iff_sigma_zero {φ : Semiformula L ξ n} :
    Hierarchy 𝚷 0 φ ↔ Hierarchy 𝚺 0 φ :=
  Bounding.Hierarchy.pi_zero_iff_sigma_zero

lemma zero_iff {Γ Γ'} {φ : Semiformula L ξ n} :
    Hierarchy Γ 0 φ ↔ Hierarchy Γ' 0 φ :=
  Bounding.Hierarchy.zero_iff

lemma zero_iff_delta_zero {Γ} {φ : Semiformula L ξ n} :
    Hierarchy Γ 0 φ ↔ DeltaZero φ :=
  Bounding.Hierarchy.zero_iff_bounded

@[simp] lemma alt_zero_iff_zero {φ : Semiformula L ξ n} :
    Hierarchy Γ.alt 0 φ ↔ Hierarchy Γ 0 φ :=
  Bounding.Hierarchy.alt_zero_iff_zero

lemma accum {Γ} {s : ℕ} {φ : Semiformula L ξ n} :
    Hierarchy Γ s φ → ∀ Γ', Hierarchy Γ' (s + 1) φ :=
  Bounding.Hierarchy.accum

lemma strict_mono {Γ s} {φ : Semiformula L ξ n}
    (hp : Hierarchy Γ s φ) (Γ') {s'} (h : s < s') : Hierarchy Γ' s' φ :=
  Bounding.Hierarchy.strict_mono hp Γ' h

lemma mono {Γ} {s s' : ℕ} {φ : Semiformula L ξ n}
    (hp : Hierarchy Γ s φ) (h : s ≤ s') : Hierarchy Γ s' φ :=
  Bounding.Hierarchy.mono hp h

lemma of_zero {b b'} {s : ℕ} {φ : Semiformula L ξ n}
    (hp : Hierarchy b 0 φ) : Hierarchy b' s φ :=
  Bounding.Hierarchy.of_zero hp

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
  Bounding.Hierarchy.neg

@[simp] lemma neg_iff {φ : Semiformula L ξ n} :
    Hierarchy Γ s (∼φ) ↔ Hierarchy Γ.alt s φ :=
  Bounding.Hierarchy.neg_iff

@[simp] lemma imp_iff {φ ψ : Semiformula L ξ n} :
    Hierarchy Γ s (φ 🡒 ψ) ↔ Hierarchy Γ.alt s φ ∧ Hierarchy Γ s ψ :=
  Bounding.Hierarchy.imp_iff

@[simp] lemma ball_iff {Γ s n} {φ : Semiformula L ξ (n + 1)} {t : Semiterm L ξ (n + 1)}
    (ht : t.Positive) :
    Hierarchy Γ s (∀¹[“x. x < !!t”] φ) ↔ Hierarchy Γ s φ :=
  Bounding.Hierarchy.ball_iff (R := Semiformula.Operator.LT.lt) (by rfl) ht

@[simp] lemma bexs_iff {Γ s n} {φ : Semiformula L ξ (n + 1)} {t : Semiterm L ξ (n + 1)}
    (ht : t.Positive) :
    Hierarchy Γ s (∃¹[“x. x < !!t”] φ) ↔ Hierarchy Γ s φ :=
  Bounding.Hierarchy.bexs_iff (R := Semiformula.Operator.LT.lt) (by rfl) ht

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
  Bounding.Hierarchy.pi_of_pi_all

@[simp] lemma all_iff {φ : Semiformula L ξ (n + 1)} :
    Hierarchy 𝚷 (s + 1) (∀¹ φ) ↔ Hierarchy 𝚷 (s + 1) φ :=
  Bounding.Hierarchy.all_iff

@[simp] lemma allItr_iff {φ : Semiformula L ξ (n + k)} :
    Hierarchy 𝚷 (s + 1) (∀¹^[k] φ) ↔ Hierarchy 𝚷 (s + 1) φ :=
  Bounding.Hierarchy.allItr_iff

lemma sigma_of_sigma_ex {φ : Semiformula L ξ (n + 1)} :
    Hierarchy 𝚺 s (∃¹ φ) → Hierarchy 𝚺 s φ :=
  Bounding.Hierarchy.sigma_of_sigma_ex

@[simp] lemma sigma_iff {φ : Semiformula L ξ (n + 1)} :
    Hierarchy 𝚺 (s + 1) (∃¹ φ) ↔ Hierarchy 𝚺 (s + 1) φ :=
  Bounding.Hierarchy.sigma_iff

@[simp] lemma exsItr_iff {φ : Semiformula L ξ (n + k)} :
    Hierarchy 𝚺 (s + 1) (∃¹^[k] φ) ↔ Hierarchy 𝚺 (s + 1) φ :=
  Bounding.Hierarchy.exsItr_iff

lemma rew (ω : Rew L ξ₁ n₁ ξ₂ n₂) {φ : Semiformula L ξ₁ n₁} :
    Hierarchy Γ s φ → Hierarchy Γ s (ω ▹ φ) :=
  Bounding.Hierarchy.rew ω

@[simp] lemma rew_iff {ω : Rew L ξ₁ n₁ ξ₂ n₂} {φ : Semiformula L ξ₁ n₁} :
    Hierarchy Γ s (ω ▹ φ) ↔ Hierarchy Γ s φ :=
  Bounding.Hierarchy.rew_iff

lemma exsClosure : {n : ℕ} → {φ : Semiformula L ξ n} →
    Hierarchy 𝚺 (s + 1) φ → Hierarchy 𝚺 (s + 1) (exsClosure φ) :=
  Bounding.Hierarchy.exsClosure

lemma of_open {φ : Semiformula L ξ n} : φ.Open → Hierarchy Γ s φ :=
  Bounding.Hierarchy.of_open

lemma zero_induction {Γ} {P : (n : ℕ) → Semiformula L ξ n → Prop}
    (hVerum : ∀ n, P n ⊤)
    (hFalsum : ∀ n, P n ⊥)
    (hRel : ∀ n {k} (r : L.Rel k) v, P n (Semiformula.rel r v))
    (hNRel : ∀ n {k} (r : L.Rel k) v, P n (Semiformula.nrel r v))
    (hAnd : ∀ n φ ψ, Hierarchy Γ 0 φ → Hierarchy Γ 0 ψ → P n φ → P n ψ → P n (φ ⋏ ψ))
    (hOr : ∀ n φ ψ, Hierarchy Γ 0 φ → Hierarchy Γ 0 ψ → P n φ → P n ψ → P n (φ ⋎ ψ))
    (hBall : ∀ n t φ, Hierarchy Γ 0 φ → P (n + 1) φ → P n (∀¹[“#0 < !!(Rew.bShift t)”] φ))
    (hBexs : ∀ n t φ, Hierarchy Γ 0 φ → P (n + 1) φ → P n (∃¹[“#0 < !!(Rew.bShift t)”] φ))
    (n φ) : Hierarchy Γ 0 φ → P n φ := by
  intro h;
  replace h := zero_iff_delta_zero.mp h;
  induction h with
  | verum n => exact hVerum n;
  | falsum n => exact hFalsum n;
  | rel r v => exact hRel _ r v;
  | nrel r v => exact hNRel _ r v;
  | and hp hq ihp ihq => exact hAnd _ _ _ (bounded _ _ _ hp) (bounded _ _ _ hq) ihp ihq;
  | or hp hq ihp ihq => exact hOr _ _ _ (bounded _ _ _ hp) (bounded _ _ _ hq) ihp ihq;
  | ball hR ht hp ih =>
    obtain rfl := Set.mem_singleton_iff.mp hR
    obtain ⟨t, rfl⟩ := Rew.positive_iff.mp ht;
    exact hBall _ t _ (bounded _ _ _ hp) ih;
  | bexs hR ht hp ih =>
    obtain rfl := Set.mem_singleton_iff.mp hR
    obtain ⟨t, rfl⟩ := Rew.positive_iff.mp ht;
    exact hBexs _ t _ (bounded _ _ _ hp) ih;

lemma sigma_succ_induction {s : ℕ} {P : (n : ℕ) → Semiformula L ξ n → Prop}
    (hPi : ∀ n φ, Hierarchy 𝚷 s φ → P n φ)
    (hAnd : ∀ n φ ψ, Hierarchy 𝚺 (s + 1) φ → Hierarchy 𝚺 (s + 1) ψ → P n φ → P n ψ → P n (φ ⋏ ψ))
    (hOr : ∀ n φ ψ, Hierarchy 𝚺 (s + 1) φ → Hierarchy 𝚺 (s + 1) ψ → P n φ → P n ψ → P n (φ ⋎ ψ))
    (hBall : ∀ n t φ, Hierarchy 𝚺 (s + 1) φ → P (n + 1) φ → P n (∀¹[“#0 < !!(Rew.bShift t)”] φ))
    (hBexs : ∀ n t φ, Hierarchy 𝚺 (s + 1) φ → P (n + 1) φ → P n (∃¹[“#0 < !!(Rew.bShift t)”] φ))
    (hExs : ∀ n φ, Hierarchy 𝚺 (s + 1) φ → P (n + 1) φ → P n (∃¹ φ))
    (n φ) : Hierarchy 𝚺 (s + 1) φ → P n φ := by
  generalize hΓ : (𝚺 : Polarity) = Γ;
  generalize hs : s + 1 = S;
  intro h;
  induction h with
  | bounded _ _ _ h => exact hPi _ _ (bounded _ _ _ h);
  | ball hR pos hp ih =>
    obtain rfl := Set.mem_singleton_iff.mp hR
    rcases hΓ with rfl;
    rcases hs with rfl;
    rcases Rew.positive_iff.mp pos with ⟨t, rfl⟩;
    exact hBall _ t _ hp (ih rfl rfl);
  | bexs hR pos hp ih =>
    obtain rfl := Set.mem_singleton_iff.mp hR
    rcases hΓ with rfl;
    rcases hs with rfl;
    rcases Rew.positive_iff.mp pos with ⟨t, rfl⟩;
    exact hBexs _ t _ hp (ih rfl rfl);
  | sigma hp _ =>
    injection hs with hs;
    subst hs;
    exact hExs _ _ (hp.accum _) (hPi _ _ hp);
  | dummy_sigma hp _ =>
    injection hs with hs;
    subst hs;
    exact hPi _ _ hp.all;
  | and | or | exs => grind;
  | all | pi | dummy_pi => simp at hΓ;

lemma iff_iff {φ ψ : Semiformula L ξ n} :
    Hierarchy b s (φ 🡘 ψ) ↔
      (Hierarchy b s φ ∧ Hierarchy b.alt s φ ∧
        Hierarchy b s ψ ∧ Hierarchy b.alt s ψ) :=
  Bounding.Hierarchy.iff_iff

@[simp] lemma iff_iff₀ {φ ψ : Semiformula L ξ n} :
    Hierarchy b 0 (φ 🡘 ψ) ↔ Hierarchy b 0 φ ∧ Hierarchy b 0 ψ :=
  Bounding.Hierarchy.iff_iff₀

@[simp] lemma matrix_conj_iff {b s n} {φ : Fin m → Semiformula L ξ n} :
    Hierarchy b s (Matrix.conj fun j ↦ φ j) ↔ ∀ j, Hierarchy b s (φ j) :=
  Bounding.Hierarchy.conj_iff

lemma remove_forall {φ : Semiformula L ξ (n + 1)} :
    Hierarchy b s (∀¹ φ) → Hierarchy b s φ :=
  Bounding.Hierarchy.remove_forall

lemma remove_exists {φ : Semiformula L ξ (n + 1)} :
    Hierarchy b s (∃¹ φ) → Hierarchy b s φ :=
  Bounding.Hierarchy.remove_exists

@[simp] lemma padding_iff {Γ s n} {φ : Semiformula L ξ n} :
    Hierarchy Γ s (φ.padding k) ↔ Hierarchy Γ s φ :=
  Bounding.Hierarchy.padding_iff

@[simp] lemma list_conj₂_iff {Γ s n} {l : List (Semiformula L ξ n)} :
    Hierarchy Γ s (⋀l) ↔ ∀ φ ∈ l, Hierarchy Γ s φ :=
  Bounding.Hierarchy.list_conj₂_iff

@[simp] lemma list_disj₂_iff {Γ s n} {l : List (Semiformula L ξ n)} :
    Hierarchy Γ s (⋁l) ↔ ∀ φ ∈ l, Hierarchy Γ s φ :=
  Bounding.Hierarchy.list_disj₂_iff

@[simp] lemma list_conj'_iff {Γ s n} {l : List ι} {φ : ι → Semiformula L ξ n} :
    Hierarchy Γ s (l.conj' φ) ↔ ∀ i ∈ l, Hierarchy Γ s (φ i) :=
  Bounding.Hierarchy.list_conj'_iff (ℬ := ℬ[<, L])

@[simp] lemma list_disj'_iff {Γ s n} {l : List ι} {φ : ι → Semiformula L ξ n} :
    Hierarchy Γ s (l.disj' φ) ↔ ∀ i ∈ l, Hierarchy Γ s (φ i) :=
  Bounding.Hierarchy.list_disj'_iff (ℬ := ℬ[<, L])

@[simp] lemma finset_conj'_iff {Γ s n} {t : Finset ι} {φ : ι → Semiformula L ξ n} :
    Hierarchy Γ s (t.conj' φ) ↔ ∀ i ∈ t, Hierarchy Γ s (φ i) :=
  Bounding.Hierarchy.finset_conj'_iff (ℬ := ℬ[<, L])

@[simp] lemma finset_disj'_iff {Γ s n} {t : Finset ι} {φ : ι → Semiformula L ξ n} :
    Hierarchy Γ s (t.disj' φ) ↔ ∀ i ∈ t, Hierarchy Γ s (φ i) :=
  Bounding.Hierarchy.finset_disj'_iff (ℬ := ℬ[<, L])

@[simp] lemma finset_uconj_iff {Γ s n} [Fintype ι] {φ : ι → Semiformula L ξ n} :
    Hierarchy Γ s (Finset.uconj φ) ↔ ∀ i, Hierarchy Γ s (φ i) :=
  Bounding.Hierarchy.finset_uconj_iff

@[simp] lemma finset_udisj_iff {Γ s n} [Fintype ι] {φ : ι → Semiformula L ξ n} :
    Hierarchy Γ s (Finset.udisj φ) ↔ ∀ i, Hierarchy Γ s (φ i) :=
  Bounding.Hierarchy.finset_udisj_iff

@[simp] lemma exsItr {n k} {φ : Semiformula L ξ (n + k)} :
    Hierarchy 𝚺 (s + 1) (∃¹^[k] φ) ↔ Hierarchy 𝚺 (s + 1) φ :=
  Bounding.Hierarchy.exsItr_iff

@[simp] lemma allItr {n k} {φ : Semiformula L ξ (n + k)} :
    Hierarchy 𝚷 (s + 1) (∀¹^[k] φ) ↔ Hierarchy 𝚷 (s + 1) φ :=
  Bounding.Hierarchy.allItr_iff

end Hierarchy

namespace Hierarchy

lemma toPrenex {φ : Semiformula L ξ (n + s)}
    (h : Hierarchy (Γ.altItr s) j φ) :
    Hierarchy Γ (j + s) (φ.toPrenex Γ s) := by
  induction s generalizing n j with
  | zero => simpa using h
  | succ s ih =>
    rw [Polarity.altItr_succ] at h
    show Hierarchy Γ (j + (s + 1)) (Polarity.quantItr Γ (s + 1) φ)
    rw [Polarity.quantItr_succ', (show j + (s + 1) = (j + 1) + s by omega)]
    rcases hΓ : Γ.altItr s with _ | _
    · apply ih
      rw [hΓ] at h ⊢
      exact h.sigma
    · apply ih
      rw [hΓ] at h ⊢
      exact h.pi

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
  Bounding.Hierarchy.sigma₁_induction
    (ℬ := ℬ[<, ℒₒᵣ]) (P := P)
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
      intro R hR n t φ hφ hp
      obtain rfl := Set.mem_singleton_iff.mp hR
      simpa [Semiformula.Operator.lt_def] using hBall n t φ hφ hp)
    hExs
    (by
      intro R hR n t
      obtain rfl := Set.mem_singleton_iff.mp hR
      simpa [Semiformula.Operator.lt_def] using hLT (n + 1) #0 (Rew.bShift t))
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

end FFL
