module

public import Foundation.FirstOrder.Syntax.Classical.Bounding
public import Foundation.FirstOrder.Syntax.Classical.Padding

/-!
# Hierarchies over a bounding

`ℬ.Hierarchy Γ s` is the `s`th level of the `Γ` side of the hierarchy using `ℬ` to bound
quantifiers, and `ℬ.PrenexHierarchy Γ s` is its subclass of formulas in prenex normal form.

We may insert bounded quantifiers wherever we like in a `ℬ.Hierarchy Γ s` formula, however
this is not allowed for `ℬ.PrenexHierarchy Γ s` formulas.

## References

- [HP98]
-/

@[expose] public section

namespace FFL.FirstOrder

variable {L : Language}
variable {ξ : Type*} {n m s : ℕ} {Γ Γ' : Polarity}

namespace Bounding

inductive Hierarchy (ℬ : Bounding L) : Polarity → ℕ → {n : ℕ} → Semiformula L ξ n → Prop
  | bounded (Γ : Polarity) (s n : ℕ) {φ : Semiformula L ξ n} :
    ℬ.Closure φ → ℬ.Hierarchy Γ s φ
  | and {Γ : Polarity} {s n : ℕ} {φ ψ : Semiformula L ξ n} :
    ℬ.Hierarchy Γ s φ → ℬ.Hierarchy Γ s ψ → ℬ.Hierarchy Γ s (φ ⋏ ψ)
  | or {Γ : Polarity} {s n : ℕ} {φ ψ : Semiformula L ξ n} :
    ℬ.Hierarchy Γ s φ → ℬ.Hierarchy Γ s ψ → ℬ.Hierarchy Γ s (φ ⋎ ψ)
  | ball {Γ : Polarity} {s n : ℕ} {R : Semiformula.Operator L 2} {φ : Semiformula L ξ (n + 1)}
    {t : Semiterm L ξ (n + 1)} :
    R ∈ ℬ → t.Positive → ℬ.Hierarchy Γ s φ → ℬ.Hierarchy Γ s (∀¹[R.operator ![#0, t]] φ)
  | bexs {Γ : Polarity} {s n : ℕ} {R : Semiformula.Operator L 2} {φ : Semiformula L ξ (n + 1)}
    {t : Semiterm L ξ (n + 1)} :
    R ∈ ℬ → t.Positive → ℬ.Hierarchy Γ s φ → ℬ.Hierarchy Γ s (∃¹[R.operator ![#0, t]] φ)
  | exs {s n : ℕ} {φ : Semiformula L ξ (n + 1)} :
    ℬ.Hierarchy 𝚺 (s + 1) φ → ℬ.Hierarchy 𝚺 (s + 1) (∃¹ φ)
  | all {s n : ℕ} {φ : Semiformula L ξ (n + 1)} :
    ℬ.Hierarchy 𝚷 (s + 1) φ → ℬ.Hierarchy 𝚷 (s + 1) (∀¹ φ)
  | sigma {s n : ℕ} {φ : Semiformula L ξ (n + 1)} :
    ℬ.Hierarchy 𝚷 s φ → ℬ.Hierarchy 𝚺 (s + 1) (∃¹ φ)
  | pi {s n : ℕ} {φ : Semiformula L ξ (n + 1)} :
    ℬ.Hierarchy 𝚺 s φ → ℬ.Hierarchy 𝚷 (s + 1) (∀¹ φ)
  | dummy_sigma {s n : ℕ} {φ : Semiformula L ξ (n + 1)} :
    ℬ.Hierarchy 𝚷 (s + 1) φ → ℬ.Hierarchy 𝚺 (s + 1 + 1) (∀¹ φ)
  | dummy_pi {s n : ℕ} {φ : Semiformula L ξ (n + 1)} :
    ℬ.Hierarchy 𝚺 (s + 1) φ → ℬ.Hierarchy 𝚷 (s + 1 + 1) (∃¹ φ)

namespace Hierarchy

variable {ℬ : Bounding L}

@[simp] lemma verum (Γ s n) : ℬ.Hierarchy Γ s (⊤ : Semiformula L ξ n) :=
  .bounded Γ s n (.verum n)

@[simp] lemma falsum (Γ s n) : ℬ.Hierarchy Γ s (⊥ : Semiformula L ξ n) :=
  .bounded Γ s n (.falsum n)

@[simp] lemma rel (Γ s) {n k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) :
    ℬ.Hierarchy Γ s (Semiformula.rel r v) :=
  .bounded Γ s n (.rel r v)

@[simp] lemma nrel (Γ s) {n k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) :
    ℬ.Hierarchy Γ s (Semiformula.nrel r v) :=
  .bounded Γ s n (.nrel r v)

@[simp] lemma and_iff {φ ψ : Semiformula L ξ n} :
    ℬ.Hierarchy Γ s (φ ⋏ ψ) ↔ ℬ.Hierarchy Γ s φ ∧ ℬ.Hierarchy Γ s ψ :=
  ⟨fun
    | .bounded _ _ _ h =>
      ⟨.bounded _ _ _ ((FFL.FirstOrder.Bounding.Closure.and_iff (ℬ := ℬ)).mp h).1,
        .bounded _ _ _ ((FFL.FirstOrder.Bounding.Closure.and_iff (ℬ := ℬ)).mp h).2⟩
    | .and hp hq => ⟨hp, hq⟩,
    fun ⟨hp, hq⟩ => .and hp hq⟩

@[simp] lemma or_iff {φ ψ : Semiformula L ξ n} :
    ℬ.Hierarchy Γ s (φ ⋎ ψ) ↔ ℬ.Hierarchy Γ s φ ∧ ℬ.Hierarchy Γ s ψ :=
  ⟨fun
    | .bounded _ _ _ h =>
      ⟨.bounded _ _ _ ((FFL.FirstOrder.Bounding.Closure.or_iff (ℬ := ℬ)).mp h).1,
        .bounded _ _ _ ((FFL.FirstOrder.Bounding.Closure.or_iff (ℬ := ℬ)).mp h).2⟩
    | .or hp hq => ⟨hp, hq⟩,
    fun ⟨hp, hq⟩ => .or hp hq⟩

@[simp] lemma conj_iff {φ : Fin m → Semiformula L ξ n} :
    ℬ.Hierarchy Γ s (Matrix.conj φ) ↔ ∀ i, ℬ.Hierarchy Γ s (φ i) := by
  induction m <;> simp [Matrix.conj, Matrix.vecTail, Fin.forall_fin_succ, *];

lemma zero_eq_alt {φ : Semiformula L ξ n} :
    ℬ.Hierarchy Γ 0 φ → ℬ.Hierarchy Γ.alt 0 φ := by
  generalize hz : 0 = z;
  rw [eq_comm] at hz;
  intro h;
  induction h <;> try (solve | simp at hz ⊢);
  case bounded h => exact .bounded _ _ _ h;
  case and _ _ ihp ihq => exact .and (ihp hz) (ihq hz);
  case or _ _ ihp ihq => exact .or (ihp hz) (ihq hz);
  case ball hR pos _ ih => exact ball hR pos (ih hz);
  case bexs hR pos _ ih => exact bexs hR pos (ih hz);

lemma pi_zero_iff_sigma_zero {φ : Semiformula L ξ n} :
    ℬ.Hierarchy 𝚷 0 φ ↔ ℬ.Hierarchy 𝚺 0 φ :=
  ⟨zero_eq_alt, zero_eq_alt⟩

lemma zero_iff {Γ Γ'} {φ : Semiformula L ξ n} :
    ℬ.Hierarchy Γ 0 φ ↔ ℬ.Hierarchy Γ' 0 φ := by
  rcases Γ <;> rcases Γ' <;> simp [pi_zero_iff_sigma_zero]

lemma zero_iff_bounded {Γ} {φ : Semiformula L ξ n} :
    ℬ.Hierarchy Γ 0 φ ↔ ℬ.Closure φ :=
  ⟨go, bounded Γ 0 n⟩
where
  go {Γ n} {φ : Semiformula L ξ n} : ℬ.Hierarchy Γ 0 φ → ℬ.Closure φ
    | .bounded _ _ _ h => h
    | .and hp hq => .and (go hp) (go hq)
    | .or hp hq => .or (go hp) (go hq)
    | .ball hR ht hp => .ball hR ht (go hp)
    | .bexs hR ht hp => .bexs hR ht (go hp)

@[simp] lemma alt_zero_iff_zero {φ : Semiformula L ξ n} :
    ℬ.Hierarchy Γ.alt 0 φ ↔ ℬ.Hierarchy Γ 0 φ := by
  rcases Γ <;> simp [pi_zero_iff_sigma_zero]

lemma accum {Γ} {s : ℕ} :
    ∀ {n : ℕ} {φ : Semiformula L ξ n},
      ℬ.Hierarchy Γ s φ → ∀ Γ', ℬ.Hierarchy Γ' (s + 1) φ
  | _, _, bounded _ _ _ h, Γ => bounded Γ _ _ h
  | _, _,      and hp hq, _ => and (hp.accum _) (hq.accum _)
  | _, _,       or hp hq, _ => or (hp.accum _) (hq.accum _)
  | _, _, ball hR pos hp, _ => ball hR pos (hp.accum _)
  | _, _, bexs hR pos hp, _ => bexs hR pos (hp.accum _)
  | _, _,         all hp, Γ => by
    cases Γ
    · exact hp.dummy_sigma
    · exact (hp.accum 𝚷).all
  | _, _,          exs hp, Γ => by
    cases Γ
    · exact (hp.accum 𝚺).exs
    · exact hp.dummy_pi
  | _, _,       sigma hp, Γ => by
    cases Γ
    · exact ((hp.accum 𝚺).accum 𝚺).exs
    · exact (hp.accum 𝚺).dummy_pi
  | _, _,          pi hp, Γ => by
    cases Γ
    · exact (hp.accum 𝚷).dummy_sigma
    · exact ((hp.accum 𝚷).accum 𝚷).all
  | _, _, dummy_sigma hp, Γ => by
    cases Γ
    · exact (hp.accum 𝚷).dummy_sigma
    · exact ((hp.accum 𝚷).accum 𝚷).all
  | _, _,    dummy_pi hp, Γ => by
    cases Γ
    · exact ((hp.accum 𝚺).accum 𝚺).exs
    · exact (hp.accum 𝚺).dummy_pi

lemma strict_mono {Γ s} {φ : Semiformula L ξ n}
    (hp : ℬ.Hierarchy Γ s φ) (Γ') {s'} (h : s < s') : ℬ.Hierarchy Γ' s' φ := by
  have : ∀ d, ℬ.Hierarchy Γ' (s + d + 1) φ := by
    intro d
    induction d with
    | zero => simpa using hp.accum Γ'
    | succ d ih => simpa only [Nat.add_succ, add_zero] using ih.accum _
  simpa [show s + (s' - s.succ) + 1 = s' from by
    simpa [Nat.succ_add] using Nat.add_sub_of_le h] using this (s' - s.succ)

lemma mono {Γ} {s s' : ℕ} {φ : Semiformula L ξ n}
    (hp : ℬ.Hierarchy Γ s φ) (h : s ≤ s') : ℬ.Hierarchy Γ s' φ := by
  rcases Nat.lt_or_eq_of_le h with (lt | rfl)
  · exact hp.strict_mono Γ lt
  · assumption

lemma of_zero {Γ Γ'} {s : ℕ} {φ : Semiformula L ξ n}
    (hp : ℬ.Hierarchy Γ 0 φ) : ℬ.Hierarchy Γ' s φ := by
  rcases Nat.eq_or_lt_of_le (Nat.zero_le s) with (rfl | pos)
  · exact zero_iff.mp hp
  · exact strict_mono hp Γ' pos

lemma neg {φ : Semiformula L ξ n} :
    ℬ.Hierarchy Γ s φ → ℬ.Hierarchy Γ.alt s (∼φ) := by
  intro h;
  induction h <;> try (solve | simp [*]);
  case bounded h => exact .bounded _ _ _ h.neg;
  case bexs hR pos _ ih => simpa only [Semiformula.neg_bexs] using ball hR pos ih;
  case ball hR pos _ ih => simpa only [Semiformula.neg_ball] using bexs hR pos ih;
  case exs ih => exact all ih;
  case all ih => exact exs ih;
  case sigma ih => exact pi ih;
  case pi ih => exact sigma ih;
  case dummy_pi ih => exact dummy_sigma ih;
  case dummy_sigma ih => exact dummy_pi ih;

@[simp] lemma neg_iff {φ : Semiformula L ξ n} :
    ℬ.Hierarchy Γ s (∼φ) ↔ ℬ.Hierarchy Γ.alt s φ := by
  constructor
  · intro h
    simpa using neg h
  · intro h
    simpa using neg h

@[simp] lemma imp_iff {φ ψ : Semiformula L ξ n} :
    ℬ.Hierarchy Γ s (φ 🡒 ψ) ↔
      (ℬ.Hierarchy Γ.alt s φ ∧ ℬ.Hierarchy Γ s ψ) := by
  simp [Semiformula.imp_eq]

@[simp] lemma ball_iff {Γ s n} {R : Semiformula.Operator L 2} {φ : Semiformula L ξ (n + 1)}
    {t : Semiterm L ξ (n + 1)} (hR : R ∈ ℬ) (ht : t.Positive) :
    ℬ.Hierarchy Γ s (∀¹[R.operator ![#0, t]] φ) ↔ ℬ.Hierarchy Γ s φ := by
  constructor;
  · generalize hq : (∀¹[R.operator ![#0, t]] φ) = ψ;
    intro H;
    induction H <;> simp only [FFL.FirstOrder.ball, FFL.FirstOrder.bexs,
      Semiformula.all_inj, Semiformula.imp_inj, reduceCtorEq] at hq;
    case bounded h =>
      rcases hq with rfl;
      exact .bounded _ _ _ ((FFL.FirstOrder.Bounding.Closure.ball_iff (ℬ := ℬ) hR ht).mp h);
    case ball hR' φ t pt hp ih =>
      rcases hq with ⟨_, rfl⟩;
      assumption;
    case all hp ih =>
      rcases hq with rfl;
      exact (imp_iff.mp hp).2;
    case pi s _ _ hp ih =>
      rcases hq with rfl;
      exact (imp_iff.mp hp).2.accum _;
    case dummy_sigma hp _ =>
      rcases hq with rfl;
      exact (imp_iff.mp hp).2.accum _;
  · intro hp
    exact hp.ball hR ht;

@[simp] lemma bexs_iff {Γ s n} {R : Semiformula.Operator L 2} {φ : Semiformula L ξ (n + 1)}
    {t : Semiterm L ξ (n + 1)} (hR : R ∈ ℬ) (ht : t.Positive) :
    ℬ.Hierarchy Γ s (∃¹[R.operator ![#0, t]] φ) ↔ ℬ.Hierarchy Γ s φ := by
  constructor;
  · generalize hq : (∃¹[R.operator ![#0, t]] φ) = ψ;
    intro H;
    induction H <;> simp only [FFL.FirstOrder.ball, FFL.FirstOrder.bexs,
      Semiformula.exs_inj, Semiformula.and_inj, reduceCtorEq] at hq;
    case bounded h =>
      rcases hq with rfl;
      exact .bounded _ _ _ ((FFL.FirstOrder.Bounding.Closure.bexs_iff (ℬ := ℬ) hR ht).mp h);
    case bexs hR' φ t pt hp ih =>
      rcases hq with ⟨_, rfl⟩;
      assumption;
    case exs hp ih =>
      rcases hq with rfl;
      exact (and_iff.mp hp).2;
    case sigma s _ _ hp ih =>
      rcases hq with rfl;
      exact (and_iff.mp hp).2.accum _;
    case dummy_pi hp _ =>
      rcases hq with rfl;
      exact (and_iff.mp hp).2.accum _;
  · intro hp
    exact hp.bexs hR ht;

/-- A formalization-specific induction principle separating the preceding Π level. -/
lemma sigma_succ_induction {s : ℕ} {P : (n : ℕ) → Semiformula L ξ n → Prop}
    (hPi : ∀ n φ, ℬ.Hierarchy 𝚷 s φ → P n φ)
    (hAnd : ∀ n φ ψ,
      ℬ.Hierarchy 𝚺 (s + 1) φ → ℬ.Hierarchy 𝚺 (s + 1) ψ →
      P n φ → P n ψ → P n (φ ⋏ ψ))
    (hOr : ∀ n φ ψ,
      ℬ.Hierarchy 𝚺 (s + 1) φ → ℬ.Hierarchy 𝚺 (s + 1) ψ →
      P n φ → P n ψ → P n (φ ⋎ ψ))
    (hBall : ∀ R ∈ ℬ, ∀ n t φ,
      ℬ.Hierarchy 𝚺 (s + 1) φ → P (n + 1) φ →
      P n (∀¹[R.operator ![#0, Rew.bShift t]] φ))
    (hBexs : ∀ R ∈ ℬ, ∀ n t φ,
      ℬ.Hierarchy 𝚺 (s + 1) φ → P (n + 1) φ →
      P n (∃¹[R.operator ![#0, Rew.bShift t]] φ))
    (hExs : ∀ n φ, ℬ.Hierarchy 𝚺 (s + 1) φ → P (n + 1) φ → P n (∃¹ φ))
    (n φ) : ℬ.Hierarchy 𝚺 (s + 1) φ → P n φ := by
  generalize hΓ : (𝚺 : Polarity) = Γ
  generalize hs : s + 1 = S
  intro h
  induction h with
  | bounded _ _ _ h => exact hPi _ _ (bounded _ _ _ h)
  | ball hR pos hp ih =>
    rcases hΓ with rfl
    rcases hs with rfl
    rcases Rew.positive_iff.mp pos with ⟨t, rfl⟩
    exact hBall _ hR _ t _ hp (ih rfl rfl)
  | bexs hR pos hp ih =>
    rcases hΓ with rfl
    rcases hs with rfl
    rcases Rew.positive_iff.mp pos with ⟨t, rfl⟩
    exact hBexs _ hR _ t _ hp (ih rfl rfl)
  | sigma hp _ =>
    injection hs with hs
    subst hs
    exact hExs _ _ (hp.accum _) (hPi _ _ hp)
  | dummy_sigma hp _ =>
    injection hs with hs
    subst hs
    exact hPi _ _ hp.all
  | and | or | exs => grind
  | all | pi | dummy_pi => simp at hΓ

/-- An auxiliary condition requiring every selected bounding operator to lie in every
  hierarchy level. -/
class Small (ℬ : Bounding L) (ξ : Type*) : Prop where
  operator {R : Semiformula.Operator L 2} (hR : R ∈ ℬ) {n : ℕ} {Γ : Polarity} {s : ℕ}
    (v : Fin 2 → Semiterm L ξ n) : ℬ.Hierarchy Γ s (R.operator v)

attribute [simp] Small.operator

instance smallLT [L.LT] (ξ : Type*) :
    Small ℬ[<, L] ξ where
  operator {R} hR v := by
    change R ∈ ({Semiformula.Operator.LT.lt} : Set (Semiformula.Operator L 2)) at hR
    rcases Set.mem_singleton_iff.mp hR with rfl
    simp [Semiformula.Operator.operator, Semiformula.Operator.LT.sentence_eq]

instance smallMem [L.Mem] (ξ : Type*) :
    Small ℬ[∈, L] ξ where
  operator {R} hR v := by
    change R ∈ ({Semiformula.Operator.Mem.mem} : Set (Semiformula.Operator L 2)) at hR
    rcases Set.mem_singleton_iff.mp hR with rfl
    simp [Semiformula.Operator.operator, Semiformula.Operator.Mem.sentence_eq]

lemma pi_of_pi_all [Small ℬ ξ] {φ : Semiformula L ξ (n + 1)} :
    ℬ.Hierarchy 𝚷 s (∀¹ φ) → ℬ.Hierarchy 𝚷 s φ := by
  intro h;
  cases h;
  case bounded h =>
    cases h;
    case ball R φ t hR ht hp => exact imp_iff.mpr ⟨Small.operator φ _, .bounded _ _ _ hp⟩;
  case ball R φ t hR pt hp => exact imp_iff.mpr ⟨Small.operator φ _, hp⟩;
  case all => assumption;
  case pi hp => exact hp.accum _;

@[simp] lemma all_iff [Small ℬ ξ] {φ : Semiformula L ξ (n + 1)} :
    ℬ.Hierarchy 𝚷 (s + 1) (∀¹ φ) ↔ ℬ.Hierarchy 𝚷 (s + 1) φ :=
  ⟨pi_of_pi_all, all⟩

@[simp] lemma allItr_iff [Small ℬ ξ] {k : ℕ} {φ : Semiformula L ξ (n + k)} :
    ℬ.Hierarchy 𝚷 (s + 1) (∀¹^[k] φ) ↔ ℬ.Hierarchy 𝚷 (s + 1) φ := by
  induction k <;> simp [allItr_succ, *]

lemma sigma_of_sigma_ex [Small ℬ ξ] {φ : Semiformula L ξ (n + 1)} :
    ℬ.Hierarchy 𝚺 s (∃¹ φ) → ℬ.Hierarchy 𝚺 s φ := by
  intro h;
  cases h;
  case bounded h =>
    cases h;
    case bexs R φ t hR ht hp => exact and_iff.mpr ⟨Small.operator φ _, .bounded _ _ _ hp⟩;
  case bexs R φ t hR pt hp => exact and_iff.mpr ⟨Small.operator φ _, hp⟩;
  case exs => assumption;
  case sigma hp => exact hp.accum _;

@[simp] lemma sigma_iff [Small ℬ ξ] {φ : Semiformula L ξ (n + 1)} :
    ℬ.Hierarchy 𝚺 (s + 1) (∃¹ φ) ↔ ℬ.Hierarchy 𝚺 (s + 1) φ :=
  ⟨sigma_of_sigma_ex, exs⟩

@[simp] lemma equal [L.Eq] {t u : Semiterm L ξ n} :
    ℬ.Hierarchy Γ s “!!t = !!u” := by
  simp [Semiformula.Operator.operator, Matrix.fun_eq_vec_two,
    Semiformula.Operator.Eq.sentence_eq]

@[simp] lemma lt [L.LT] {t u : Semiterm L ξ n} :
    ℬ.Hierarchy Γ s “!!t < !!u” := by
  simp [Semiformula.Operator.operator, Matrix.fun_eq_vec_two,
    Semiformula.Operator.LT.sentence_eq]

@[simp] lemma le [L.Eq] [L.LT] {t u : Semiterm L ξ n} :
    ℬ.Hierarchy Γ s “!!t ≤ !!u” := by
  simp [Semiformula.Operator.operator, Matrix.fun_eq_vec_two,
    Semiformula.Operator.Eq.sentence_eq, Semiformula.Operator.LT.sentence_eq,
    Semiformula.Operator.LE.sentence_eq]

@[simp] lemma exsItr_iff [Small ℬ ξ] {k : ℕ} {φ : Semiformula L ξ (n + k)} :
    ℬ.Hierarchy 𝚺 (s + 1) (∃¹^[k] φ) ↔ ℬ.Hierarchy 𝚺 (s + 1) φ := by
  induction k <;> simp [exsItr_succ, *]

lemma rew {ξ₁ ξ₂ : Type*} {n₁ n₂ : ℕ} (ω : Rew L ξ₁ n₁ ξ₂ n₂)
    {φ : Semiformula L ξ₁ n₁} :
    ℬ.Hierarchy Γ s φ → ℬ.Hierarchy Γ s (ω ▹ φ) := by
  intro h;
  induction h generalizing n₂ <;> try (solve | simp [*]);
  case bounded h => exact .bounded _ _ _ (FFL.FirstOrder.Bounding.Closure.rew (ℬ := ℬ) ω h);
  case exs ih => exact (ih ω.q).exs;
  case all ih => exact (ih ω.q).all;
  case sigma ih => exact (ih ω.q).sigma;
  case pi ih => exact (ih ω.q).pi;
  case dummy_pi ih => exact (ih ω.q).dummy_pi;
  case dummy_sigma ih => exact (ih ω.q).dummy_sigma;

@[simp] lemma rew_iff {ξ₁ ξ₂ : Type*} {n₁ n₂ : ℕ} [SymbolLike ℬ ξ₁ ξ₂]
    {ω : Rew L ξ₁ n₁ ξ₂ n₂} {φ : Semiformula L ξ₁ n₁} :
    ℬ.Hierarchy Γ s (ω ▹ φ) ↔ ℬ.Hierarchy Γ s φ := by
  constructor;
  · generalize eq : ω ▹ φ = ψ;
    intro hq;
    induction hq generalizing φ n₁
      <;> try simp only [Semiformula.eq_ball_iff,
        Semiformula.eq_bexs_iff, Semiformula.eq_all_iff,
        Semiformula.eq_exs_iff, Semiformula.eq_and_iff, Semiformula.eq_or_iff,
        exists_and_left] at eq;
    case bounded h =>
      exact .bounded _ _ _ ((FFL.FirstOrder.Bounding.Closure.rew_iff (ℬ := ℬ)).mp (eq.symm ▸ h));
    case and ihp ihq =>
      rcases eq with ⟨φ₁, rfl, φ₂, rfl, rfl⟩;
      simpa using ⟨ihp rfl, ihq rfl⟩;
    case or ihp ihq =>
      rcases eq with ⟨φ₁, rfl, φ₂, rfl, rfl⟩;
      simpa using ⟨ihp rfl, ihq rfl⟩;
    case ball t hR pos _ ih =>
      rcases eq with ⟨χ, hχ, φ, hφ, rfl⟩;
      obtain ⟨u, rfl, hu⟩ := FFL.FirstOrder.Bounding.Closure.operator_preimage (ℬ := ℬ) hR hχ pos;
      exact Hierarchy.ball hR hu (ih hφ);
    case bexs t hR pos _ ih =>
      rcases eq with ⟨χ, hχ, φ, hφ, rfl⟩;
      obtain ⟨u, rfl, hu⟩ := FFL.FirstOrder.Bounding.Closure.operator_preimage (ℬ := ℬ) hR hχ pos;
      exact Hierarchy.bexs hR hu (ih hφ);
    case all ih => rcases eq with ⟨φ, rfl, rfl⟩; exact Hierarchy.all (ih rfl);
    case exs ih => rcases eq with ⟨φ, rfl, rfl⟩; exact Hierarchy.exs (ih rfl);
    case pi ih => rcases eq with ⟨φ, rfl, rfl⟩; exact Hierarchy.pi (ih rfl);
    case sigma ih => rcases eq with ⟨φ, rfl, rfl⟩; exact Hierarchy.sigma (ih rfl);
    case dummy_sigma ih => rcases eq with ⟨φ, rfl, rfl⟩; exact Hierarchy.dummy_sigma (ih rfl);
    case dummy_pi ih => rcases eq with ⟨φ, rfl, rfl⟩; exact Hierarchy.dummy_pi (ih rfl);
  · exact Hierarchy.rew _

lemma exsClosure : {n : ℕ} → {φ : Semiformula L ξ n} →
    ℬ.Hierarchy 𝚺 (s + 1) φ → ℬ.Hierarchy 𝚺 (s + 1) (exsClosure φ)
  | 0, _, hp => hp
  | _ + 1, φ, hp => exsClosure (φ := ∃¹ φ) hp.exs

instance {k : ℕ} : LogicalConnective.AndOrClosed (ℬ.Hierarchy Γ s : Semiformula L ξ k → Prop) where
  verum := verum _ _ _
  falsum := falsum _ _ _
  and := and
  or := or

instance {k : ℕ} : LogicalConnective.Closed (ℬ.Hierarchy Γ 0 : Semiformula L ξ k → Prop) where
  not := by simp
  imply := by simp [Semiformula.imp_eq]; tauto

lemma of_open {φ : Semiformula L ξ n} : φ.Open → ℬ.Hierarchy Γ s φ := by
  induction φ using Semiformula.rec' <;> simp_all;

lemma iff_iff {φ ψ : Semiformula L ξ n} :
    ℬ.Hierarchy Γ s (φ 🡘 ψ) ↔
      (ℬ.Hierarchy Γ s φ ∧ ℬ.Hierarchy Γ.alt s φ ∧
        ℬ.Hierarchy Γ s ψ ∧ ℬ.Hierarchy Γ.alt s ψ) := by
  simp [Semiformula.iff_eq]; tauto

@[simp] lemma iff_iff₀ {φ ψ : Semiformula L ξ n} :
    ℬ.Hierarchy Γ 0 (φ 🡘 ψ) ↔
      (ℬ.Hierarchy Γ 0 φ ∧ ℬ.Hierarchy Γ 0 ψ) := by
  simp [Semiformula.iff_eq]; tauto

lemma remove_forall [Small ℬ ξ] {φ : Semiformula L ξ (n + 1)} :
    ℬ.Hierarchy Γ s (∀¹ φ) → ℬ.Hierarchy Γ s φ := by
  intro h
  rcases h
  case bounded h =>
    cases h;
    case ball R φ t hR ht hp => exact imp_iff.mpr ⟨Small.operator φ _, .bounded _ _ _ hp⟩;
  case ball R φ t hR pt hp =>
    exact imp_iff.mpr ⟨Small.operator φ _, hp⟩
  case all => assumption
  case pi h => exact h.accum _
  case dummy_sigma h => exact h.accum _

lemma remove_exists [Small ℬ ξ] {φ : Semiformula L ξ (n + 1)} :
    ℬ.Hierarchy Γ s (∃¹ φ) → ℬ.Hierarchy Γ s φ := by
  intro h
  rcases h
  case bounded h =>
    cases h;
    case bexs R φ t hR ht hp => exact and_iff.mpr ⟨Small.operator φ _, .bounded _ _ _ hp⟩;
  case bexs R φ t hR pt hp =>
    exact and_iff.mpr ⟨Small.operator φ _, hp⟩
  case exs => assumption
  case sigma h => exact h.accum _
  case dummy_pi h => exact h.accum _

@[simp] lemma padding_iff {Γ s n k} {φ : Semiformula L ξ n} :
    ℬ.Hierarchy Γ s (φ.padding k) ↔ ℬ.Hierarchy Γ s φ := by
  simp only [Semiformula.padding, and_iff, and_iff_left_iff_imp]
  intro h
  induction k <;> simp [List.replicate_succ, *]

@[simp] lemma list_conj₂_iff {Γ s n} {l : List (Semiformula L ξ n)} :
    ℬ.Hierarchy Γ s (⋀l) ↔ ∀ φ ∈ l, ℬ.Hierarchy Γ s φ := by
  match l with
  |          [] => simp
  |         [_] => simp
  | ψ :: χ :: l => simp [list_conj₂_iff (l := χ :: l)]

@[simp] lemma list_disj₂_iff {Γ s n} {l : List (Semiformula L ξ n)} :
    ℬ.Hierarchy Γ s (⋁l) ↔ ∀ φ ∈ l, ℬ.Hierarchy Γ s φ := by
  match l with
  |          [] => simp
  |         [_] => simp
  | ψ :: χ :: l => simp [list_disj₂_iff (l := χ :: l)]

@[simp] lemma list_conj'_iff {Γ s n} {ι : Type*} {l : List ι}
    {φ : ι → Semiformula L ξ n} :
    ℬ.Hierarchy Γ s (l.conj' φ) ↔ ∀ i ∈ l, ℬ.Hierarchy Γ s (φ i) := by
  simp [List.conj']

@[simp] lemma list_disj'_iff {Γ s n} {ι : Type*} {l : List ι}
    {φ : ι → Semiformula L ξ n} :
    ℬ.Hierarchy Γ s (l.disj' φ) ↔ ∀ i ∈ l, ℬ.Hierarchy Γ s (φ i) := by
  simp [List.disj']

@[simp] lemma finset_conj'_iff {Γ s n} {ι : Type*} {t : Finset ι}
    {φ : ι → Semiformula L ξ n} :
    ℬ.Hierarchy Γ s (t.conj' φ) ↔ ∀ i ∈ t, ℬ.Hierarchy Γ s (φ i) := by
  simp [Finset.conj']

@[simp] lemma finset_disj'_iff {Γ s n} {ι : Type*} {t : Finset ι}
    {φ : ι → Semiformula L ξ n} :
    ℬ.Hierarchy Γ s (t.disj' φ) ↔ ∀ i ∈ t, ℬ.Hierarchy Γ s (φ i) := by
  simp [Finset.disj']

@[simp] lemma finset_uconj_iff {Γ s n} {ι : Type*} [Fintype ι]
    {φ : ι → Semiformula L ξ n} :
    ℬ.Hierarchy Γ s (Finset.uconj φ) ↔ ∀ i, ℬ.Hierarchy Γ s (φ i) := by
  simp [Finset.uconj]

@[simp] lemma finset_udisj_iff {Γ s n} {ι : Type*} [Fintype ι]
    {φ : ι → Semiformula L ξ n} :
    ℬ.Hierarchy Γ s (Finset.udisj φ) ↔ ∀ i, ℬ.Hierarchy Γ s (φ i) := by
  simp [Finset.udisj]

lemma sigma₁_induction [Small ℬ ξ]
    {P : (n : ℕ) → Semiformula L ξ n → Prop}
    (hVerum : ∀ n, P n ⊤)
    (hFalsum : ∀ n, P n ⊥)
    (hRel : ∀ n k (r : L.Rel k) (v : Fin k → Semiterm L ξ n), P n (.rel r v))
    (hNRel : ∀ n k (r : L.Rel k) (v : Fin k → Semiterm L ξ n), P n (.nrel r v))
    (hAnd : ∀ n φ ψ, ℬ.Hierarchy 𝚺 1 φ → ℬ.Hierarchy 𝚺 1 ψ → P n φ → P n ψ → P n (φ ⋏ ψ))
    (hOr : ∀ n φ ψ, ℬ.Hierarchy 𝚺 1 φ → ℬ.Hierarchy 𝚺 1 ψ → P n φ → P n ψ → P n (φ ⋎ ψ))
    (hBall : ∀ R (_hR : R ∈ ℬ) n t φ, ℬ.Hierarchy 𝚺 1 φ → P (n + 1) φ →
      P n (∀¹[R.operator ![#0, Rew.bShift t]] φ))
    (hExs : ∀ n φ, ℬ.Hierarchy 𝚺 1 φ → P (n + 1) φ → P n (∃¹ φ))
    (hOperator : ∀ R (_hR : R ∈ ℬ) n t, P (n + 1) (R.operator ![#0, Rew.bShift t]))
    (n φ) : ℬ.Hierarchy 𝚺 1 φ → P n φ
  | Hierarchy.bounded _ _ _ h => by
    rename_i φ₀;
    clear φ₀;
    induction h with
    | verum n => exact hVerum n;
    | falsum n => exact hFalsum n;
    | rel r v => exact hRel _ _ r v;
    | nrel r v => exact hNRel _ _ r v;
    | and hp hq ihp ihq =>
      exact hAnd _ _ _ (.bounded _ _ _ hp) (.bounded _ _ _ hq) ihp ihq;
    | or hp hq ihp ihq =>
      exact hOr _ _ _ (.bounded _ _ _ hp) (.bounded _ _ _ hq) ihp ihq;
    | ball hR ht hp ih =>
      obtain ⟨t, rfl⟩ := Rew.positive_iff.mp ht;
      exact hBall _ hR _ t _ (.bounded _ _ _ hp) ih;
    | bexs hR ht hp ih =>
      obtain ⟨t, rfl⟩ := Rew.positive_iff.mp ht;
      exact hExs _ _ (and_iff.mpr ⟨Small.operator hR _, .bounded _ _ _ hp⟩)
        (hAnd _ _ _ (Small.operator hR _) (.bounded _ _ _ hp) (hOperator _ hR _ t) ih);
  |                 Hierarchy.and hp hq =>
    hAnd _ _ _ hp hq
      (sigma₁_induction hVerum hFalsum hRel hNRel hAnd hOr hBall hExs hOperator _ _ hp)
      (sigma₁_induction hVerum hFalsum hRel hNRel hAnd hOr hBall hExs hOperator _ _ hq)
  |                  Hierarchy.or hp hq =>
    hOr _ _ _ hp hq
      (sigma₁_induction hVerum hFalsum hRel hNRel hAnd hOr hBall hExs hOperator _ _ hp)
      (sigma₁_induction hVerum hFalsum hRel hNRel hAnd hOr hBall hExs hOperator _ _ hq)
  |                Hierarchy.ball hR pt hp => by
    rcases Rew.positive_iff.mp pt with ⟨t, rfl⟩
    exact hBall _ hR _ t _ hp
      (sigma₁_induction hVerum hFalsum hRel hNRel hAnd hOr hBall hExs hOperator _ _ hp)
  |                 Hierarchy.bexs hR pt hp => by
    apply hExs
    · exact and_iff.mpr ⟨Small.operator hR _, hp⟩
    · rcases Rew.positive_iff.mp pt with ⟨t, rfl⟩
      apply hAnd _ _ _ (Small.operator hR _) hp (hOperator _ hR _ t)
        (sigma₁_induction hVerum hFalsum hRel hNRel hAnd hOr hBall hExs hOperator _ _ hp)
  |         Hierarchy.sigma (φ := φ) hp =>
    have : ℬ.Hierarchy 𝚺 1 φ := hp.accum _
    hExs _ _ this
      (sigma₁_induction hVerum hFalsum hRel hNRel hAnd hOr hBall hExs hOperator _ _ this)
  |                    Hierarchy.exs hp =>
    hExs _ _ hp
      (sigma₁_induction hVerum hFalsum hRel hNRel hAnd hOr hBall hExs hOperator _ _ hp)

lemma toPrenex {j : ℕ} {φ : Semiformula L ξ (n + s)}
    (h : ℬ.Hierarchy (Γ.altItr s) j φ) :
    ℬ.Hierarchy Γ (j + s) (φ.toPrenex Γ s) := by
  induction s generalizing n j with
  | zero => simpa using h
  | succ s ih =>
    rw [Polarity.altItr_succ] at h
    change ℬ.Hierarchy Γ (j + (s + 1)) (Polarity.quantItr Γ (s + 1) φ)
    rw [Polarity.quantItr_succ', (show j + (s + 1) = (j + 1) + s by omega)]
    rcases hΓ : Γ.altItr s with _ | _
    · apply ih
      rw [hΓ] at h ⊢
      exact h.sigma
    · apply ih
      rw [hΓ] at h ⊢
      exact h.pi

end Hierarchy

@[simp] lemma Semiformula.hierarchy {ℬ : Bounding L} (φ : ℬ.Semiformula ξ n) :
    ℬ.Hierarchy Γ s φ.val :=
  .bounded Γ s n φ.bounded

/-- A `Γ`-prenex formula of level `s` with a `ℬ`-bounded matrix. -/
structure Prenex (ℬ : Bounding L) (Γ : Polarity) (s : ℕ) (ξ : Type*) (n : ℕ) where
  matrix : ℬ.Semiformula ξ (n + s)

namespace Prenex

variable {ℬ : Bounding L} {ξ₁ ξ₂ : Type*} {n₁ n₂ : ℕ}

@[coe]
def val (φ : ℬ.Prenex Γ s ξ n) : Semiformula L ξ n := φ.matrix.val.toPrenex Γ s

instance : CoeTC (ℬ.Prenex Γ s ξ n) (Semiformula L ξ n) := ⟨val⟩

def neg (φ : ℬ.Prenex Γ s ξ n) : ℬ.Prenex Γ.alt s ξ n := ⟨⟨∼φ.matrix.val, φ.matrix.bounded.neg⟩⟩

instance : HTilde (ℬ.Prenex Γ s ξ n) (ℬ.Prenex Γ.alt s ξ n) := ⟨neg⟩

def rew (φ : ℬ.Prenex Γ s ξ₁ n₁) (ω : Rew L ξ₁ n₁ ξ₂ n₂) : ℬ.Prenex Γ s ξ₂ n₂ :=
  ⟨φ.matrix.rew (ω.qpow s)⟩

def sigma (φ : ℬ.Prenex 𝚷 s ξ (n + 1)) : ℬ.Prenex 𝚺 (s + 1) ξ n :=
  ⟨φ.matrix.rew (Rew.castLE (Nat.succ_add n s).le)⟩

def pi (φ : ℬ.Prenex 𝚺 s ξ (n + 1)) : ℬ.Prenex 𝚷 (s + 1) ξ n :=
  ⟨φ.matrix.rew (Rew.castLE (Nat.succ_add n s).le)⟩

def sigmaInv (φ : ℬ.Prenex 𝚺 (s + 1) ξ n) : ℬ.Prenex 𝚷 s ξ (n + 1) :=
  ⟨φ.matrix.rew (Rew.castLE (Nat.succ_add n s).ge)⟩

def piInv (φ : ℬ.Prenex 𝚷 (s + 1) ξ n) : ℬ.Prenex 𝚺 s ξ (n + 1) :=
  ⟨φ.matrix.rew (Rew.castLE (Nat.succ_add n s).ge)⟩

def altUp (φ : ℬ.Prenex Γ s ξ n) : ℬ.Prenex Γ.alt (s + 1) ξ n := by
  rcases Γ with _ | _;
  · exact (φ.rew Rew.bShift).pi;
  · exact (φ.rew Rew.bShift).sigma;

def ofΔ₀ (φ : ℬ.Semiformula ξ n) : (Γ : Polarity) → (s : ℕ) → ℬ.Prenex Γ s ξ n
  | Γ, 0     => ⟨φ⟩
  | Γ, s + 1 => by simpa using altUp (ofΔ₀ φ Γ.alt s)

def verum : ℬ.Prenex Γ s ξ n := ofΔ₀ ⟨⊤, .verum n⟩ Γ s

def falsum : ℬ.Prenex Γ s ξ n := ofΔ₀ ⟨⊥, .falsum n⟩ Γ s

def rel {k : ℕ} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : ℬ.Prenex Γ s ξ n :=
  ofΔ₀ ⟨.rel r v, .rel r v⟩ Γ s

def nrel {k : ℕ} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : ℬ.Prenex Γ s ξ n :=
  ofΔ₀ ⟨.nrel r v, .nrel r v⟩ Γ s

def succ : {Γ : Polarity} → {s n : ℕ} → ℬ.Prenex Γ s ξ n → ℬ.Prenex Γ (s + 1) ξ n
  | Γ, 0,     _, φ => ofΔ₀ φ.matrix Γ 1
  | 𝚺, _ + 1, _, φ => φ.sigmaInv.succ.sigma
  | 𝚷, _ + 1, _, φ => φ.piInv.succ.pi

@[simp, grind .]
lemma val_hierarchy {φ : ℬ.Prenex Γ s ξ n} : ℬ.Hierarchy Γ s φ.val := by
  simpa [val] using Hierarchy.toPrenex (Γ := Γ) (j := 0) φ.matrix.hierarchy;

@[simp, grind .]
lemma val_deltaZero {φ : ℬ.Prenex Γ 0 ξ n} : ℬ.Hierarchy 𝚺 0 φ.val := φ.matrix.hierarchy

@[simp, grind .]
lemma val_neg (φ : ℬ.Prenex Γ s ξ n) : (∼φ).val = ∼φ.val :=
  (Semiformula.neg_toPrenex ..).symm

@[simp, grind .]
lemma val_rew (φ : ℬ.Prenex Γ s ξ₁ n₁) (ω : Rew L ξ₁ n₁ ξ₂ n₂) :
    (φ.rew ω).val = ω ▹ φ.val := by
  simp [val, rew];

@[simp, grind .]
lemma val_sigma {φ : ℬ.Prenex 𝚷 s ξ (n + 1)} : φ.sigma.val = ∃¹ φ.val := by
  simp [val, sigma, Rewriting.quantItr_succ_smul_castLE];

@[simp, grind .]
lemma val_pi {φ : ℬ.Prenex 𝚺 s ξ (n + 1)} : φ.pi.val = ∀¹ φ.val := by
  simp [val, pi, Rewriting.quantItr_succ_smul_castLE];

@[simp, grind .]
lemma val_sigmaInv {φ : ℬ.Prenex 𝚺 (s + 1) ξ n} : φ.val = ∃¹ φ.sigmaInv.val := by
  unfold val sigmaInv;
  rw [Semiformula.val_rew, ← Polarity.quant_sigma, ← Polarity.alt_sigma,
    ← Rewriting.quantItr_succ_smul_castLE, ← TransitiveRewriting.comp_app];
  simp;

@[simp, grind .]
lemma val_piInv {φ : ℬ.Prenex 𝚷 (s + 1) ξ n} : φ.val = ∀¹ φ.piInv.val := by
  unfold val piInv;
  rw [Semiformula.val_rew, ← Polarity.quant_pi, ← Polarity.alt_pi,
    ← Rewriting.quantItr_succ_smul_castLE, ← TransitiveRewriting.comp_app];
  simp;

section models

variable {M : Type*} [Tarski.Structure L M] {f : ξ → M}

lemma models_sigmaInv (φ : ℬ.Prenex 𝚺 (s + 1) ξ n) (e : Fin n → M) :
    Semiformula.Eval e f φ.val ↔ ∃ x, Semiformula.Eval (x :> e) f φ.sigmaInv.val := by
  rw [val_sigmaInv, Semiformula.eval_ex];

lemma models_piInv (φ : ℬ.Prenex 𝚷 (s + 1) ξ n) (e : Fin n → M) :
    Semiformula.Eval e f φ.val ↔ ∀ x, Semiformula.Eval (x :> e) f φ.piInv.val := by
  rw [val_piInv, Semiformula.eval_all];

lemma models_sigma (φ : ℬ.Prenex 𝚷 s ξ (n + 1)) (e : Fin n → M) :
    Semiformula.Eval e f φ.sigma.val ↔ ∃ x, Semiformula.Eval (x :> e) f φ.val := by
  rw [val_sigma, Semiformula.eval_ex];

lemma models_pi (φ : ℬ.Prenex 𝚺 s ξ (n + 1)) (e : Fin n → M) :
    Semiformula.Eval e f φ.pi.val ↔ ∀ x, Semiformula.Eval (x :> e) f φ.val := by
  rw [val_pi, Semiformula.eval_all];

variable [Nonempty M]

lemma models_altUp (φ : ℬ.Prenex Γ s ξ n) (e : Fin n → M) :
    Semiformula.Eval e f φ.altUp.val ↔ Semiformula.Eval e f φ.val := by
  rcases Γ <;> simp [altUp, -val_piInv, -val_sigmaInv];

lemma models_ofΔ₀ (φ : ℬ.Semiformula ξ n) (e : Fin n → M) :
    Semiformula.Eval e f (ofΔ₀ φ Γ s).val ↔ Semiformula.Eval e f φ.val := by
  induction s generalizing Γ with
  | zero => rfl;
  | succ s ih =>
    rcases Γ with _ | _;
    · exact (models_altUp (ofΔ₀ φ 𝚷 s) e).trans ih;
    · exact (models_altUp (ofΔ₀ φ 𝚺 s) e).trans ih;

lemma models_verum (e : Fin n → M) :
    Semiformula.Eval e f (verum : ℬ.Prenex Γ s ξ n).val ↔
      Semiformula.Eval e f (⊤ : Semiformula L ξ n) :=
  models_ofΔ₀ ⟨⊤, .verum n⟩ e

lemma models_falsum (e : Fin n → M) :
    Semiformula.Eval e f (falsum : ℬ.Prenex Γ s ξ n).val ↔
      Semiformula.Eval e f (⊥ : Semiformula L ξ n) :=
  models_ofΔ₀ ⟨⊥, .falsum n⟩ e

lemma models_rel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) (e : Fin n → M) :
    Semiformula.Eval e f (rel r v : ℬ.Prenex Γ s ξ n).val ↔
      Semiformula.Eval e f (Semiformula.rel r v) :=
  models_ofΔ₀ ⟨.rel r v, .rel r v⟩ e

lemma models_nrel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) (e : Fin n → M) :
    Semiformula.Eval e f (nrel r v : ℬ.Prenex Γ s ξ n).val ↔
      Semiformula.Eval e f (Semiformula.nrel r v) :=
  models_ofΔ₀ ⟨.nrel r v, .nrel r v⟩ e

lemma models_succ (φ : ℬ.Prenex Γ s ξ n) (e : Fin n → M) :
    Semiformula.Eval e f φ.succ.val ↔ Semiformula.Eval e f φ.val := by
  induction s generalizing Γ n with
  | zero => exact models_ofΔ₀ φ.matrix e;
  | succ s ih =>
    rcases Γ with _ | _;
    · simp only [succ, models_sigma, ih, models_sigmaInv φ];
    · simp only [succ, models_pi, ih, models_piInv φ];

end models

lemma provable_iff_sigmaInv {T : Theory L} {φ : Semisentence L n} {φ' : ℬ.Prenex 𝚺 (s + 1) Empty n}
    (hφ' : T ⊢ ∀¹* (φ 🡘 φ'.val)) : T ⊢ ∀¹* (φ 🡘 ∃¹ φ'.sigmaInv.val) := φ'.val_sigmaInv ▸ hφ'

lemma provable_iff_piInv {T : Theory L} {φ : Semisentence L n} {φ' : ℬ.Prenex 𝚷 (s + 1) Empty n}
    (hφ' : T ⊢ ∀¹* (φ 🡘 φ'.val)) : T ⊢ ∀¹* (φ 🡘 ∀¹ φ'.piInv.val) := φ'.val_piInv ▸ hφ'

end Prenex

def PrenexHierarchy (ℬ : Bounding L) (Γ : Polarity) (s : ℕ) (φ : Semiformula L ξ n) : Prop :=
  ∃ ψ : ℬ.Prenex Γ s ξ n, φ = ψ.val

@[simp, grind .]
lemma Prenex.val_prenexHierarchy {ℬ : Bounding L} {φ : ℬ.Prenex Γ s ξ n} :
    ℬ.PrenexHierarchy Γ s φ.val := ⟨φ, rfl⟩

namespace PrenexHierarchy

variable {ℬ : Bounding L} {ξ₁ ξ₂ : Type*} {n₁ n₂ : ℕ}

section

variable {φ : Semiformula L ξ n}

lemma zero_iff_bounded : ℬ.PrenexHierarchy Γ 0 φ ↔ ℬ.Closure φ := by
  constructor;
  · rintro ⟨ψ, rfl⟩;
    exact ψ.matrix.bounded;
  · exact fun h ↦ ⟨⟨⟨φ, h⟩⟩, rfl⟩;

lemma zero_iff : ℬ.PrenexHierarchy Γ 0 φ ↔ ℬ.Hierarchy 𝚺 0 φ :=
  zero_iff_bounded.trans Hierarchy.zero_iff_bounded.symm

lemma sigma_succ_iff :
    ℬ.PrenexHierarchy 𝚺 (s + 1) φ ↔ ∃ ψ, ℬ.PrenexHierarchy 𝚷 s ψ ∧ φ = ∃¹ ψ := by
  constructor;
  · rintro ⟨χ, rfl⟩;
    exact ⟨_, χ.sigmaInv.val_prenexHierarchy, χ.val_sigmaInv⟩;
  · rintro ⟨_, ⟨χ, rfl⟩, rfl⟩;
    exact ⟨χ.sigma, χ.val_sigma.symm⟩;

lemma pi_succ_iff :
    ℬ.PrenexHierarchy 𝚷 (s + 1) φ ↔ ∃ ψ, ℬ.PrenexHierarchy 𝚺 s ψ ∧ φ = ∀¹ ψ := by
  constructor;
  · rintro ⟨χ, rfl⟩;
    exact ⟨_, χ.piInv.val_prenexHierarchy, χ.val_piInv⟩;
  · rintro ⟨_, ⟨χ, rfl⟩, rfl⟩;
    exact ⟨χ.pi, χ.val_pi.symm⟩;

lemma hierarchy (h : ℬ.PrenexHierarchy Γ s φ) : ℬ.Hierarchy Γ s φ := by
  obtain ⟨ψ, rfl⟩ := h;
  exact ψ.val_hierarchy;

lemma neg (h : ℬ.PrenexHierarchy Γ s φ) : ℬ.PrenexHierarchy Γ.alt s (∼φ) := by
  obtain ⟨ψ, rfl⟩ := h;
  exact ⟨∼ψ, (Prenex.val_neg ψ).symm⟩;

@[simp] lemma neg_iff : ℬ.PrenexHierarchy Γ s (∼φ) ↔ ℬ.PrenexHierarchy Γ.alt s φ :=
  ⟨fun h ↦ by simpa using h.neg, fun h ↦ by simpa using h.neg⟩

end

lemma exs {φ : Semiformula L ξ (n + 1)} (h : ℬ.PrenexHierarchy 𝚷 s φ) :
    ℬ.PrenexHierarchy 𝚺 (s + 1) (∃¹ φ) := sigma_succ_iff.mpr ⟨φ, h, rfl⟩

lemma all {φ : Semiformula L ξ (n + 1)} (h : ℬ.PrenexHierarchy 𝚺 s φ) :
    ℬ.PrenexHierarchy 𝚷 (s + 1) (∀¹ φ) := pi_succ_iff.mpr ⟨φ, h, rfl⟩

section

variable {φ : Semiformula L ξ₁ n₁}

lemma rew (ω : Rew L ξ₁ n₁ ξ₂ n₂) (h : ℬ.PrenexHierarchy Γ s φ) :
    ℬ.PrenexHierarchy Γ s (ω ▹ φ) := by
  obtain ⟨ψ, rfl⟩ := h;
  exact ⟨ψ.rew ω, (ψ.val_rew ω).symm⟩;

variable [ℬ.SymbolLike ξ₁ ξ₂]

lemma of_rew {ω : Rew L ξ₁ n₁ ξ₂ n₂} (h : ℬ.PrenexHierarchy Γ s (ω ▹ φ)) :
    ℬ.PrenexHierarchy Γ s φ := by
  induction s generalizing Γ n₁ n₂ with
  | zero => exact zero_iff_bounded.mpr (Closure.rew_iff.mp (zero_iff_bounded.mp h));
  | succ s ih =>
    rcases Γ with _ | _;
    · obtain ⟨ψ, hψ, e⟩ := sigma_succ_iff.mp h;
      obtain ⟨φ', rfl, rfl⟩ := (Semiformula.eq_exs_iff _).mp e;
      exact (ih hψ).exs;
    · obtain ⟨ψ, hψ, e⟩ := pi_succ_iff.mp h;
      obtain ⟨φ', rfl, rfl⟩ := (Semiformula.eq_all_iff _).mp e;
      exact (ih hψ).all;

@[simp] lemma rew_iff {ω : Rew L ξ₁ n₁ ξ₂ n₂} :
    ℬ.PrenexHierarchy Γ s (ω ▹ φ) ↔ ℬ.PrenexHierarchy Γ s φ := ⟨of_rew, rew ω⟩

end

section

variable {φ : Semiformula L ξ n}

lemma exists_eval_iff_of_le (h : ℬ.PrenexHierarchy Γ s φ) {s' : ℕ} (hs : s ≤ s') :
    ∃ ψ, ℬ.PrenexHierarchy Γ s' ψ ∧
      ∀ (M : Type*) [Tarski.Structure L M] [Nonempty M] (e : Fin n → M) (f : ξ → M),
        Semiformula.Eval e f φ ↔ Semiformula.Eval e f ψ := by
  induction s', hs using Nat.le_induction with
  | base => exact ⟨φ, h, fun _ _ _ _ _ ↦ Iff.rfl⟩;
  | succ s' _ ih =>
    obtain ⟨_, ⟨χ, rfl⟩, hχ⟩ := ih;
    exact ⟨χ.succ.val, χ.succ.val_prenexHierarchy,
      fun M _ _ e f ↦ (hχ M e f).trans (χ.models_succ e).symm⟩;

lemma exists_eval_iff_of_lt (h : ℬ.PrenexHierarchy Γ s φ) (Γ' : Polarity) {s' : ℕ}
    (hs : s < s') :
    ∃ ψ, ℬ.PrenexHierarchy Γ' s' ψ ∧
      ∀ (M : Type*) [Tarski.Structure L M] [Nonempty M] (e : Fin n → M) (f : ξ → M),
        Semiformula.Eval e f φ ↔ Semiformula.Eval e f ψ := by
  obtain rfl | rfl : Γ' = Γ ∨ Γ' = Γ.alt := by rcases Γ <;> rcases Γ' <;> simp;
  · exact h.exists_eval_iff_of_le hs.le;
  obtain ⟨t, rfl⟩ : ∃ t, s' = t + 1 := ⟨s' - 1, by omega⟩;
  obtain ⟨_, ⟨χ, rfl⟩, hχ⟩ := h.exists_eval_iff_of_le (Nat.le_of_lt_succ hs);
  exact ⟨χ.altUp.val, χ.altUp.val_prenexHierarchy,
    fun M _ _ e f ↦ (hχ M e f).trans (χ.models_altUp e).symm⟩;

lemma exists_eval_iff_of_deltaZero (h : ℬ.Hierarchy 𝚺 0 φ) (Γ : Polarity) (s : ℕ) :
    ∃ ψ, ℬ.PrenexHierarchy Γ s ψ ∧
      ∀ (M : Type*) [Tarski.Structure L M] [Nonempty M] (e : Fin n → M) (f : ξ → M),
        Semiformula.Eval e f φ ↔ Semiformula.Eval e f ψ := by
  have hφ : ℬ.Closure φ := Hierarchy.zero_iff_bounded.mp h;
  exact ⟨_, (Prenex.ofΔ₀ ⟨φ, hφ⟩ Γ s).val_prenexHierarchy,
    fun _ _ _ e _ ↦ (Prenex.models_ofΔ₀ ⟨φ, hφ⟩ e).symm⟩;

end

end PrenexHierarchy

end Bounding

end FFL.FirstOrder

end
