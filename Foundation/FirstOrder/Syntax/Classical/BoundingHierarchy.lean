module

public import Foundation.FirstOrder.Syntax.Classical.Bounded
public import Foundation.FirstOrder.Syntax.Classical.Padding

@[expose] public section

namespace FFL.FirstOrder

variable {L : Language}
variable (ℬ : Bounding L)

namespace Bounding

/-! This formalization generalizes the syntactic arithmetical hierarchy using a set of operators for bounds. -/

inductive Hierarchy (ℬ : Bounding L) : Polarity → ℕ → {n : ℕ} → Semiformula L ξ n → Prop
  | bounded (Γ s n) {φ : Semiformula L ξ n} :
    Closure ℬ φ → Hierarchy ℬ Γ s φ
  | and {Γ s n} {φ ψ : Semiformula L ξ n} :
    Hierarchy ℬ Γ s φ → Hierarchy ℬ Γ s ψ → Hierarchy ℬ Γ s (φ ⋏ ψ)
  | or {Γ s n} {φ ψ : Semiformula L ξ n} :
    Hierarchy ℬ Γ s φ → Hierarchy ℬ Γ s ψ → Hierarchy ℬ Γ s (φ ⋎ ψ)
  | ball {Γ s n} {R : Semiformula.Operator L 2} {φ : Semiformula L ξ (n + 1)}
    {t : Semiterm L ξ (n + 1)} :
    R ∈ ℬ.set → t.Positive → Hierarchy ℬ Γ s φ → Hierarchy ℬ Γ s (∀¹[R.operator ![#0, t]] φ)
  | bexs {Γ s n} {R : Semiformula.Operator L 2} {φ : Semiformula L ξ (n + 1)}
    {t : Semiterm L ξ (n + 1)} :
    R ∈ ℬ.set → t.Positive → Hierarchy ℬ Γ s φ → Hierarchy ℬ Γ s (∃¹[R.operator ![#0, t]] φ)
  | exs {s n} {φ : Semiformula L ξ (n + 1)} :
    Hierarchy ℬ 𝚺 (s + 1) φ → Hierarchy ℬ 𝚺 (s + 1) (∃¹ φ)
  | all {s n} {φ : Semiformula L ξ (n + 1)} :
    Hierarchy ℬ 𝚷 (s + 1) φ → Hierarchy ℬ 𝚷 (s + 1) (∀¹ φ)
  | sigma {s n} {φ : Semiformula L ξ (n + 1)} :
    Hierarchy ℬ 𝚷 s φ → Hierarchy ℬ 𝚺 (s + 1) (∃¹ φ)
  | pi {s n} {φ : Semiformula L ξ (n + 1)} :
    Hierarchy ℬ 𝚺 s φ → Hierarchy ℬ 𝚷 (s + 1) (∀¹ φ)
  | dummy_sigma {s n} {φ : Semiformula L ξ (n + 1)} :
    Hierarchy ℬ 𝚷 (s + 1) φ → Hierarchy ℬ 𝚺 (s + 1 + 1) (∀¹ φ)
  | dummy_pi {s n} {φ : Semiformula L ξ (n + 1)} :
    Hierarchy ℬ 𝚺 (s + 1) φ → Hierarchy ℬ 𝚷 (s + 1 + 1) (∃¹ φ)

namespace Hierarchy

abbrev DeltaZero (φ : Semiformula L ξ n) : Prop := Closure ℬ φ

variable {ℬ}

@[simp] lemma verum (Γ s n) : Hierarchy ℬ Γ s (⊤ : Semiformula L ξ n) :=
  .bounded Γ s n (.verum n)

@[simp] lemma falsum (Γ s n) : Hierarchy ℬ Γ s (⊥ : Semiformula L ξ n) :=
  .bounded Γ s n (.falsum n)

@[simp] lemma rel (Γ s) {n k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) :
    Hierarchy ℬ Γ s (Semiformula.rel r v) :=
  .bounded Γ s n (.rel r v)

@[simp] lemma nrel (Γ s) {n k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) :
    Hierarchy ℬ Γ s (Semiformula.nrel r v) :=
  .bounded Γ s n (.nrel r v)

@[simp] lemma and_iff {φ ψ : Semiformula L ξ n} :
    Hierarchy ℬ Γ s (φ ⋏ ψ) ↔ Hierarchy ℬ Γ s φ ∧ Hierarchy ℬ Γ s ψ :=
  ⟨fun
    | .bounded _ _ _ h =>
      ⟨.bounded _ _ _ ((FFL.FirstOrder.Bounding.Closure.and_iff (ℬ := ℬ)).mp h).1,
        .bounded _ _ _ ((FFL.FirstOrder.Bounding.Closure.and_iff (ℬ := ℬ)).mp h).2⟩
    | .and hp hq => ⟨hp, hq⟩,
    fun ⟨hp, hq⟩ => .and hp hq⟩

@[simp] lemma or_iff {φ ψ : Semiformula L ξ n} :
    Hierarchy ℬ Γ s (φ ⋎ ψ) ↔ Hierarchy ℬ Γ s φ ∧ Hierarchy ℬ Γ s ψ :=
  ⟨fun
    | .bounded _ _ _ h =>
      ⟨.bounded _ _ _ ((FFL.FirstOrder.Bounding.Closure.or_iff (ℬ := ℬ)).mp h).1,
        .bounded _ _ _ ((FFL.FirstOrder.Bounding.Closure.or_iff (ℬ := ℬ)).mp h).2⟩
    | .or hp hq => ⟨hp, hq⟩,
    fun ⟨hp, hq⟩ => .or hp hq⟩

@[simp] lemma conj_iff {φ : Fin m → Semiformula L ξ n} :
    Hierarchy ℬ Γ s (Matrix.conj φ) ↔ ∀ i, Hierarchy ℬ Γ s (φ i) := by
  induction m <;> simp [Matrix.conj, Matrix.vecTail, Fin.forall_fin_succ, *];

lemma zero_eq_alt {φ : Semiformula L ξ n} :
    Hierarchy ℬ Γ 0 φ → Hierarchy ℬ Γ.alt 0 φ := by
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
    Hierarchy ℬ 𝚷 0 φ ↔ Hierarchy ℬ 𝚺 0 φ :=
  ⟨zero_eq_alt, zero_eq_alt⟩

lemma zero_iff {Γ Γ'} {φ : Semiformula L ξ n} :
    Hierarchy ℬ Γ 0 φ ↔ Hierarchy ℬ Γ' 0 φ := by
  rcases Γ <;> rcases Γ' <;> simp [pi_zero_iff_sigma_zero]

lemma zero_iff_bounded {Γ} {φ : Semiformula L ξ n} :
    Hierarchy ℬ Γ 0 φ ↔ Closure ℬ φ :=
  ⟨go, bounded Γ 0 n⟩
where
  go {Γ n} {φ : Semiformula L ξ n} : Hierarchy ℬ Γ 0 φ → Closure ℬ φ
    | .bounded _ _ _ h => h
    | .and hp hq => .and (go hp) (go hq)
    | .or hp hq => .or (go hp) (go hq)
    | .ball hR ht hp => .ball hR ht (go hp)
    | .bexs hR ht hp => .bexs hR ht (go hp)

lemma zero_iff_delta_zero {Γ} {φ : Semiformula L ξ n} :
    Hierarchy ℬ Γ 0 φ ↔ DeltaZero ℬ φ :=
  zero_iff_bounded

@[simp] lemma alt_zero_iff_zero {φ : Semiformula L ξ n} :
    Hierarchy ℬ Γ.alt 0 φ ↔ Hierarchy ℬ Γ 0 φ := by
  rcases Γ <;> simp [pi_zero_iff_sigma_zero]

lemma accum {Γ} {s : ℕ} {φ : Semiformula L ξ n} :
    Hierarchy ℬ Γ s φ → ∀ Γ', Hierarchy ℬ Γ' (s + 1) φ
  | bounded _ _ _ h, Γ => bounded Γ _ _ h
  |      and hp hq, _ => and (hp.accum _) (hq.accum _)
  |       or hp hq, _ => or (hp.accum _) (hq.accum _)
  | ball hR pos hp, _ => ball hR pos (hp.accum _)
  | bexs hR pos hp, _ => bexs hR pos (hp.accum _)
  |         all hp, Γ => by
    cases Γ
    · exact hp.dummy_sigma
    · exact (hp.accum 𝚷).all
  |          exs hp, Γ => by
    cases Γ
    · exact (hp.accum 𝚺).exs
    · exact hp.dummy_pi
  |       sigma hp, Γ => by
    cases Γ
    · exact ((hp.accum 𝚺).accum 𝚺).exs
    · exact (hp.accum 𝚺).dummy_pi
  |          pi hp, Γ => by
    cases Γ
    · exact (hp.accum 𝚷).dummy_sigma
    · exact ((hp.accum 𝚷).accum 𝚷).all
  | dummy_sigma hp, Γ => by
    cases Γ
    · exact (hp.accum 𝚷).dummy_sigma
    · exact ((hp.accum 𝚷).accum 𝚷).all
  |    dummy_pi hp, Γ => by
    cases Γ
    · exact ((hp.accum 𝚺).accum 𝚺).exs
    · exact (hp.accum 𝚺).dummy_pi

lemma strict_mono {Γ s} {φ : Semiformula L ξ n}
    (hp : Hierarchy ℬ Γ s φ) (Γ') {s'} (h : s < s') : Hierarchy ℬ Γ' s' φ := by
  have : ∀ d, Hierarchy ℬ Γ' (s + d + 1) φ := by
    intro d
    induction' d with d ih
    · simpa using hp.accum Γ'
    · simpa only [Nat.add_succ, add_zero] using ih.accum _
  simpa [show s + (s' - s.succ) + 1 = s' from by
    simpa [Nat.succ_add] using Nat.add_sub_of_le h] using this (s' - s.succ)

lemma mono {Γ} {s s' : ℕ} {φ : Semiformula L ξ n}
    (hp : Hierarchy ℬ Γ s φ) (h : s ≤ s') : Hierarchy ℬ Γ s' φ := by
  rcases Nat.lt_or_eq_of_le h with (lt | rfl)
  · exact hp.strict_mono Γ lt
  · assumption

lemma of_zero {Γ Γ'} {s : ℕ} {φ : Semiformula L ξ n}
    (hp : Hierarchy ℬ Γ 0 φ) : Hierarchy ℬ Γ' s φ := by
  rcases Nat.eq_or_lt_of_le (Nat.zero_le s) with (rfl | pos)
  · exact zero_iff.mp hp
  · exact strict_mono hp Γ' pos

lemma neg {φ : Semiformula L ξ n} :
    Hierarchy ℬ Γ s φ → Hierarchy ℬ Γ.alt s (∼φ) := by
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
    Hierarchy ℬ Γ s (∼φ) ↔ Hierarchy ℬ Γ.alt s φ := by
  constructor
  · intro h
    simpa using neg h
  · intro h
    simpa using neg h

@[simp] lemma imp_iff {φ ψ : Semiformula L ξ n} :
    Hierarchy ℬ Γ s (φ 🡒 ψ) ↔
      (Hierarchy ℬ Γ.alt s φ ∧ Hierarchy ℬ Γ s ψ) := by
  simp [Semiformula.imp_eq]

@[simp] lemma ball_iff {Γ s n} {R : Semiformula.Operator L 2} {φ : Semiformula L ξ (n + 1)}
    {t : Semiterm L ξ (n + 1)} (hR : R ∈ ℬ.set) (ht : t.Positive) :
    Hierarchy ℬ Γ s (∀¹[R.operator ![#0, t]] φ) ↔ Hierarchy ℬ Γ s φ := by
  constructor;
  . generalize hq : (∀¹[R.operator ![#0, t]] φ) = ψ;
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
  . intro hp;
    exact hp.ball hR ht;

@[simp] lemma bexs_iff {Γ s n} {R : Semiformula.Operator L 2} {φ : Semiformula L ξ (n + 1)}
    {t : Semiterm L ξ (n + 1)} (hR : R ∈ ℬ.set) (ht : t.Positive) :
    Hierarchy ℬ Γ s (∃¹[R.operator ![#0, t]] φ) ↔ Hierarchy ℬ Γ s φ := by
  constructor;
  . generalize hq : (∃¹[R.operator ![#0, t]] φ) = ψ;
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
  . intro hp;
    exact hp.bexs hR ht;

/-- A formalization-specific induction principle separating the preceding Π level. -/
lemma sigma_succ_induction {s : ℕ} {P : (n : ℕ) → Semiformula L ξ n → Prop}
    (hPi : ∀ n φ, Hierarchy ℬ 𝚷 s φ → P n φ)
    (hAnd : ∀ n φ ψ, Hierarchy ℬ 𝚺 (s + 1) φ → Hierarchy ℬ 𝚺 (s + 1) ψ → P n φ → P n ψ → P n (φ ⋏ ψ))
    (hOr : ∀ n φ ψ, Hierarchy ℬ 𝚺 (s + 1) φ → Hierarchy ℬ 𝚺 (s + 1) ψ → P n φ → P n ψ → P n (φ ⋎ ψ))
    (hBall : ∀ R (_hR : R ∈ ℬ.set) n t φ, Hierarchy ℬ 𝚺 (s + 1) φ → P (n + 1) φ → P n (∀¹[R.operator ![#0, Rew.bShift t]] φ))
    (hBexs : ∀ R (_hR : R ∈ ℬ.set) n t φ, Hierarchy ℬ 𝚺 (s + 1) φ → P (n + 1) φ → P n (∃¹[R.operator ![#0, Rew.bShift t]] φ))
    (hExs : ∀ n φ, Hierarchy ℬ 𝚺 (s + 1) φ → P (n + 1) φ → P n (∃¹ φ))
    (n φ) : Hierarchy ℬ 𝚺 (s + 1) φ → P n φ := by
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

/-- An auxiliary condition requiring every selected bounding operator to lie in every hierarchy level. -/
class Small (ℬ : Bounding L) (ξ : Type*) : Prop where
  operator {R : Semiformula.Operator L 2} (hR : R ∈ ℬ.set) {n : ℕ} {Γ : Polarity} {s : ℕ}
    (v : Fin 2 → Semiterm L ξ n) : Hierarchy ℬ Γ s (R.operator v)

attribute [simp] Small.operator

instance smallEq [L.Eq] (ξ : Type*) :
    Small (Bounding.ofOperator (Semiformula.Operator.Eq.eq : Semiformula.Operator L 2)) ξ where
  operator hR v := by
    rcases Set.mem_singleton_iff.mp hR with rfl
    simp [Semiformula.Operator.operator, Semiformula.Operator.Eq.sentence_eq]

instance smallLT [L.LT] (ξ : Type*) :
    Small (Bounding.ofOperator (Semiformula.Operator.LT.lt : Semiformula.Operator L 2)) ξ where
  operator hR v := by
    rcases Set.mem_singleton_iff.mp hR with rfl
    simp [Semiformula.Operator.operator, Semiformula.Operator.LT.sentence_eq]

instance smallMem [L.Mem] (ξ : Type*) :
    Small (Bounding.ofOperator (Semiformula.Operator.Mem.mem : Semiformula.Operator L 2)) ξ where
  operator hR v := by
    rcases Set.mem_singleton_iff.mp hR with rfl
    simp [Semiformula.Operator.operator, Semiformula.Operator.Mem.sentence_eq]

lemma pi_of_pi_all [Small ℬ ξ] {φ : Semiformula L ξ (n + 1)} :
    Hierarchy ℬ 𝚷 s (∀¹ φ) → Hierarchy ℬ 𝚷 s φ := by
  intro h;
  cases h;
  case bounded h =>
    cases h;
    case ball R φ t hR ht hp => exact imp_iff.mpr ⟨Small.operator φ _, .bounded _ _ _ hp⟩;
  case ball R φ t hR pt hp => exact imp_iff.mpr ⟨Small.operator φ _, hp⟩;
  case all => assumption;
  case pi hp => exact hp.accum _;

@[simp] lemma all_iff [Small ℬ ξ] {φ : Semiformula L ξ (n + 1)} :
    Hierarchy ℬ 𝚷 (s + 1) (∀¹ φ) ↔ Hierarchy ℬ 𝚷 (s + 1) φ :=
  ⟨pi_of_pi_all, all⟩

@[simp] lemma allItr_iff [Small ℬ ξ] {φ : Semiformula L ξ (n + k)} :
    Hierarchy ℬ 𝚷 (s + 1) (∀¹^[k] φ) ↔ Hierarchy ℬ 𝚷 (s + 1) φ := by
  induction k <;> simp [allItr_succ, *]

lemma sigma_of_sigma_ex [Small ℬ ξ] {φ : Semiformula L ξ (n + 1)} :
    Hierarchy ℬ 𝚺 s (∃¹ φ) → Hierarchy ℬ 𝚺 s φ := by
  intro h;
  cases h;
  case bounded h =>
    cases h;
    case bexs R φ t hR ht hp => exact and_iff.mpr ⟨Small.operator φ _, .bounded _ _ _ hp⟩;
  case bexs R φ t hR pt hp => exact and_iff.mpr ⟨Small.operator φ _, hp⟩;
  case exs => assumption;
  case sigma hp => exact hp.accum _;

@[simp] lemma sigma_iff [Small ℬ ξ] {φ : Semiformula L ξ (n + 1)} :
    Hierarchy ℬ 𝚺 (s + 1) (∃¹ φ) ↔ Hierarchy ℬ 𝚺 (s + 1) φ :=
  ⟨sigma_of_sigma_ex, exs⟩

@[simp] lemma exsItr_iff [Small ℬ ξ] {φ : Semiformula L ξ (n + k)} :
    Hierarchy ℬ 𝚺 (s + 1) (∃¹^[k] φ) ↔ Hierarchy ℬ 𝚺 (s + 1) φ := by
  induction k <;> simp [exsItr_succ, *]

lemma rew (ω : Rew L ξ₁ n₁ ξ₂ n₂) {φ : Semiformula L ξ₁ n₁} :
    Hierarchy ℬ Γ s φ → Hierarchy ℬ Γ s (ω ▹ φ) := by
  intro h;
  induction h generalizing n₂ <;> try (solve | simp [*]);
  case bounded h => exact .bounded _ _ _ (FFL.FirstOrder.Bounding.Closure.rew (ℬ := ℬ) ω h);
  case exs ih => exact (ih ω.q).exs;
  case all ih => exact (ih ω.q).all;
  case sigma ih => exact (ih ω.q).sigma;
  case pi ih => exact (ih ω.q).pi;
  case dummy_pi ih => exact (ih ω.q).dummy_pi;
  case dummy_sigma ih => exact (ih ω.q).dummy_sigma;

@[simp] lemma rew_iff [SymbolLike ℬ ξ₁ ξ₂]
    {ω : Rew L ξ₁ n₁ ξ₂ n₂} {φ : Semiformula L ξ₁ n₁} :
    Hierarchy ℬ Γ s (ω ▹ φ) ↔ Hierarchy ℬ Γ s φ := by
  constructor;
  . generalize eq : ω ▹ φ = ψ;
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
  . exact Hierarchy.rew _;

lemma exsClosure : {n : ℕ} → {φ : Semiformula L ξ n} →
    Hierarchy ℬ 𝚺 (s + 1) φ → Hierarchy ℬ 𝚺 (s + 1) (exsClosure φ)
  | 0, _, hp => hp
  | _ + 1, φ, hp => exsClosure (φ := ∃¹ φ) hp.exs

instance : LogicalConnective.AndOrClosed (Hierarchy ℬ Γ s : Semiformula L ξ k → Prop) where
  verum := verum _ _ _
  falsum := falsum _ _ _
  and := and
  or := or

instance : LogicalConnective.Closed (Hierarchy ℬ Γ 0 : Semiformula L ξ k → Prop) where
  not := by simp
  imply := by simp [Semiformula.imp_eq]; tauto

lemma of_open {φ : Semiformula L ξ n} : φ.Open → Hierarchy ℬ Γ s φ := by
  induction φ using Semiformula.rec' <;> simp_all;

lemma iff_iff {φ ψ : Semiformula L ξ n} :
    Hierarchy ℬ Γ s (φ 🡘 ψ) ↔
      (Hierarchy ℬ Γ s φ ∧ Hierarchy ℬ Γ.alt s φ ∧
        Hierarchy ℬ Γ s ψ ∧ Hierarchy ℬ Γ.alt s ψ) := by
  simp [Semiformula.iff_eq]; tauto

@[simp] lemma iff_iff₀ {φ ψ : Semiformula L ξ n} :
    Hierarchy ℬ Γ 0 (φ 🡘 ψ) ↔
      (Hierarchy ℬ Γ 0 φ ∧ Hierarchy ℬ Γ 0 ψ) := by
  simp [Semiformula.iff_eq]; tauto

lemma remove_forall [Small ℬ ξ] {φ : Semiformula L ξ (n + 1)} :
    Hierarchy ℬ Γ s (∀¹ φ) → Hierarchy ℬ Γ s φ := by
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
    Hierarchy ℬ Γ s (∃¹ φ) → Hierarchy ℬ Γ s φ := by
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

@[simp] lemma padding_iff {Γ s n} {φ : Semiformula L ξ n} :
    Hierarchy ℬ Γ s (φ.padding k) ↔ Hierarchy ℬ Γ s φ := by
  simp only [Semiformula.padding, and_iff, and_iff_left_iff_imp]
  intro h
  induction k <;> simp [List.replicate_succ, *]

@[simp] lemma list_conj₂_iff {Γ s n} {l : List (Semiformula L ξ n)} :
    Hierarchy ℬ Γ s (⋀l) ↔ ∀ φ ∈ l, Hierarchy ℬ Γ s φ := by
  match l with
  |          [] => simp
  |         [_] => simp
  | ψ :: χ :: l => simp [list_conj₂_iff (l := χ :: l)]

@[simp] lemma list_disj₂_iff {Γ s n} {l : List (Semiformula L ξ n)} :
    Hierarchy ℬ Γ s (⋁l) ↔ ∀ φ ∈ l, Hierarchy ℬ Γ s φ := by
  match l with
  |          [] => simp
  |         [_] => simp
  | ψ :: χ :: l => simp [list_disj₂_iff (l := χ :: l)]

@[simp] lemma list_conj'_iff {Γ s n} {l : List ι} {φ : ι → Semiformula L ξ n} :
    Hierarchy ℬ Γ s (l.conj' φ) ↔ ∀ i ∈ l, Hierarchy ℬ Γ s (φ i) := by
  simp [List.conj']

@[simp] lemma list_disj'_iff {Γ s n} {l : List ι} {φ : ι → Semiformula L ξ n} :
    Hierarchy ℬ Γ s (l.disj' φ) ↔ ∀ i ∈ l, Hierarchy ℬ Γ s (φ i) := by
  simp [List.disj']

@[simp] lemma finset_conj'_iff {Γ s n} {t : Finset ι} {φ : ι → Semiformula L ξ n} :
    Hierarchy ℬ Γ s (t.conj' φ) ↔ ∀ i ∈ t, Hierarchy ℬ Γ s (φ i) := by
  simp [Finset.conj']

@[simp] lemma finset_disj'_iff {Γ s n} {t : Finset ι} {φ : ι → Semiformula L ξ n} :
    Hierarchy ℬ Γ s (t.disj' φ) ↔ ∀ i ∈ t, Hierarchy ℬ Γ s (φ i) := by
  simp [Finset.disj']

@[simp] lemma finset_uconj_iff {Γ s n} [Fintype ι] {φ : ι → Semiformula L ξ n} :
    Hierarchy ℬ Γ s (Finset.uconj φ) ↔ ∀ i, Hierarchy ℬ Γ s (φ i) := by
  simp [Finset.uconj]

@[simp] lemma finset_udisj_iff {Γ s n} [Fintype ι] {φ : ι → Semiformula L ξ n} :
    Hierarchy ℬ Γ s (Finset.udisj φ) ↔ ∀ i, Hierarchy ℬ Γ s (φ i) := by
  simp [Finset.udisj]

lemma sigma₁_induction [Small ℬ ξ]
    {P : (n : ℕ) → Semiformula L ξ n → Prop}
    (hVerum : ∀ n, P n ⊤)
    (hFalsum : ∀ n, P n ⊥)
    (hRel : ∀ n k (r : L.Rel k) (v : Fin k → Semiterm L ξ n), P n (.rel r v))
    (hNRel : ∀ n k (r : L.Rel k) (v : Fin k → Semiterm L ξ n), P n (.nrel r v))
    (hAnd : ∀ n φ ψ, Hierarchy ℬ 𝚺 1 φ → Hierarchy ℬ 𝚺 1 ψ → P n φ → P n ψ → P n (φ ⋏ ψ))
    (hOr : ∀ n φ ψ, Hierarchy ℬ 𝚺 1 φ → Hierarchy ℬ 𝚺 1 ψ → P n φ → P n ψ → P n (φ ⋎ ψ))
    (hBall : ∀ R (_hR : R ∈ ℬ.set) n t φ, Hierarchy ℬ 𝚺 1 φ → P (n + 1) φ →
      P n (∀¹[R.operator ![#0, Rew.bShift t]] φ))
    (hExs : ∀ n φ, Hierarchy ℬ 𝚺 1 φ → P (n + 1) φ → P n (∃¹ φ))
    (hOperator : ∀ R (_hR : R ∈ ℬ.set) n t, P (n + 1) (R.operator ![#0, Rew.bShift t]))
    (n φ) : Hierarchy ℬ 𝚺 1 φ → P n φ
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
    have : Hierarchy ℬ 𝚺 1 φ := hp.accum _
    hExs _ _ this
      (sigma₁_induction hVerum hFalsum hRel hNRel hAnd hOr hBall hExs hOperator _ _ this)
  |                    Hierarchy.exs hp =>
    hExs _ _ hp
      (sigma₁_induction hVerum hFalsum hRel hNRel hAnd hOr hBall hExs hOperator _ _ hp)

end Hierarchy

end FFL.FirstOrder.Bounding

end
