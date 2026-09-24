module

public import Foundation.FirstOrder.Syntax.Classical.Bounded
public import Foundation.FirstOrder.Syntax.Classical.Padding

@[expose] public section

namespace FFL.FirstOrder

variable {L : Language}
variable (R : Semiformula.Operator L 2)
variable {ξ ξ₁ ξ₂ : Type*}

/-- This formalization generalizes the syntactic arithmetical hierarchy using `R` for bounds. -/
inductive BoundingHierarchy : Polarity → ℕ → {n : ℕ} → Semiformula L ξ n → Prop
  | bounded (Γ s n) {φ : Semiformula L ξ n} :
    Semiformula.Bounded R φ → BoundingHierarchy Γ s φ
  | and {Γ s n} {φ ψ : Semiformula L ξ n} :
    BoundingHierarchy Γ s φ → BoundingHierarchy Γ s ψ → BoundingHierarchy Γ s (φ ⋏ ψ)
  | or {Γ s n} {φ ψ : Semiformula L ξ n} :
    BoundingHierarchy Γ s φ → BoundingHierarchy Γ s ψ → BoundingHierarchy Γ s (φ ⋎ ψ)
  | ball {Γ s n} {φ : Semiformula L ξ (n + 1)} {t : Semiterm L ξ (n + 1)} :
    t.Positive → BoundingHierarchy Γ s φ → BoundingHierarchy Γ s (∀¹[R.operator ![#0, t]] φ)
  | bexs {Γ s n} {φ : Semiformula L ξ (n + 1)} {t : Semiterm L ξ (n + 1)} :
    t.Positive → BoundingHierarchy Γ s φ → BoundingHierarchy Γ s (∃¹[R.operator ![#0, t]] φ)
  | exs {s n} {φ : Semiformula L ξ (n + 1)} :
    BoundingHierarchy 𝚺 (s + 1) φ → BoundingHierarchy 𝚺 (s + 1) (∃¹ φ)
  | all {s n} {φ : Semiformula L ξ (n + 1)} :
    BoundingHierarchy 𝚷 (s + 1) φ → BoundingHierarchy 𝚷 (s + 1) (∀¹ φ)
  | sigma {s n} {φ : Semiformula L ξ (n + 1)} :
    BoundingHierarchy 𝚷 s φ → BoundingHierarchy 𝚺 (s + 1) (∃¹ φ)
  | pi {s n} {φ : Semiformula L ξ (n + 1)} :
    BoundingHierarchy 𝚺 s φ → BoundingHierarchy 𝚷 (s + 1) (∀¹ φ)
  | dummy_sigma {s n} {φ : Semiformula L ξ (n + 1)} :
    BoundingHierarchy 𝚷 (s + 1) φ → BoundingHierarchy 𝚺 (s + 1 + 1) (∀¹ φ)
  | dummy_pi {s n} {φ : Semiformula L ξ (n + 1)} :
    BoundingHierarchy 𝚺 (s + 1) φ → BoundingHierarchy 𝚷 (s + 1 + 1) (∃¹ φ)

namespace BoundingHierarchy

variable {n : ℕ}

abbrev DeltaZero (φ : Semiformula L ξ n) : Prop := Semiformula.Bounded R φ

variable {R} {n₁ n₂ k : ℕ} {Γ : Polarity} {s : ℕ} {ι : Type*}

@[simp] lemma verum (Γ s n) : BoundingHierarchy R Γ s (⊤ : Semiformula L ξ n) :=
  .bounded Γ s n (.verum n)

@[simp] lemma falsum (Γ s n) : BoundingHierarchy R Γ s (⊥ : Semiformula L ξ n) :=
  .bounded Γ s n (.falsum n)

@[simp] lemma rel (Γ s) {n k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) :
    BoundingHierarchy R Γ s (Semiformula.rel r v) :=
  .bounded Γ s n (.rel r v)

@[simp] lemma nrel (Γ s) {n k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) :
    BoundingHierarchy R Γ s (Semiformula.nrel r v) :=
  .bounded Γ s n (.nrel r v)

@[simp] lemma and_iff {φ ψ : Semiformula L ξ n} :
    BoundingHierarchy R Γ s (φ ⋏ ψ) ↔ BoundingHierarchy R Γ s φ ∧ BoundingHierarchy R Γ s ψ :=
  ⟨fun
    | .bounded _ _ _ h =>
      ⟨.bounded _ _ _ (Semiformula.Bounded.and_iff.mp h).1,
        .bounded _ _ _ (Semiformula.Bounded.and_iff.mp h).2⟩
    | .and hp hq => ⟨hp, hq⟩,
    fun ⟨hp, hq⟩ => .and hp hq⟩

@[simp] lemma or_iff {φ ψ : Semiformula L ξ n} :
    BoundingHierarchy R Γ s (φ ⋎ ψ) ↔ BoundingHierarchy R Γ s φ ∧ BoundingHierarchy R Γ s ψ :=
  ⟨fun
    | .bounded _ _ _ h =>
      ⟨.bounded _ _ _ (Semiformula.Bounded.or_iff.mp h).1,
        .bounded _ _ _ (Semiformula.Bounded.or_iff.mp h).2⟩
    | .or hp hq => ⟨hp, hq⟩,
    fun ⟨hp, hq⟩ => .or hp hq⟩

@[simp] lemma conj_iff {m : ℕ} {φ : Fin m → Semiformula L ξ n} :
    BoundingHierarchy R Γ s (Matrix.conj φ) ↔ ∀ i, BoundingHierarchy R Γ s (φ i) := by
  induction m <;> simp [Matrix.conj, Matrix.vecTail, Fin.forall_fin_succ, *];

lemma zero_eq_alt {φ : Semiformula L ξ n} :
    BoundingHierarchy R Γ 0 φ → BoundingHierarchy R Γ.alt 0 φ := by
  generalize hz : 0 = z;
  rw [eq_comm] at hz;
  intro h;
  induction h <;> try (solve | simp at hz ⊢);
  case bounded h => exact .bounded _ _ _ h;
  case and _ _ ihp ihq => exact .and (ihp hz) (ihq hz);
  case or _ _ ihp ihq => exact .or (ihp hz) (ihq hz);
  case ball pos _ ih => exact ball pos (ih hz);
  case bexs pos _ ih => exact bexs pos (ih hz);

lemma pi_zero_iff_sigma_zero {φ : Semiformula L ξ n} :
    BoundingHierarchy R 𝚷 0 φ ↔ BoundingHierarchy R 𝚺 0 φ :=
  ⟨zero_eq_alt, zero_eq_alt⟩

lemma zero_iff {Γ Γ'} {φ : Semiformula L ξ n} :
    BoundingHierarchy R Γ 0 φ ↔ BoundingHierarchy R Γ' 0 φ := by
  rcases Γ <;> rcases Γ' <;> simp [pi_zero_iff_sigma_zero]

lemma zero_iff_bounded {Γ} {φ : Semiformula L ξ n} :
    BoundingHierarchy R Γ 0 φ ↔ Semiformula.Bounded R φ :=
  ⟨go, bounded Γ 0 n⟩
where
  go {Γ n} {φ : Semiformula L ξ n} : BoundingHierarchy R Γ 0 φ → Semiformula.Bounded R φ
    | .bounded _ _ _ h => h
    | .and hp hq => .and (go hp) (go hq)
    | .or hp hq => .or (go hp) (go hq)
    | .ball ht hp => .ball ht (go hp)
    | .bexs ht hp => .bexs ht (go hp)

lemma zero_iff_delta_zero {Γ} {φ : Semiformula L ξ n} :
    BoundingHierarchy R Γ 0 φ ↔ DeltaZero R φ :=
  zero_iff_bounded

@[simp] lemma alt_zero_iff_zero {φ : Semiformula L ξ n} :
    BoundingHierarchy R Γ.alt 0 φ ↔ BoundingHierarchy R Γ 0 φ := by
  rcases Γ <;> simp [pi_zero_iff_sigma_zero]

lemma accum {n : ℕ} {Γ} {s : ℕ} {φ : Semiformula L ξ n} :
    BoundingHierarchy R Γ s φ → ∀ Γ', BoundingHierarchy R Γ' (s + 1) φ
  | bounded _ _ _ h, Γ => bounded Γ _ _ h
  |      and hp hq, _ => and (hp.accum _) (hq.accum _)
  |       or hp hq, _ => or (hp.accum _) (hq.accum _)
  |    ball pos hp, _ => ball pos (hp.accum _)
  |     bexs pos hp, _ => bexs pos (hp.accum _)
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
    (hp : BoundingHierarchy R Γ s φ) (Γ') {s'} (h : s < s') : BoundingHierarchy R Γ' s' φ := by
  have : ∀ d, BoundingHierarchy R Γ' (s + d + 1) φ := by
    intro d
    induction d with
    | zero => simpa using hp.accum Γ'
    | succ d ih => simpa only [Nat.add_succ, add_zero] using ih.accum _
  simpa [show s + (s' - s.succ) + 1 = s' from by
    simpa [Nat.succ_add] using Nat.add_sub_of_le h] using this (s' - s.succ)

lemma mono {Γ} {s s' : ℕ} {φ : Semiformula L ξ n}
    (hp : BoundingHierarchy R Γ s φ) (h : s ≤ s') : BoundingHierarchy R Γ s' φ := by
  rcases Nat.lt_or_eq_of_le h with (lt | rfl)
  · exact hp.strict_mono Γ lt
  · assumption

lemma of_zero {Γ Γ'} {s : ℕ} {φ : Semiformula L ξ n}
    (hp : BoundingHierarchy R Γ 0 φ) : BoundingHierarchy R Γ' s φ := by
  rcases Nat.eq_or_lt_of_le (Nat.zero_le s) with (rfl | pos)
  · exact zero_iff.mp hp
  · exact strict_mono hp Γ' pos

lemma neg {φ : Semiformula L ξ n} :
    BoundingHierarchy R Γ s φ → BoundingHierarchy R Γ.alt s (∼φ) := by
  intro h;
  induction h <;> try (solve | simp [*]);
  case bounded h => exact .bounded _ _ _ h.neg;
  case bexs pos _ ih => simpa only [Semiformula.neg_bexs] using ball pos ih;
  case ball pos _ ih => simpa only [Semiformula.neg_ball] using bexs pos ih;
  case exs ih => exact all ih;
  case all ih => exact exs ih;
  case sigma ih => exact pi ih;
  case pi ih => exact sigma ih;
  case dummy_pi ih => exact dummy_sigma ih;
  case dummy_sigma ih => exact dummy_pi ih;

@[simp] lemma neg_iff {φ : Semiformula L ξ n} :
    BoundingHierarchy R Γ s (∼φ) ↔ BoundingHierarchy R Γ.alt s φ := by
  constructor
  · intro h
    simpa using neg h
  · intro h
    simpa using neg h

@[simp] lemma imp_iff {φ ψ : Semiformula L ξ n} :
    BoundingHierarchy R Γ s (φ 🡒 ψ) ↔
      (BoundingHierarchy R Γ.alt s φ ∧ BoundingHierarchy R Γ s ψ) := by
  simp [Semiformula.imp_eq]

@[simp] lemma ball_iff {Γ s n} {φ : Semiformula L ξ (n + 1)}
    {t : Semiterm L ξ (n + 1)} (ht : t.Positive) :
    BoundingHierarchy R Γ s (∀¹[R.operator ![#0, t]] φ) ↔ BoundingHierarchy R Γ s φ := by
  constructor;
  · generalize hq : (∀¹[R.operator ![#0, t]] φ) = ψ;
    intro H;
    induction H <;> simp only [FFL.FirstOrder.ball, FFL.FirstOrder.bexs,
      Semiformula.all_inj, Semiformula.imp_inj, reduceCtorEq] at hq;
    case bounded h =>
      rcases hq with rfl;
      exact .bounded _ _ _ ((Semiformula.Bounded.ball_iff ht).mp h);
    case ball φ t pt hp ih =>
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
  · intro hp;
    exact hp.ball ht;

@[simp] lemma bexs_iff {Γ s n} {φ : Semiformula L ξ (n + 1)}
    {t : Semiterm L ξ (n + 1)} (ht : t.Positive) :
    BoundingHierarchy R Γ s (∃¹[R.operator ![#0, t]] φ) ↔ BoundingHierarchy R Γ s φ := by
  constructor;
  · generalize hq : (∃¹[R.operator ![#0, t]] φ) = ψ;
    intro H;
    induction H <;> simp only [FFL.FirstOrder.ball, FFL.FirstOrder.bexs,
      Semiformula.exs_inj, Semiformula.and_inj, reduceCtorEq] at hq;
    case bounded h =>
      rcases hq with rfl;
      exact .bounded _ _ _ ((Semiformula.Bounded.bexs_iff ht).mp h);
    case bexs φ t pt hp ih =>
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
  · intro hp;
    exact hp.bexs ht;

/-- An auxiliary condition here requiring every application of `R` to lie in every hierarchy
level. -/
class Small (R : Semiformula.Operator L 2) (ξ : Type*) : Prop where
  operator {n : ℕ} {Γ : Polarity} {s : ℕ}
    (v : Fin 2 → Semiterm L ξ n) :
    BoundingHierarchy R Γ s (R.operator v)

attribute [simp] Small.operator

instance smallEq [L.Eq] (ξ : Type*) :
    Small (Semiformula.Operator.Eq.eq : Semiformula.Operator L 2) ξ where
  operator v := by
    simp [Semiformula.Operator.operator, Semiformula.Operator.Eq.sentence_eq]

instance smallLT [L.LT] (ξ : Type*) :
    Small (Semiformula.Operator.LT.lt : Semiformula.Operator L 2) ξ where
  operator v := by
    simp [Semiformula.Operator.operator, Semiformula.Operator.LT.sentence_eq]

instance smallMem [L.Mem] (ξ : Type*) :
    Small (Semiformula.Operator.Mem.mem : Semiformula.Operator L 2) ξ where
  operator v := by
    simp [Semiformula.Operator.operator, Semiformula.Operator.Mem.sentence_eq]

lemma pi_of_pi_all [Small R ξ] {φ : Semiformula L ξ (n + 1)} :
    BoundingHierarchy R 𝚷 s (∀¹ φ) → BoundingHierarchy R 𝚷 s φ := by
  intro h;
  cases h;
  case bounded h =>
    cases h;
    case ball φ t ht hp => exact imp_iff.mpr ⟨by simp, .bounded _ _ _ hp⟩;
  case ball φ t pt hp => exact imp_iff.mpr ⟨by simp, hp⟩;
  case all => assumption;
  case pi hp => exact hp.accum _;

@[simp] lemma all_iff [Small R ξ] {φ : Semiformula L ξ (n + 1)} :
    BoundingHierarchy R 𝚷 (s + 1) (∀¹ φ) ↔ BoundingHierarchy R 𝚷 (s + 1) φ :=
  ⟨pi_of_pi_all, all⟩

@[simp] lemma allItr_iff [Small R ξ] {φ : Semiformula L ξ (n + k)} :
    BoundingHierarchy R 𝚷 (s + 1) (∀¹^[k] φ) ↔ BoundingHierarchy R 𝚷 (s + 1) φ := by
  induction k <;> simp [allItr_succ, *]

lemma sigma_of_sigma_ex [Small R ξ] {φ : Semiformula L ξ (n + 1)} :
    BoundingHierarchy R 𝚺 s (∃¹ φ) → BoundingHierarchy R 𝚺 s φ := by
  intro h;
  cases h;
  case bounded h =>
    cases h;
    case bexs φ t ht hp => exact and_iff.mpr ⟨by simp, .bounded _ _ _ hp⟩;
  case bexs φ t pt hp => exact and_iff.mpr ⟨by simp, hp⟩;
  case exs => assumption;
  case sigma hp => exact hp.accum _;

@[simp] lemma sigma_iff [Small R ξ] {φ : Semiformula L ξ (n + 1)} :
    BoundingHierarchy R 𝚺 (s + 1) (∃¹ φ) ↔ BoundingHierarchy R 𝚺 (s + 1) φ :=
  ⟨sigma_of_sigma_ex, exs⟩

@[simp] lemma exsItr_iff [Small R ξ] {φ : Semiformula L ξ (n + k)} :
    BoundingHierarchy R 𝚺 (s + 1) (∃¹^[k] φ) ↔ BoundingHierarchy R 𝚺 (s + 1) φ := by
  induction k <;> simp [exsItr_succ, *]

lemma rew (ω : Rew L ξ₁ n₁ ξ₂ n₂) {φ : Semiformula L ξ₁ n₁} :
    BoundingHierarchy R Γ s φ → BoundingHierarchy R Γ s (ω ▹ φ) := by
  intro h;
  induction h generalizing n₂ <;> try (solve | simp [*]);
  case bounded h => exact .bounded _ _ _ (h.rew ω);
  case exs ih => exact (ih ω.q).exs;
  case all ih => exact (ih ω.q).all;
  case sigma ih => exact (ih ω.q).sigma;
  case pi ih => exact (ih ω.q).pi;
  case dummy_pi ih => exact (ih ω.q).dummy_pi;
  case dummy_sigma ih => exact (ih ω.q).dummy_sigma;

@[simp] lemma rew_iff [R.SymbolLike ξ₁ ξ₂]
    {ω : Rew L ξ₁ n₁ ξ₂ n₂} {φ : Semiformula L ξ₁ n₁} :
    BoundingHierarchy R Γ s (ω ▹ φ) ↔ BoundingHierarchy R Γ s φ := by
  constructor;
  · generalize eq : ω ▹ φ = ψ;
    intro hq;
    induction hq generalizing φ n₁
      <;> try simp only [Semiformula.eq_ball_iff,
        Semiformula.eq_bexs_iff, Semiformula.eq_all_iff,
        Semiformula.eq_exs_iff, Semiformula.eq_and_iff, Semiformula.eq_or_iff,
        exists_and_left] at eq;
    case bounded h =>
      exact .bounded _ _ _ (Semiformula.Bounded.rew_iff.mp (eq.symm ▸ h));
    case and ihp ihq =>
      rcases eq with ⟨φ₁, rfl, φ₂, rfl, rfl⟩;
      simpa using ⟨ihp rfl, ihq rfl⟩;
    case or ihp ihq =>
      rcases eq with ⟨φ₁, rfl, φ₂, rfl, rfl⟩;
      simpa using ⟨ihp rfl, ihq rfl⟩;
    case ball t pos _ ih =>
      rcases eq with ⟨χ, hχ, φ, hφ, rfl⟩;
      obtain ⟨u, rfl, hu⟩ := Semiformula.Bounded.operator_preimage hχ pos;
      exact BoundingHierarchy.ball hu (ih hφ);
    case bexs t pos _ ih =>
      rcases eq with ⟨χ, hχ, φ, hφ, rfl⟩;
      obtain ⟨u, rfl, hu⟩ := Semiformula.Bounded.operator_preimage hχ pos;
      exact BoundingHierarchy.bexs hu (ih hφ);
    case all ih => rcases eq with ⟨φ, rfl, rfl⟩; exact BoundingHierarchy.all (ih rfl);
    case exs ih => rcases eq with ⟨φ, rfl, rfl⟩; exact BoundingHierarchy.exs (ih rfl);
    case pi ih => rcases eq with ⟨φ, rfl, rfl⟩; exact BoundingHierarchy.pi (ih rfl);
    case sigma ih => rcases eq with ⟨φ, rfl, rfl⟩; exact BoundingHierarchy.sigma (ih rfl);
    case dummy_sigma ih =>
      rcases eq with ⟨φ, rfl, rfl⟩; exact BoundingHierarchy.dummy_sigma (ih rfl);
    case dummy_pi ih => rcases eq with ⟨φ, rfl, rfl⟩; exact BoundingHierarchy.dummy_pi (ih rfl);
  · exact BoundingHierarchy.rew _;

lemma exsClosure : {n : ℕ} → {φ : Semiformula L ξ n} →
    BoundingHierarchy R 𝚺 (s + 1) φ → BoundingHierarchy R 𝚺 (s + 1) (exsClosure φ)
  | 0, _, hp => hp
  | _ + 1, φ, hp => exsClosure (φ := ∃¹ φ) hp.exs

instance : LogicalConnective.AndOrClosed (BoundingHierarchy R Γ s : Semiformula L ξ k → Prop) where
  verum := verum _ _ _
  falsum := falsum _ _ _
  and := and
  or := or

instance : LogicalConnective.Closed (BoundingHierarchy R Γ 0 : Semiformula L ξ k → Prop) where
  not := by simp
  imply := by simp [Semiformula.imp_eq]; tauto

lemma of_open {φ : Semiformula L ξ n} : φ.Open → BoundingHierarchy R Γ s φ := by
  induction φ using Semiformula.rec' <;> simp_all;

lemma iff_iff {φ ψ : Semiformula L ξ n} :
    BoundingHierarchy R Γ s (φ 🡘 ψ) ↔
      (BoundingHierarchy R Γ s φ ∧ BoundingHierarchy R Γ.alt s φ ∧
        BoundingHierarchy R Γ s ψ ∧ BoundingHierarchy R Γ.alt s ψ) := by
  simp [Semiformula.iff_eq]; tauto

@[simp] lemma iff_iff₀ {φ ψ : Semiformula L ξ n} :
    BoundingHierarchy R Γ 0 (φ 🡘 ψ) ↔
      (BoundingHierarchy R Γ 0 φ ∧ BoundingHierarchy R Γ 0 ψ) := by
  simp [Semiformula.iff_eq]; tauto

lemma remove_forall [Small R ξ] {φ : Semiformula L ξ (n + 1)} :
    BoundingHierarchy R Γ s (∀¹ φ) → BoundingHierarchy R Γ s φ := by
  intro h
  rcases h
  case bounded h =>
    cases h;
    case ball φ t ht hp => exact imp_iff.mpr ⟨by simp, .bounded _ _ _ hp⟩;
  case ball φ t pt hp =>
    exact imp_iff.mpr
      ⟨(show BoundingHierarchy R Γ.alt s (R.operator ![#0, t]) from
          (inferInstance : Small R ξ).operator ![#0, t]), hp⟩
  case all => assumption
  case pi h => exact h.accum _
  case dummy_sigma h => exact h.accum _

lemma remove_exists [Small R ξ] {φ : Semiformula L ξ (n + 1)} :
    BoundingHierarchy R Γ s (∃¹ φ) → BoundingHierarchy R Γ s φ := by
  intro h
  rcases h
  case bounded h =>
    cases h;
    case bexs φ t ht hp => exact and_iff.mpr ⟨by simp, .bounded _ _ _ hp⟩;
  case bexs φ t pt hp =>
    exact and_iff.mpr
      ⟨(show BoundingHierarchy R Γ s (R.operator ![#0, t]) from
          (inferInstance : Small R ξ).operator ![#0, t]), hp⟩
  case exs => assumption
  case sigma h => exact h.accum _
  case dummy_pi h => exact h.accum _

@[simp] lemma padding_iff {Γ s n} {φ : Semiformula L ξ n} :
    BoundingHierarchy R Γ s (φ.padding k) ↔ BoundingHierarchy R Γ s φ := by
  simp only [Semiformula.padding, and_iff, and_iff_left_iff_imp]
  intro h
  induction k <;> simp [List.replicate_succ, *]

@[simp] lemma list_conj₂_iff {Γ s n} {l : List (Semiformula L ξ n)} :
    BoundingHierarchy R Γ s (⋀l) ↔ ∀ φ ∈ l, BoundingHierarchy R Γ s φ := by
  match l with
  |          [] => simp
  |         [_] => simp
  | ψ :: χ :: l => simp [list_conj₂_iff (l := χ :: l)]

@[simp] lemma list_disj₂_iff {Γ s n} {l : List (Semiformula L ξ n)} :
    BoundingHierarchy R Γ s (⋁l) ↔ ∀ φ ∈ l, BoundingHierarchy R Γ s φ := by
  match l with
  |          [] => simp
  |         [_] => simp
  | ψ :: χ :: l => simp [list_disj₂_iff (l := χ :: l)]

@[simp] lemma list_conj'_iff {Γ s n} {l : List ι} {φ : ι → Semiformula L ξ n} :
    BoundingHierarchy R Γ s (l.conj' φ) ↔ ∀ i ∈ l, BoundingHierarchy R Γ s (φ i) := by
  simp [List.conj']

@[simp] lemma list_disj'_iff {Γ s n} {l : List ι} {φ : ι → Semiformula L ξ n} :
    BoundingHierarchy R Γ s (l.disj' φ) ↔ ∀ i ∈ l, BoundingHierarchy R Γ s (φ i) := by
  simp [List.disj']

@[simp] lemma finset_conj'_iff {Γ s n} {t : Finset ι} {φ : ι → Semiformula L ξ n} :
    BoundingHierarchy R Γ s (t.conj' φ) ↔ ∀ i ∈ t, BoundingHierarchy R Γ s (φ i) := by
  simp [Finset.conj']

@[simp] lemma finset_disj'_iff {Γ s n} {t : Finset ι} {φ : ι → Semiformula L ξ n} :
    BoundingHierarchy R Γ s (t.disj' φ) ↔ ∀ i ∈ t, BoundingHierarchy R Γ s (φ i) := by
  simp [Finset.disj']

@[simp] lemma finset_uconj_iff {Γ s n} [Fintype ι] {φ : ι → Semiformula L ξ n} :
    BoundingHierarchy R Γ s (Finset.uconj φ) ↔ ∀ i, BoundingHierarchy R Γ s (φ i) := by
  simp [Finset.uconj]

@[simp] lemma finset_udisj_iff {Γ s n} [Fintype ι] {φ : ι → Semiformula L ξ n} :
    BoundingHierarchy R Γ s (Finset.udisj φ) ↔ ∀ i, BoundingHierarchy R Γ s (φ i) := by
  simp [Finset.udisj]

lemma sigma₁_induction [Small R ξ]
    {P : (n : ℕ) → Semiformula L ξ n → Prop}
    (hVerum : ∀ n, P n ⊤)
    (hFalsum : ∀ n, P n ⊥)
    (hRel : ∀ n k (r : L.Rel k) (v : Fin k → Semiterm L ξ n), P n (.rel r v))
    (hNRel : ∀ n k (r : L.Rel k) (v : Fin k → Semiterm L ξ n), P n (.nrel r v))
    (hAnd : ∀ n φ ψ, BoundingHierarchy R 𝚺 1 φ → BoundingHierarchy R 𝚺 1 ψ → P n φ → P n ψ →
      P n (φ ⋏ ψ))
    (hOr : ∀ n φ ψ, BoundingHierarchy R 𝚺 1 φ → BoundingHierarchy R 𝚺 1 ψ → P n φ → P n ψ →
      P n (φ ⋎ ψ))
    (hBall : ∀ n t φ, BoundingHierarchy R 𝚺 1 φ → P (n + 1) φ →
      P n (∀¹[R.operator ![#0, Rew.bShift t]] φ))
    (hExs : ∀ n φ, BoundingHierarchy R 𝚺 1 φ → P (n + 1) φ → P n (∃¹ φ))
    (hOperator : ∀ n t, P (n + 1) (R.operator ![#0, Rew.bShift t]))
    (n φ) : BoundingHierarchy R 𝚺 1 φ → P n φ
  | BoundingHierarchy.bounded _ _ _ h => by
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
    | ball ht hp ih =>
      obtain ⟨t, rfl⟩ := Rew.positive_iff.mp ht;
      exact hBall _ t _ (.bounded _ _ _ hp) ih;
    | bexs ht hp ih =>
      obtain ⟨t, rfl⟩ := Rew.positive_iff.mp ht;
      exact hExs _ _ (and_iff.mpr ⟨by simp, .bounded _ _ _ hp⟩)
        (hAnd _ _ _ (by simp) (.bounded _ _ _ hp) (hOperator _ t) ih);
  |                 BoundingHierarchy.and hp hq =>
    hAnd _ _ _ hp hq
      (sigma₁_induction hVerum hFalsum hRel hNRel hAnd hOr hBall hExs hOperator _ _ hp)
      (sigma₁_induction hVerum hFalsum hRel hNRel hAnd hOr hBall hExs hOperator _ _ hq)
  |                  BoundingHierarchy.or hp hq =>
    hOr _ _ _ hp hq
      (sigma₁_induction hVerum hFalsum hRel hNRel hAnd hOr hBall hExs hOperator _ _ hp)
      (sigma₁_induction hVerum hFalsum hRel hNRel hAnd hOr hBall hExs hOperator _ _ hq)
  |                BoundingHierarchy.ball pt hp => by
    rcases Rew.positive_iff.mp pt with ⟨t, rfl⟩
    exact hBall _ t _ hp
      (sigma₁_induction hVerum hFalsum hRel hNRel hAnd hOr hBall hExs hOperator _ _ hp)
  |                 BoundingHierarchy.bexs pt hp => by
    apply hExs
    · simp [hp]
    · rcases Rew.positive_iff.mp pt with ⟨t, rfl⟩
      apply hAnd _ _ _ (by simp) hp (hOperator _ t)
        (sigma₁_induction hVerum hFalsum hRel hNRel hAnd hOr hBall hExs hOperator _ _ hp)
  |         BoundingHierarchy.sigma (φ := φ) hp =>
    have : BoundingHierarchy R 𝚺 1 φ := hp.accum _
    hExs _ _ this
      (sigma₁_induction hVerum hFalsum hRel hNRel hAnd hOr hBall hExs hOperator _ _ this)
  |                    BoundingHierarchy.exs hp =>
    hExs _ _ hp
      (sigma₁_induction hVerum hFalsum hRel hNRel hAnd hOr hBall hExs hOperator _ _ hp)

end BoundingHierarchy

end FFL.FirstOrder

end
