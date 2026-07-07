module

public import Foundation.FirstOrder.Basic.Operator
public import Foundation.FirstOrder.Basic.Padding

@[expose] public section
/-!
# Operator-bounded first-order hierarchies

This file provides the reusable syntactic part of a Levy-style hierarchy:
bounded quantifiers are bounded by a binary `Semiformula.Operator`.

The intended specializations are arithmetic (`op(<)`) and set theory (`op(∈)`).
-/

namespace LO.FirstOrder

namespace OperatorHierarchy

variable {L : Language}

/-- The `R`-bounded universal quantifier. -/
def ball (R : Semiformula.Operator L 2) (t : Semiterm L ξ n)
    (φ : Semiformula L ξ (n + 1)) : Semiformula L ξ n :=
  ∀⁰[R.operator ![#0, Rew.bShift t]] φ

/-- The `R`-bounded existential quantifier. -/
def bexs (R : Semiformula.Operator L 2) (t : Semiterm L ξ n)
    (φ : Semiformula L ξ (n + 1)) : Semiformula L ξ n :=
  ∃⁰[R.operator ![#0, Rew.bShift t]] φ

variable (R : Semiformula.Operator L 2)

/--
`Hierarchy R Γ n φ` says that `φ` is a `Σₙ` or `Πₙ` formula, with bounded
quantifiers recognized syntactically as quantifiers bounded by `R`.
-/
inductive Hierarchy : Polarity → ℕ → {n : ℕ} → Semiformula L ξ n → Prop
  | verum (Γ s n) : Hierarchy Γ s (⊤ : Semiformula L ξ n)
  | falsum (Γ s n) : Hierarchy Γ s (⊥ : Semiformula L ξ n)
  | rel (Γ s) {k} (r : L.Rel k) (v) : Hierarchy Γ s (Semiformula.rel r v)
  | nrel (Γ s) {k} (r : L.Rel k) (v) : Hierarchy Γ s (Semiformula.nrel r v)
  | and {Γ s n} {φ ψ : Semiformula L ξ n} :
    Hierarchy Γ s φ → Hierarchy Γ s ψ → Hierarchy Γ s (φ ⋏ ψ)
  | or {Γ s n} {φ ψ : Semiformula L ξ n} :
    Hierarchy Γ s φ → Hierarchy Γ s ψ → Hierarchy Γ s (φ ⋎ ψ)
  | ball {Γ s n} {φ : Semiformula L ξ (n + 1)} {t : Semiterm L ξ (n + 1)} :
    t.Positive → Hierarchy Γ s φ → Hierarchy Γ s (∀⁰[R.operator ![#0, t]] φ)
  | bexs {Γ s n} {φ : Semiformula L ξ (n + 1)} {t : Semiterm L ξ (n + 1)} :
    t.Positive → Hierarchy Γ s φ → Hierarchy Γ s (∃⁰[R.operator ![#0, t]] φ)
  | exs {s n} {φ : Semiformula L ξ (n + 1)} :
    Hierarchy 𝚺 (s + 1) φ → Hierarchy 𝚺 (s + 1) (∃⁰ φ)
  | all {s n} {φ : Semiformula L ξ (n + 1)} :
    Hierarchy 𝚷 (s + 1) φ → Hierarchy 𝚷 (s + 1) (∀⁰ φ)
  | sigma {s n} {φ : Semiformula L ξ (n + 1)} :
    Hierarchy 𝚷 s φ → Hierarchy 𝚺 (s + 1) (∃⁰ φ)
  | pi {s n} {φ : Semiformula L ξ (n + 1)} :
    Hierarchy 𝚺 s φ → Hierarchy 𝚷 (s + 1) (∀⁰ φ)
  | dummy_sigma {s n} {φ : Semiformula L ξ (n + 1)} :
    Hierarchy 𝚷 (s + 1) φ → Hierarchy 𝚺 (s + 1 + 1) (∀⁰ φ)
  | dummy_pi {s n} {φ : Semiformula L ξ (n + 1)} :
    Hierarchy 𝚺 (s + 1) φ → Hierarchy 𝚷 (s + 1 + 1) (∃⁰ φ)

def DeltaZero (φ : Semiformula L ξ n) : Prop := Hierarchy R 𝚺 0 φ

attribute [simp] Hierarchy.verum Hierarchy.falsum Hierarchy.rel Hierarchy.nrel

namespace Hierarchy

variable {R}

set_option linter.flexible false in
@[simp] lemma and_iff {φ ψ : Semiformula L ξ n} :
    Hierarchy R Γ s (φ ⋏ ψ) ↔ Hierarchy R Γ s φ ∧ Hierarchy R Γ s ψ :=
  ⟨by
      generalize hr : φ ⋏ ψ = r
      intro H
      induction H <;> try simp [LO.FirstOrder.ball, LO.FirstOrder.bexs] at hr
      case and =>
        rcases hr with ⟨rfl, rfl⟩
        constructor <;> assumption,
   by rintro ⟨hp, hq⟩; exact Hierarchy.and hp hq⟩

set_option linter.flexible false in
@[simp] lemma or_iff {φ ψ : Semiformula L ξ n} :
    Hierarchy R Γ s (φ ⋎ ψ) ↔ Hierarchy R Γ s φ ∧ Hierarchy R Γ s ψ :=
  ⟨by
      generalize hr : φ ⋎ ψ = r
      intro H
      induction H <;> try simp [LO.FirstOrder.ball, LO.FirstOrder.bexs] at hr
      case or =>
        rcases hr with ⟨rfl, rfl⟩
        constructor <;> assumption,
   by rintro ⟨hp, hq⟩; exact Hierarchy.or hp hq⟩

set_option linter.flexible false in
lemma zero_eq_alt {φ : Semiformula L ξ n} :
    Hierarchy R Γ 0 φ → Hierarchy R Γ.alt 0 φ := by
  generalize hz : 0 = z
  rw [eq_comm] at hz
  intro h
  induction h <;> try simp at hz ⊢
  case and _ _ ihp ihq => exact ⟨ihp hz, ihq hz⟩
  case or _ _ ihp ihq => exact ⟨ihp hz, ihq hz⟩
  case ball pos _ ih => exact ball pos (ih hz)
  case bexs pos _ ih => exact bexs pos (ih hz)

lemma pi_zero_iff_sigma_zero {φ : Semiformula L ξ n} :
    Hierarchy R 𝚷 0 φ ↔ Hierarchy R 𝚺 0 φ :=
  ⟨zero_eq_alt, zero_eq_alt⟩

lemma zero_iff {Γ Γ'} {φ : Semiformula L ξ n} :
    Hierarchy R Γ 0 φ ↔ Hierarchy R Γ' 0 φ := by
  rcases Γ <;> rcases Γ' <;> simp [pi_zero_iff_sigma_zero]

lemma zero_iff_delta_zero {Γ} {φ : Semiformula L ξ n} :
    Hierarchy R Γ 0 φ ↔ DeltaZero R φ := by
  simpa [DeltaZero, pi_zero_iff_sigma_zero] using zero_iff (R := R)

@[simp] lemma alt_zero_iff_zero {φ : Semiformula L ξ n} :
    Hierarchy R Γ.alt 0 φ ↔ Hierarchy R Γ 0 φ := by
  rcases Γ <;> simp [pi_zero_iff_sigma_zero]

lemma accum {Γ} {s : ℕ} {φ : Semiformula L ξ n} :
    Hierarchy R Γ s φ → ∀ Γ', Hierarchy R Γ' (s + 1) φ
  |    verum _ _ _, _ => verum _ _ _
  |   falsum _ _ _, _ => falsum _ _ _
  |    rel _ _ r v, _ => rel _ _ r v
  |   nrel _ _ r v, _ => nrel _ _ r v
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
    (hp : Hierarchy R Γ s φ) (Γ') {s'} (h : s < s') : Hierarchy R Γ' s' φ := by
  have : ∀ d, Hierarchy R Γ' (s + d + 1) φ := by
    intro d
    induction' d with d ih
    · simpa using hp.accum Γ'
    · simpa only [Nat.add_succ, add_zero] using ih.accum _
  simpa [show s + (s' - s.succ) + 1 = s' from by
    simpa [Nat.succ_add] using Nat.add_sub_of_le h] using this (s' - s.succ)

lemma mono {Γ} {s s' : ℕ} {φ : Semiformula L ξ n}
    (hp : Hierarchy R Γ s φ) (h : s ≤ s') : Hierarchy R Γ s' φ := by
  rcases Nat.lt_or_eq_of_le h with (lt | rfl)
  · exact hp.strict_mono Γ lt
  · assumption

lemma of_zero {Γ Γ'} {s : ℕ} {φ : Semiformula L ξ n}
    (hp : Hierarchy R Γ 0 φ) : Hierarchy R Γ' s φ := by
  rcases Nat.eq_or_lt_of_le (Nat.zero_le s) with (rfl | pos)
  · exact zero_iff.mp hp
  · exact strict_mono hp Γ' pos

set_option linter.flexible false in
lemma neg {φ : Semiformula L ξ n} :
    Hierarchy R Γ s φ → Hierarchy R Γ.alt s (∼φ) := by
  intro h
  induction h <;> try simp [*]
  case bexs pos _ ih => exact ball pos ih
  case ball pos _ ih => exact bexs pos ih
  case exs ih => exact all ih
  case all ih => exact exs ih
  case sigma ih => exact pi ih
  case pi ih => exact sigma ih
  case dummy_pi ih => exact dummy_sigma ih
  case dummy_sigma ih => exact dummy_pi ih

@[simp] lemma neg_iff {φ : Semiformula L ξ n} :
    Hierarchy R Γ s (∼φ) ↔ Hierarchy R Γ.alt s φ :=
  ⟨fun h => by simpa using neg h, fun h => by simpa using neg h⟩

@[simp] lemma imp_iff {φ ψ : Semiformula L ξ n} :
    Hierarchy R Γ s (φ 🡒 ψ) ↔
      (Hierarchy R Γ.alt s φ ∧ Hierarchy R Γ s ψ) := by
  simp [Semiformula.imp_eq]

lemma ball_of {φ : Semiformula L ξ (n + 1)} {t : Semiterm L ξ n}
    (hφ : Hierarchy R Γ s φ) : Hierarchy R Γ s (OperatorHierarchy.ball R t φ) := by
  exact Hierarchy.ball (R := R) (t := Rew.bShift t) (by simp) hφ

lemma bexs_of {φ : Semiformula L ξ (n + 1)} {t : Semiterm L ξ n}
    (hφ : Hierarchy R Γ s φ) : Hierarchy R Γ s (OperatorHierarchy.bexs R t φ) := by
  exact Hierarchy.bexs (R := R) (t := Rew.bShift t) (by simp) hφ

set_option linter.flexible false in
lemma rew (ω : Rew L ξ₁ n₁ ξ₂ n₂) {φ : Semiformula L ξ₁ n₁} :
    Hierarchy R Γ s φ → Hierarchy R Γ s (ω ▹ φ) := by
  intro h
  induction h generalizing n₂ <;> try simp [*]
  case ball t pos hp ih =>
    simpa [LO.FirstOrder.ball, LO.FirstOrder.bexs] using
      Hierarchy.ball (R := R) (t := ω.q t) (by simpa using pos) (ih ω.q)
  case bexs t pos hp ih =>
    simpa [LO.FirstOrder.ball, LO.FirstOrder.bexs] using
      Hierarchy.bexs (R := R) (t := ω.q t) (by simpa using pos) (ih ω.q)
  case exs ih => exact (ih ω.q).exs
  case all ih => exact (ih ω.q).all
  case sigma ih => exact (ih ω.q).sigma
  case pi ih => exact (ih ω.q).pi
  case dummy_pi ih => exact (ih ω.q).dummy_pi
  case dummy_sigma ih => exact (ih ω.q).dummy_sigma

lemma exsClosure : {n : ℕ} → {φ : Semiformula L ξ n} →
    Hierarchy R 𝚺 (s + 1) φ → Hierarchy R 𝚺 (s + 1) (exsClosure φ)
  | 0, _, hp => hp
  | _ + 1, φ, hp => exsClosure (φ := ∃⁰ φ) hp.exs

instance : LogicalConnective.AndOrClosed (Hierarchy R Γ s : Semiformula L ξ k → Prop) where
  verum := verum _ _ _
  falsum := falsum _ _ _
  and := and
  or := or

instance : LogicalConnective.Closed (Hierarchy R Γ 0 : Semiformula L ξ k → Prop) where
  not := by simp
  imply := by simp [Semiformula.imp_eq]; tauto

set_option linter.flexible false in
lemma of_open {φ : Semiformula L ξ n} : φ.Open → Hierarchy R Γ s φ := by
  induction φ using Semiformula.rec' <;> simp
  case hand ihp ihq => intro hp hq; exact ⟨ihp hp, ihq hq⟩
  case hor ihp ihq => intro hp hq; exact ⟨ihp hp, ihq hq⟩

/--
An operator is small for its own hierarchy if every substitution instance of
the operator formula is available at every finite hierarchy level.

This holds for the arithmetic `<` operator and the set-theoretic membership
operator because those operators are atomic. It is not true for an arbitrary
`Semiformula.Operator`, so bounded-quantifier inversion lemmas below keep this
assumption explicit.
-/
class OperatorSmall (R : Semiformula.Operator L 2) (ξ : Type*) : Prop where
  operator {n : ℕ} {Γ : Polarity} {s : ℕ}
    (v : Fin 2 → Semiterm L ξ n) :
    Hierarchy R Γ s (R.operator v)

attribute [simp] OperatorSmall.operator

instance operatorSmallLT [L.LT] (ξ : Type*) :
    OperatorSmall (Semiformula.Operator.LT.lt : Semiformula.Operator L 2) ξ where
  operator v := by
    simp [Semiformula.Operator.operator, Semiformula.Operator.LT.sentence_eq]

instance operatorSmallMem [L.Mem] (ξ : Type*) :
    OperatorSmall (Semiformula.Operator.Mem.mem : Semiformula.Operator L 2) ξ where
  operator v := by
    simp [Semiformula.Operator.operator, Semiformula.Operator.Mem.sentence_eq]

/--
`OperatorRewPreimage R` says that an `R`-bound recognized after rewriting by
`ω.q` already came from an `R`-bound before rewriting.

This is the exact syntactic fact needed to prove the reverse direction of
`rew_iff`. It holds for the atomic operators used by the arithmetic and Levy
hierarchies. It is kept separate from `OperatorSmall`, since arbitrary
`Semiformula.Operator`s can be composite formulas where this inversion is a
stronger requirement.
-/
class OperatorRewPreimage (R : Semiformula.Operator L 2) (ξ₁ ξ₂ : Type*) : Prop where
  operator_preimage {n₁ n₂ : ℕ} (ω : Rew L ξ₁ n₁ ξ₂ n₂)
    {φ : Semiformula L ξ₁ (n₁ + 1)}
    {t : Semiterm L ξ₂ (n₂ + 1)} :
      ω.q ▹ φ = R.operator ![#0, t] →
        ∃ u : Semiterm L ξ₁ (n₁ + 1),
          ω.q u = t ∧ φ = R.operator ![#0, u]

instance operatorRewPreimageLT [L.LT] (ξ₁ ξ₂ : Type*) :
    OperatorRewPreimage (Semiformula.Operator.LT.lt : Semiformula.Operator L 2) ξ₁ ξ₂ where
  operator_preimage := by
    intro n₁ n₂ ω φ t h
    rcases (Rew.eq_lt_iff (ω := ω.q)).mp h with ⟨t', u, ht', hu, hφ⟩
    have ht' : t' = #0 := (Rew.q_eq_zero_iff (ω := ω) (t := t')).mp ht'
    subst ht'
    exact ⟨u, hu, hφ⟩

instance operatorRewPreimageMem [L.Mem] (ξ₁ ξ₂ : Type*) :
    OperatorRewPreimage (Semiformula.Operator.Mem.mem : Semiformula.Operator L 2) ξ₁ ξ₂ where
  operator_preimage := by
    intro n₁ n₂ ω φ t h
    rcases (Rew.eq_mem_iff (ω := ω.q)).mp h with ⟨t', u, ht', hu, hφ⟩
    have ht' : t' = #0 := (Rew.q_eq_zero_iff (ω := ω) (t := t')).mp ht'
    subst ht'
    exact ⟨u, hu, hφ⟩

set_option linter.flexible false in
@[simp] lemma rew_iff [OperatorRewPreimage R ξ₁ ξ₂]
    {ω : Rew L ξ₁ n₁ ξ₂ n₂} {φ : Semiformula L ξ₁ n₁} :
    Hierarchy R Γ s (ω ▹ φ) ↔ Hierarchy R Γ s φ := by
  constructor
  · generalize eq : ω ▹ φ = ψ
    intro hq
    induction hq generalizing φ n₁
      <;> try simp [Semiformula.eq_rel_iff,
        Semiformula.eq_nrel_iff, Semiformula.eq_ball_iff,
        Semiformula.eq_bexs_iff, Semiformula.eq_all_iff,
        Semiformula.eq_exs_iff] at eq
    case verum =>
      rcases eq with rfl
      simp
    case falsum =>
      rcases eq with rfl
      simp
    case rel =>
      rcases eq with ⟨v', rfl, rfl⟩
      simp
    case nrel =>
      rcases eq with ⟨v', rfl, rfl⟩
      simp
    case and ihp ihq =>
      rcases eq with ⟨φ₁, rfl, φ₂, rfl, rfl⟩
      simpa using ⟨ihp rfl, ihq rfl⟩
    case or ihp ihq =>
      rcases eq with ⟨φ₁, rfl, φ₂, rfl, rfl⟩
      simpa using ⟨ihp rfl, ihq rfl⟩
    case ball pos _ ih =>
      rcases eq with ⟨χ, hχ, φ, hφ, rfl⟩
      rcases (inferInstance : OperatorRewPreimage R ξ₁ ξ₂).operator_preimage
          (φ := χ) (t := _) ω hχ with
        ⟨u, hu, rfl⟩
      have huPos : u.Positive := by
        rw [← Rew.q_positive_iff (ω := ω) (t := u), hu]
        exact pos
      exact Hierarchy.ball huPos (ih hφ)
    case bexs pos _ ih =>
      rcases eq with ⟨χ, hχ, φ, hφ, rfl⟩
      rcases (inferInstance : OperatorRewPreimage R ξ₁ ξ₂).operator_preimage
          (φ := χ) (t := _) ω hχ with
        ⟨u, hu, rfl⟩
      have huPos : u.Positive := by
        rw [← Rew.q_positive_iff (ω := ω) (t := u), hu]
        exact pos
      exact Hierarchy.bexs huPos (ih hφ)
    case all ih =>
      rcases eq with ⟨φ, rfl, rfl⟩
      exact Hierarchy.all (ih rfl)
    case exs ih =>
      rcases eq with ⟨φ, rfl, rfl⟩
      exact Hierarchy.exs (ih rfl)
    case pi ih =>
      rcases eq with ⟨φ, rfl, rfl⟩
      exact Hierarchy.pi (ih rfl)
    case sigma ih =>
      rcases eq with ⟨φ, rfl, rfl⟩
      exact Hierarchy.sigma (ih rfl)
    case dummy_sigma ih =>
      rcases eq with ⟨φ, rfl, rfl⟩
      exact Hierarchy.dummy_sigma (ih rfl)
    case dummy_pi ih =>
      rcases eq with ⟨φ, rfl, rfl⟩
      exact Hierarchy.dummy_pi (ih rfl)
  · exact Hierarchy.rew _

set_option linter.flexible false in
@[simp] lemma conj_iff {φ : Fin m → Semiformula L ξ n} :
    Hierarchy R Γ s (Matrix.conj φ) ↔ ∀ i, Hierarchy R Γ s (φ i) := by
  induction m <;> simp [Matrix.conj, Matrix.vecTail, *]
  · exact ⟨by rintro ⟨hz, hs⟩ i; cases i using Fin.cases <;> simp [*],
           by intro h; exact ⟨h 0, fun _ => h _⟩⟩

set_option linter.flexible false in
@[simp] lemma ball_iff [OperatorSmall R ξ] {Γ s n} {φ : Semiformula L ξ (n + 1)}
    {t : Semiterm L ξ (n + 1)} (ht : t.Positive) :
    Hierarchy R Γ s (∀⁰[R.operator ![#0, t]] φ) ↔ Hierarchy R Γ s φ :=
  ⟨by
      generalize hq : (∀⁰[R.operator ![#0, t]] φ) = ψ
      intro H
      induction H <;> try simp [LO.FirstOrder.ball, LO.FirstOrder.bexs] at hq
      case ball φ t pt hp ih =>
        rcases hq with ⟨_, rfl⟩
        assumption
      case all hp ih =>
        rcases hq with rfl
        exact (imp_iff.mp hp).2
      case pi s _ _ hp ih =>
        rcases hq with rfl
        exact (imp_iff.mp hp).2.accum _
      case dummy_sigma hp _ =>
        rcases hq with rfl
        exact (imp_iff.mp hp).2.accum _,
   by intro hp; exact hp.ball ht⟩

set_option linter.flexible false in
@[simp] lemma bexs_iff [OperatorSmall R ξ] {Γ s n} {φ : Semiformula L ξ (n + 1)}
    {t : Semiterm L ξ (n + 1)} (ht : t.Positive) :
    Hierarchy R Γ s (∃⁰[R.operator ![#0, t]] φ) ↔ Hierarchy R Γ s φ :=
  ⟨by
      generalize hq : (∃⁰[R.operator ![#0, t]] φ) = ψ
      intro H
      induction H <;> try simp [LO.FirstOrder.ball, LO.FirstOrder.bexs] at hq
      case bexs φ t pt hp ih =>
        rcases hq with ⟨_, rfl⟩
        assumption
      case exs hp ih =>
        rcases hq with rfl
        exact (and_iff.mp hp).2
      case sigma s _ _ hp ih =>
        rcases hq with rfl
        exact (and_iff.mp hp).2.accum _
      case dummy_pi hp _ =>
        rcases hq with rfl
        exact (and_iff.mp hp).2.accum _,
   by intro hp; exact hp.bexs ht⟩

set_option linter.flexible false in
lemma pi_of_pi_all [OperatorSmall R ξ] {φ : Semiformula L ξ (n + 1)} :
    Hierarchy R 𝚷 s (∀⁰ φ) → Hierarchy R 𝚷 s φ := by
  generalize hr : ∀⁰ φ = r
  generalize hb : (𝚷 : Polarity) = Γ
  intro H
  cases H <;> try simp [LO.FirstOrder.ball, LO.FirstOrder.bexs] at hr
  case ball φ t pt hp =>
    rcases hr with rfl
    cases hb
    exact imp_iff.mpr
      ⟨(show Hierarchy R 𝚺 s (R.operator ![#0, t]) from
          (inferInstance : OperatorSmall R ξ).operator ![#0, t]), hp⟩
  case all => rcases hr with rfl; simpa
  case pi hp => rcases hr with rfl; exact hp.accum _
  case dummy_sigma hp => rcases hr with rfl; exact hp.accum _

@[simp] lemma all_iff [OperatorSmall R ξ] {φ : Semiformula L ξ (n + 1)} :
    Hierarchy R 𝚷 (s + 1) (∀⁰ φ) ↔ Hierarchy R 𝚷 (s + 1) φ :=
  ⟨pi_of_pi_all, all⟩

@[simp] lemma allItr_iff [OperatorSmall R ξ] {φ : Semiformula L ξ (n + k)} :
    Hierarchy R 𝚷 (s + 1) (∀⁰^[k] φ) ↔ Hierarchy R 𝚷 (s + 1) φ := by
  induction k <;> simp [allItr_succ, *]

set_option linter.flexible false in
lemma sigma_of_sigma_ex [OperatorSmall R ξ] {φ : Semiformula L ξ (n + 1)} :
    Hierarchy R 𝚺 s (∃⁰ φ) → Hierarchy R 𝚺 s φ := by
  generalize hr : ∃⁰ φ = r
  generalize hb : (𝚺 : Polarity) = Γ
  intro H
  cases H <;> try simp [LO.FirstOrder.ball, LO.FirstOrder.bexs] at hr
  case bexs φ t pt hp =>
    rcases hr with rfl
    cases hb
    exact and_iff.mpr
      ⟨(show Hierarchy R 𝚺 s (R.operator ![#0, t]) from
          (inferInstance : OperatorSmall R ξ).operator ![#0, t]), hp⟩
  case exs => rcases hr with rfl; simpa
  case sigma hp => rcases hr with rfl; exact hp.accum _
  case dummy_pi hp => rcases hr with rfl; exact hp.accum _

@[simp] lemma sigma_iff [OperatorSmall R ξ] {φ : Semiformula L ξ (n + 1)} :
    Hierarchy R 𝚺 (s + 1) (∃⁰ φ) ↔ Hierarchy R 𝚺 (s + 1) φ :=
  ⟨sigma_of_sigma_ex, exs⟩

@[simp] lemma exsItr_iff [OperatorSmall R ξ] {φ : Semiformula L ξ (n + k)} :
    Hierarchy R 𝚺 (s + 1) (∃⁰^[k] φ) ↔ Hierarchy R 𝚺 (s + 1) φ := by
  induction k <;> simp [exsItr_succ, *]

lemma iff_iff {φ ψ : Semiformula L ξ n} :
    Hierarchy R Γ s (φ 🡘 ψ) ↔
      (Hierarchy R Γ s φ ∧ Hierarchy R Γ.alt s φ ∧
        Hierarchy R Γ s ψ ∧ Hierarchy R Γ.alt s ψ) := by
  simp [Semiformula.iff_eq]; tauto

@[simp] lemma iff_iff₀ {φ ψ : Semiformula L ξ n} :
    Hierarchy R Γ 0 (φ 🡘 ψ) ↔
      (Hierarchy R Γ 0 φ ∧ Hierarchy R Γ 0 ψ) := by
  simp [Semiformula.iff_eq]; tauto

@[simp] lemma matrix_conj_iff {Γ s n} {φ : Fin m → Semiformula L ξ n} :
    Hierarchy R Γ s (Matrix.conj fun j ↦ φ j) ↔ ∀ j, Hierarchy R Γ s (φ j) := by
  cases m <;> simp

lemma remove_forall [OperatorSmall R ξ] {φ : Semiformula L ξ (n + 1)} :
    Hierarchy R Γ s (∀⁰ φ) → Hierarchy R Γ s φ := by
  intro h
  rcases h
  case ball φ t pt hp =>
    exact imp_iff.mpr
      ⟨(show Hierarchy R Γ.alt s (R.operator ![#0, t]) from
          (inferInstance : OperatorSmall R ξ).operator ![#0, t]), hp⟩
  case all => assumption
  case pi h => exact h.accum _
  case dummy_sigma h => exact h.accum _

lemma remove_exists [OperatorSmall R ξ] {φ : Semiformula L ξ (n + 1)} :
    Hierarchy R Γ s (∃⁰ φ) → Hierarchy R Γ s φ := by
  intro h
  rcases h
  case bexs φ t pt hp =>
    exact and_iff.mpr
      ⟨(show Hierarchy R Γ s (R.operator ![#0, t]) from
          (inferInstance : OperatorSmall R ξ).operator ![#0, t]), hp⟩
  case exs => assumption
  case sigma h => exact h.accum _
  case dummy_pi h => exact h.accum _

@[simp] lemma padding_iff {Γ s n} {φ : Semiformula L ξ n} :
    Hierarchy R Γ s (φ.padding k) ↔ Hierarchy R Γ s φ := by
  simp only [Semiformula.padding, and_iff, and_iff_left_iff_imp]
  intro h
  induction k <;> simp [List.replicate_succ, *]

@[simp] lemma list_conj₂_iff {Γ s n} {l : List (Semiformula L ξ n)} :
    Hierarchy R Γ s (⋀l) ↔ ∀ φ ∈ l, Hierarchy R Γ s φ := by
  match l with
  |          [] => simp
  |         [_] => simp
  | ψ :: χ :: l => simp [list_conj₂_iff (l := χ :: l)]

@[simp] lemma list_disj₂_iff {Γ s n} {l : List (Semiformula L ξ n)} :
    Hierarchy R Γ s (⋁l) ↔ ∀ φ ∈ l, Hierarchy R Γ s φ := by
  match l with
  |          [] => simp
  |         [_] => simp
  | ψ :: χ :: l => simp [list_disj₂_iff (l := χ :: l)]

@[simp] lemma list_conj'_iff {Γ s n} {l : List ι} {φ : ι → Semiformula L ξ n} :
    Hierarchy R Γ s (l.conj' φ) ↔ ∀ i ∈ l, Hierarchy R Γ s (φ i) := by
  simp [List.conj']

@[simp] lemma list_disj'_iff {Γ s n} {l : List ι} {φ : ι → Semiformula L ξ n} :
    Hierarchy R Γ s (l.disj' φ) ↔ ∀ i ∈ l, Hierarchy R Γ s (φ i) := by
  simp [List.disj']

@[simp] lemma finset_conj'_iff {Γ s n} {t : Finset ι} {φ : ι → Semiformula L ξ n} :
    Hierarchy R Γ s (t.conj' φ) ↔ ∀ i ∈ t, Hierarchy R Γ s (φ i) := by
  simp [Finset.conj']

@[simp] lemma finset_disj'_iff {Γ s n} {t : Finset ι} {φ : ι → Semiformula L ξ n} :
    Hierarchy R Γ s (t.disj' φ) ↔ ∀ i ∈ t, Hierarchy R Γ s (φ i) := by
  simp [Finset.disj']

@[simp] lemma finset_uconj_iff {Γ s n} [Fintype ι] {φ : ι → Semiformula L ξ n} :
    Hierarchy R Γ s (Finset.uconj φ) ↔ ∀ i, Hierarchy R Γ s (φ i) := by
  simp [Finset.uconj]

@[simp] lemma finset_udisj_iff {Γ s n} [Fintype ι] {φ : ι → Semiformula L ξ n} :
    Hierarchy R Γ s (Finset.udisj φ) ↔ ∀ i, Hierarchy R Γ s (φ i) := by
  simp [Finset.udisj]

@[simp] lemma exsItr [OperatorSmall R ξ] {n k} {φ : Semiformula L ξ (n + k)} :
    Hierarchy R 𝚺 (s + 1) (∃⁰^[k] φ) ↔ Hierarchy R 𝚺 (s + 1) φ := by
  match k with
  |     0 => simp
  | k + 1 => simp [LO.FirstOrder.exsItr_succ, exsItr]

@[simp] lemma allItr [OperatorSmall R ξ] {n k} {φ : Semiformula L ξ (n + k)} :
    Hierarchy R 𝚷 (s + 1) (∀⁰^[k] φ) ↔ Hierarchy R 𝚷 (s + 1) φ := by
  match k with
  |     0 => simp
  | k + 1 => simp [LO.FirstOrder.allItr_succ, allItr]

lemma sigma₁_induction [OperatorSmall R ξ]
    {P : (n : ℕ) → Semiformula L ξ n → Prop}
    (hVerum : ∀ n, P n ⊤)
    (hFalsum : ∀ n, P n ⊥)
    (hRel : ∀ n k (r : L.Rel k) (v : Fin k → Semiterm L ξ n), P n (.rel r v))
    (hNRel : ∀ n k (r : L.Rel k) (v : Fin k → Semiterm L ξ n), P n (.nrel r v))
    (hAnd : ∀ n φ ψ, Hierarchy R 𝚺 1 φ → Hierarchy R 𝚺 1 ψ → P n φ → P n ψ → P n (φ ⋏ ψ))
    (hOr : ∀ n φ ψ, Hierarchy R 𝚺 1 φ → Hierarchy R 𝚺 1 ψ → P n φ → P n ψ → P n (φ ⋎ ψ))
    (hBall : ∀ n t φ, Hierarchy R 𝚺 1 φ → P (n + 1) φ →
      P n (∀⁰[R.operator ![#0, Rew.bShift t]] φ))
    (hExs : ∀ n φ, Hierarchy R 𝚺 1 φ → P (n + 1) φ → P n (∃⁰ φ))
    (hOperator : ∀ n t, P (n + 1) (R.operator ![#0, Rew.bShift t]))
    (n φ) : Hierarchy R 𝚺 1 φ → P n φ
  |               Hierarchy.verum _ _ _ => hVerum _
  |              Hierarchy.falsum _ _ _ => hFalsum _
  |                  Hierarchy.rel _ _ r v => hRel _ _ r v
  |                 Hierarchy.nrel _ _ r v => hNRel _ _ r v
  |                 Hierarchy.and hp hq =>
    hAnd _ _ _ hp hq
      (sigma₁_induction hVerum hFalsum hRel hNRel hAnd hOr hBall hExs hOperator _ _ hp)
      (sigma₁_induction hVerum hFalsum hRel hNRel hAnd hOr hBall hExs hOperator _ _ hq)
  |                  Hierarchy.or hp hq =>
    hOr _ _ _ hp hq
      (sigma₁_induction hVerum hFalsum hRel hNRel hAnd hOr hBall hExs hOperator _ _ hp)
      (sigma₁_induction hVerum hFalsum hRel hNRel hAnd hOr hBall hExs hOperator _ _ hq)
  |                Hierarchy.ball pt hp => by
    rcases Rew.positive_iff.mp pt with ⟨t, rfl⟩
    exact hBall _ t _ hp
      (sigma₁_induction hVerum hFalsum hRel hNRel hAnd hOr hBall hExs hOperator _ _ hp)
  |                 Hierarchy.bexs pt hp => by
    apply hExs
    · simp [hp]
    · rcases Rew.positive_iff.mp pt with ⟨t, rfl⟩
      apply hAnd _ _ _ (by simp) hp (hOperator _ t)
        (sigma₁_induction hVerum hFalsum hRel hNRel hAnd hOr hBall hExs hOperator _ _ hp)
  |         Hierarchy.sigma (φ := φ) hp =>
    have : Hierarchy R 𝚺 1 φ := hp.accum _
    hExs _ _ this
      (sigma₁_induction hVerum hFalsum hRel hNRel hAnd hOr hBall hExs hOperator _ _ this)
  |                    Hierarchy.exs hp =>
    hExs _ _ hp
      (sigma₁_induction hVerum hFalsum hRel hNRel hAnd hOr hBall hExs hOperator _ _ hp)

end Hierarchy

end OperatorHierarchy

end LO.FirstOrder

end
