import Logic.FirstOrder.Arith.Basic

namespace LO

namespace FirstOrder

variable {L : Language} [L.LT] {μ : Type v}

namespace Arith

inductive VType := | sigma | pi

namespace VType

notation "Σ" => sigma
notation "Π" => pi

def alt : VType → VType
  | Σ => Π
  | Π => Σ

@[simp] lemma alt_sigma : Σ.alt = Π := rfl

@[simp] lemma alt_pi : Π.alt = Σ := rfl

@[simp] lemma alt_alt (b : VType) : b.alt.alt = b := by rcases b <;> simp

end VType

inductive Hierarchy : VType → ℕ → {n : ℕ} → Semiformula L μ n → Prop
  | verum (b s n)                                : Hierarchy b s (⊤ : Semiformula L μ n)
  | falsum (b s n)                               : Hierarchy b s (⊥ : Semiformula L μ n)
  | rel (b s) {k} (r : L.Rel k) (v)              : Hierarchy b s (Semiformula.rel r v)
  | nrel (b s) {k} (r : L.Rel k) (v)             : Hierarchy b s (Semiformula.nrel r v)
  | and {b s n} {p q : Semiformula L μ n}        : Hierarchy b s p → Hierarchy b s q → Hierarchy b s (p ⋏ q)
  | or {b s n} {p q : Semiformula L μ n}         : Hierarchy b s p → Hierarchy b s q → Hierarchy b s (p ⋎ q)
  | ball {b s n} {p : Semiformula L μ (n + 1)} {t : Semiterm L μ (n + 1)} :
    t.Positive → Hierarchy b s p → Hierarchy b s (∀[“#0 < !!t”] p)
  | bex {b s n} {p : Semiformula L μ (n + 1)} {t : Semiterm L μ (n + 1)} :
    t.Positive → Hierarchy b s p → Hierarchy b s (∃[“#0 < !!t”] p)
  | ex {s n} {p : Semiformula L μ (n + 1)}       : Hierarchy Σ (s + 1) p → Hierarchy Σ (s + 1) (∃' p)
  | all {s n} {p : Semiformula L μ (n + 1)}      : Hierarchy Π (s + 1) p → Hierarchy Π (s + 1) (∀' p)
  | sigma {s n} {p : Semiformula L μ (n + 1)}    : Hierarchy Π s p → Hierarchy Σ (s + 1) (∃' p)
  | pi {s n} {p : Semiformula L μ (n + 1)}       : Hierarchy Σ s p → Hierarchy Π (s + 1) (∀' p)
  | accum {b} (b') {s n} {p : Semiformula L μ n} : Hierarchy b s p → Hierarchy b' (s + 1) p

attribute [simp] Hierarchy.verum Hierarchy.falsum Hierarchy.rel Hierarchy.nrel

namespace Hierarchy

lemma strict_mono {s s' : ℕ} {p : Semiformula L μ n} (hp : Hierarchy b s p) (h : s < s') (b') : Hierarchy b' s' p := by
  have : ∀ d, Hierarchy b' (s + d + 1) p := by
    intro d
    induction' d with s ih
    · simpa using hp.accum b'
    · simpa [Nat.succ_eq_add_one, ←add_assoc] using ih.accum b'
  simpa [show s + (s' - Nat.succ s) + 1 = s' from by simpa [Nat.succ_add] using Nat.add_sub_of_le h] using this (s' - s.succ)

lemma mono {b} {s s' : ℕ} {p : Semiformula L μ n} (hp : Hierarchy b s p) (h : s ≤ s') : Hierarchy b s' p := by
  rcases Nat.lt_or_eq_of_le h with (lt | rfl)
  · exact hp.strict_mono lt b
  · assumption

@[simp] lemma and_iff {p q : Semiformula L μ n} : Hierarchy b s (p ⋏ q) ↔ Hierarchy b s p ∧ Hierarchy b s q :=
  ⟨by generalize hr : p ⋏ q = r
      intro H
      induction H <;> try simp [LogicSymbol.ball, LogicSymbol.bex] at hr
      case and =>
        rcases hr with ⟨rfl, rfl⟩
        constructor <;> assumption
      case accum ih =>
        rcases hr with rfl
        exact ⟨(ih rfl).1.accum _, (ih rfl).2.accum _⟩,
   by rintro ⟨hp, hq⟩; exact Hierarchy.and hp hq⟩

@[simp] lemma or_iff {p q : Semiformula L μ n} : Hierarchy b s (p ⋎ q) ↔ Hierarchy b s p ∧ Hierarchy b s q :=
  ⟨by generalize hr : p ⋎ q = r
      intro H
      induction H <;> try simp [LogicSymbol.ball, LogicSymbol.bex] at hr
      case or =>
        rcases hr with ⟨rfl, rfl⟩
        constructor <;> assumption
      case accum ih =>
        rcases hr with rfl
        exact ⟨(ih rfl).1.accum _, (ih rfl).2.accum _⟩,
      by rintro ⟨hp, hq⟩; exact Hierarchy.or hp hq⟩

@[simp] lemma conj_iff {p : Fin m → Semiformula L μ n} :
    Hierarchy b s (Matrix.conj p) ↔ ∀ i, Hierarchy b s (p i) := by
  induction m <;> simp[Matrix.conj, Matrix.vecTail, *]
  · exact ⟨by rintro ⟨hz, hs⟩ i; cases i using Fin.cases <;> simp[*],
           by intro h; exact ⟨h 0, fun _ => h _⟩⟩

section

variable {L : Language} [L.Eq] [L.LT]

@[simp] lemma equal {t u : Semiterm L μ n} : Hierarchy b s “!!t = !!u” := by
  simp[Semiformula.Operator.operator, Matrix.fun_eq_vec₂,
    Semiformula.Operator.Eq.sentence_eq]

@[simp] lemma lt {t u : Semiterm L μ n} : Hierarchy b s “!!t < !!u” := by
  simp[Semiformula.Operator.operator, Matrix.fun_eq_vec₂,
    Semiformula.Operator.Eq.sentence_eq, Semiformula.Operator.LT.sentence_eq]

@[simp] lemma le {t u : Semiterm L μ n} : Hierarchy b s “!!t ≤ !!u” := by
  simp[Semiformula.Operator.operator, Matrix.fun_eq_vec₂,
    Semiformula.Operator.Eq.sentence_eq, Semiformula.Operator.LT.sentence_eq,
    Semiformula.Operator.LE.sentence_eq]

end

lemma zero_eq_alt {p : Semiformula L μ n} : Hierarchy b 0 p → Hierarchy b.alt 0 p := by
  generalize hz : 0 = z
  rw[eq_comm] at hz
  intro h
  induction h <;> try simp at hz ⊢
  case and _ _ ihp ihq =>
    exact ⟨ihp hz, ihq hz⟩
  case or _ _ ihp ihq => exact ⟨ihp hz, ihq hz⟩
  case ball pos _ ih => exact ball pos (ih hz)
  case bex pos _ ih => exact bex pos (ih hz)

lemma pi_zero_iff_sigma_zero {p : Semiformula L μ n} : Hierarchy Π 0 p ↔ Hierarchy Σ 0 p := ⟨zero_eq_alt, zero_eq_alt⟩

lemma zero_iff_sigma_zero {p : Semiformula L μ n} : Hierarchy b 0 p ↔ Hierarchy Σ 0 p := by rcases b <;> simp[pi_zero_iff_sigma_zero]

@[simp] lemma alt_zero_iff_zero {p : Semiformula L μ n} : Hierarchy b.alt 0 p ↔ Hierarchy b 0 p := by rcases b <;> simp[pi_zero_iff_sigma_zero]

lemma neg {p : Semiformula L μ n} : Hierarchy b s p → Hierarchy b.alt s (~p) := by
  intro h; induction h <;> try simp[*]
  case bex pos _ ih => exact ball pos ih
  case ball pos _ ih => exact bex pos ih
  case ex ih => exact all ih
  case all ih => exact ex ih
  case sigma ih => exact pi ih
  case pi ih => exact sigma ih
  case accum ih => exact ih.accum _

@[simp] lemma neg_iff {p : Semiformula L μ n} : Hierarchy b s (~p) ↔ Hierarchy b.alt s p :=
  ⟨fun h => by simpa using neg h, fun h => by simpa using neg h⟩

@[simp] lemma imp_iff {p q : Semiformula L μ n} : Hierarchy b s (p ⟶ q) ↔ (Hierarchy b.alt s p ∧ Hierarchy b s q) := by simp[Semiformula.imp_eq]

@[simp] lemma ball_iff {b s n} {p : Semiformula L μ (n + 1)} {t : Semiterm L μ (n + 1)} (ht : t.Positive) :
    Hierarchy b s (∀[“#0 < !!t”] p) ↔ Hierarchy b s p :=
  ⟨by generalize hq : (∀[“#0 < !!t”] p) = q
      intro H
      induction H <;> try simp [LogicSymbol.ball, LogicSymbol.bex] at hq
      case ball p t pt hp ih =>
        rcases hq with ⟨rfl, rfl⟩
        assumption
      case all hp ih =>
        rcases hq with rfl
        simpa using hp
      case pi s _ _ hp ih =>
        rcases hq with rfl
        exact (show Hierarchy Σ s p from by simpa using hp).accum _
      case accum hp ih =>
        rcases hq with rfl
        simp at hp
        exact (ih ht rfl).accum _,
   by intro hp; exact hp.ball ht⟩

@[simp] lemma bex_iff {b s n} {p : Semiformula L μ (n + 1)} {t : Semiterm L μ (n + 1)} (ht : t.Positive) :
    Hierarchy b s (∃[“#0 < !!t”] p) ↔ Hierarchy b s p :=
  ⟨by generalize hq : (∃[“#0 < !!t”] p) = q
      intro H
      induction H <;> try simp [LogicSymbol.ball, LogicSymbol.bex] at hq
      case bex p t pt hp ih =>
        rcases hq with ⟨rfl, rfl⟩
        assumption
      case ex hp ih =>
        rcases hq with rfl
        simpa using hp
      case sigma s _ _ hp ih =>
        rcases hq with rfl
        exact (show Hierarchy Π s p from by simpa using hp).accum _
      case accum hp ih =>
        rcases hq with rfl
        simp at hp
        exact (ih ht rfl).accum _,
   by intro hp; exact hp.bex ht⟩

lemma rew (ω : Rew L μ₁ n₁ μ₂ n₂) {p : Semiformula L μ₁ n₁} : Hierarchy b s p → Hierarchy b s (ω.hom p) := by
  intro h; induction h generalizing n₂ <;> try simp [*, Rew.rel,Rew.nrel]
  case ex ih => exact ex (ih _)
  case all ih => exact all (ih _)
  case sigma ih => exact sigma (ih _)
  case pi ih => exact pi (ih _)
  case accum ih => exact (ih ω).accum _

@[simp] lemma rew_iff {ω : Rew L μ₁ n₁ μ₂ n₂} {p : Semiformula L μ₁ n₁} :
    Hierarchy b s (ω.hom p) ↔ Hierarchy b s p := by
  constructor
  · generalize eq : ω.hom p = q
    intro hq
    induction hq generalizing p n₁
      <;> try simp [Rew.eq_rel_iff, Rew.eq_nrel_iff, Rew.eq_ball_iff, Rew.eq_bex_iff, Rew.eq_all_iff, Rew.eq_ex_iff] at eq
    case verum => rcases eq with rfl; simp
    case falsum => rcases eq with rfl; simp
    case rel => rcases eq with ⟨v', rfl, rfl⟩; simp
    case nrel => rcases eq with ⟨v', rfl, rfl⟩; simp
    case and ihp ihq =>
      rcases eq with ⟨p₁, rfl, p₂, rfl, rfl⟩
      simpa using ⟨ihp rfl, ihq rfl⟩
    case or ihp ihq =>
      rcases eq with ⟨p₁, rfl, p₂, rfl, rfl⟩
      simpa using ⟨ihp rfl, ihq rfl⟩
    case ball pos _ ih =>
      simp [Rew.eq_lt_iff] at eq
      rcases eq with ⟨hp, ⟨u, rfl, s, hs, rfl⟩, p, rfl, rfl⟩
      simpa [show u.Positive from by simpa using pos] using ih rfl
    case bex pos _ ih =>
      simp [Rew.eq_lt_iff] at eq
      rcases eq with ⟨hp, ⟨u, rfl, s, hs, rfl⟩, p, rfl, rfl⟩
      simpa [show u.Positive from by simpa using pos] using ih rfl
    case all ih =>
      rcases eq with ⟨p, rfl, rfl⟩
      exact (ih rfl).all
    case ex ih =>
      rcases eq with ⟨p, rfl, rfl⟩
      exact (ih rfl).ex
    case pi ih =>
      rcases eq with ⟨p, rfl, rfl⟩
      exact (ih rfl).pi
    case sigma ih =>
      rcases eq with ⟨p, rfl, rfl⟩
      exact (ih rfl).sigma
    case accum ih =>
      rcases eq with rfl
      exact (ih rfl).accum _
  · exact rew _

lemma exClosure : {n : ℕ} → {p : Semiformula L μ n} → Hierarchy Σ (s + 1) p → Hierarchy Σ (s + 1) (exClosure p)
  | 0,     _, hp => hp
  | n + 1, p, hp => by simpa using exClosure (hp.ex)

instance : LogicSymbol.AndOrClosed (Hierarchy b s : Semiformula L μ k → Prop) where
  verum := verum _ _ _
  falsum := falsum _ _ _
  and := and
  or := or

instance : LogicSymbol.Closed (Hierarchy b 0 : Semiformula L μ k → Prop) where
  not := by simp[neg_iff]
  imply := by simp[Semiformula.imp_eq, neg_iff]; intro p q hp hq; simp[*]


section definability

variable {M} [Structure ℒₒᵣ M]

abbrev Definable (b : VType) (s : ℕ) {k} (t : (Fin k → M) → Prop) : Prop :=
  FirstOrder.Definable (Hierarchy b s : Semisentence ℒₒᵣ k → Prop) t

abbrev DefinablePred (b : VType) (s : ℕ) (P : M → Prop) : Prop :=
  Definable b s (k := 1) λ v ↦ P (Matrix.vecHead v)

abbrev DefinableRel (b : VType) (s : ℕ) (R : M → M → Prop) : Prop :=
  Definable b s (k := 2) λ v ↦ R (v 0) (v 1)

abbrev SigmaDefinablePred (s : ℕ) (P : M → Prop) : Prop := DefinablePred Σ s P

notation "Σᴬ[" s "]-Predicate" => SigmaDefinablePred s

abbrev PiDefinablePred (s : ℕ) (t : Set M) : Prop := DefinablePred Π s t

notation "Πᴬ[" s "]-Predicate" => PiDefinablePred s

abbrev SigmaDefinableRel (s : ℕ) (P : M → M → Prop) : Prop := DefinableRel Σ s P

notation "Σᴬ[" s "]-Relation" => SigmaDefinableRel s

abbrev PiDefinableRel (s : ℕ) (t : Set M) : Prop := DefinablePred Π s t

notation "Πᴬ[" s "]-Relation" => PiDefinableRel s

abbrev DefinableFunction (b : VType) (s : ℕ) {k} (f : (Fin k → M) → M) : Prop :=
  FirstOrder.DefinableFunction (Hierarchy b s : Semisentence ℒₒᵣ (k + 1) → Prop) f

abbrev DefinableFunction₁ (b : VType) (s : ℕ) (f : M → M) : Prop :=
  DefinableFunction b s (k := 1) (fun v => f (Matrix.vecHead v))

abbrev DefinableFunction₂ (b : VType) (s : ℕ) (f : M → M → M) : Prop :=
  DefinableFunction b s (k := 2) (fun v => f (v 0) (v 1))

abbrev SigmaDefinableFunction₁ (s : ℕ) (f : M → M) : Prop := DefinableFunction₁ Σ s f

notation "Σᴬ[" s "]-Function₁" => SigmaDefinableFunction₁ s

abbrev PiDefinableFunction₁ (s : ℕ) (f : M → M) : Prop := DefinableFunction₁ Π s f

notation "Πᴬ[" s "]-Function₁" => PiDefinableFunction₁ s

abbrev SigmaDefinableFunction₂ (s : ℕ) (f : M → M → M) : Prop := DefinableFunction₂ Σ s f

notation "Σᴬ[" s "]-Function₂" => SigmaDefinableFunction₂ s

abbrev PiDefinableFunction₂ (s : ℕ) (f : M → M → M) : Prop := DefinableFunction₂ Π s f

notation "Πᴬ[" s "]-Function₂" => PiDefinableFunction₂ s

variable {f : M → M}

end definability

end Hierarchy

variable {L : Language} [(k : ℕ) → DecidableEq (L.Func k)] [(k : ℕ) → DecidableEq (L.Rel k)]
  [L.LT] [Structure L ℕ]

abbrev SigmaOneSound (T : Theory L) := Sound T (Hierarchy Σ 1)

lemma consistent_of_sigmaOneSound (T : Theory L) [SigmaOneSound T] :
    System.Consistent T := consistent_of_sound T (Hierarchy Σ 1) (by simp)

end Arith

end FirstOrder

end LO
