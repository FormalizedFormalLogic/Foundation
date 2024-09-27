import Logic.FirstOrder.Arith.Basic

namespace LO

namespace FirstOrder

variable {L : Language} [L.LT] {ξ : Type v}

namespace Arith

inductive Hierarchy : Polarity → ℕ → {n : ℕ} → Semiformula L ξ n → Prop
  | verum (Γ s n)                                    : Hierarchy Γ s (⊤ : Semiformula L ξ n)
  | falsum (Γ s n)                                   : Hierarchy Γ s (⊥ : Semiformula L ξ n)
  | rel (Γ s) {k} (r : L.Rel k) (v)                  : Hierarchy Γ s (Semiformula.rel r v)
  | nrel (Γ s) {k} (r : L.Rel k) (v)                 : Hierarchy Γ s (Semiformula.nrel r v)
  | and {Γ s n} {p q : Semiformula L ξ n}            : Hierarchy Γ s p → Hierarchy Γ s q → Hierarchy Γ s (p ⋏ q)
  | or {Γ s n} {p q : Semiformula L ξ n}             : Hierarchy Γ s p → Hierarchy Γ s q → Hierarchy Γ s (p ⋎ q)
  | ball {Γ s n} {p : Semiformula L ξ (n + 1)} {t : Semiterm L ξ (n + 1)} :
    t.Positive → Hierarchy Γ s p → Hierarchy Γ s (∀[“x. x < !!t”] p)
  | bex {Γ s n} {p : Semiformula L ξ (n + 1)} {t : Semiterm L ξ (n + 1)} :
    t.Positive → Hierarchy Γ s p → Hierarchy Γ s (∃[“x. x < !!t”] p)
  | ex {s n} {p : Semiformula L ξ (n + 1)}           : Hierarchy 𝚺 (s + 1) p → Hierarchy 𝚺 (s + 1) (∃' p)
  | all {s n} {p : Semiformula L ξ (n + 1)}          : Hierarchy 𝚷 (s + 1) p → Hierarchy 𝚷 (s + 1) (∀' p)
  | sigma {s n} {p : Semiformula L ξ (n + 1)}        : Hierarchy 𝚷 s p → Hierarchy 𝚺 (s + 1) (∃' p)
  | pi {s n} {p : Semiformula L ξ (n + 1)}           : Hierarchy 𝚺 s p → Hierarchy 𝚷 (s + 1) (∀' p)
  | dummy_sigma {s n} {p : Semiformula L ξ (n + 1)}  : Hierarchy 𝚷 (s + 1) p → Hierarchy 𝚺 (s + 1 + 1) (∀' p)
  | dummy_pi {s n} {p : Semiformula L ξ (n + 1)}     : Hierarchy 𝚺 (s + 1) p → Hierarchy 𝚷 (s + 1 + 1) (∃' p)

def DeltaZero (p : Semiformula L ξ n) : Prop := Hierarchy 𝚺 0 p

attribute [simp] Hierarchy.verum Hierarchy.falsum Hierarchy.rel Hierarchy.nrel

namespace Hierarchy

@[simp] lemma and_iff {p q : Semiformula L ξ n} : Hierarchy Γ s (p ⋏ q) ↔ Hierarchy Γ s p ∧ Hierarchy Γ s q :=
  ⟨by generalize hr : p ⋏ q = r
      intro H
      induction H <;> try simp [LogicalConnective.ball, LogicalConnective.bex] at hr
      case and =>
        rcases hr with ⟨rfl, rfl⟩
        constructor <;> assumption,
   by rintro ⟨hp, hq⟩; exact Hierarchy.and hp hq⟩

@[simp] lemma or_iff {p q : Semiformula L ξ n} : Hierarchy Γ s (p ⋎ q) ↔ Hierarchy Γ s p ∧ Hierarchy Γ s q :=
  ⟨by generalize hr : p ⋎ q = r
      intro H
      induction H <;> try simp [LogicalConnective.ball, LogicalConnective.bex] at hr
      case or =>
        rcases hr with ⟨rfl, rfl⟩
        constructor <;> assumption,
      by rintro ⟨hp, hq⟩; exact Hierarchy.or hp hq⟩

@[simp] lemma conj_iff {p : Fin m → Semiformula L ξ n} :
    Hierarchy Γ s (Matrix.conj p) ↔ ∀ i, Hierarchy Γ s (p i) := by
  induction m <;> simp[Matrix.conj, Matrix.vecTail, *]
  · exact ⟨by rintro ⟨hz, hs⟩ i; cases i using Fin.cases <;> simp[*],
           by intro h; exact ⟨h 0, fun _ => h _⟩⟩

lemma zero_eq_alt {p : Semiformula L ξ n} : Hierarchy Γ 0 p → Hierarchy Γ.alt 0 p := by
  generalize hz : 0 = z
  rw[eq_comm] at hz
  intro h
  induction h <;> try simp at hz ⊢
  case and _ _ ihp ihq =>
    exact ⟨ihp hz, ihq hz⟩
  case or _ _ ihp ihq => exact ⟨ihp hz, ihq hz⟩
  case ball pos _ ih => exact ball pos (ih hz)
  case bex pos _ ih => exact bex pos (ih hz)

lemma pi_zero_iff_sigma_zero {p : Semiformula L ξ n} : Hierarchy 𝚷 0 p ↔ Hierarchy 𝚺 0 p := ⟨zero_eq_alt, zero_eq_alt⟩

lemma zero_iff {Γ Γ'} {p : Semiformula L ξ n} : Hierarchy Γ 0 p ↔ Hierarchy Γ' 0 p := by rcases Γ <;> rcases Γ' <;> simp[pi_zero_iff_sigma_zero]

lemma zero_iff_delta_zero {Γ} {p : Semiformula L ξ n} : Hierarchy Γ 0 p ↔ DeltaZero p := by
  simp[DeltaZero, pi_zero_iff_sigma_zero]; apply zero_iff

@[simp] lemma alt_zero_iff_zero {p : Semiformula L ξ n} : Hierarchy Γ.alt 0 p ↔ Hierarchy Γ 0 p := by rcases Γ <;> simp[pi_zero_iff_sigma_zero]

lemma accum : ∀ {Γ} {s : ℕ} {p : Semiformula L ξ n}, Hierarchy Γ s p → ∀ Γ', Hierarchy Γ' (s + 1) p
  | _, _, _, verum _ _ _,    _ => verum _ _ _
  | _, _, _, falsum _ _ _,   _ => falsum _ _ _
  | _, _, _, rel _ _ r v,    _ => rel _ _ r v
  | _, _, _, nrel _ _ r v,   _ => nrel _ _ r v
  | _, _, _, and hp hq,      _ => and (hp.accum _) (hq.accum _)
  | _, _, _, or hp hq,       _ => or (hp.accum _) (hq.accum _)
  | _, _, _, ball pos hp,    Γ => ball pos (hp.accum _)
  | _, _, _, bex pos hp,     Γ => bex pos (hp.accum _)
  | _, _, _, all hp,         Γ => by
    cases Γ
    · exact hp.dummy_sigma
    · exact (hp.accum 𝚷).all
  | _, _, _, ex hp,          Γ => by
    cases Γ
    · exact (hp.accum 𝚺).ex
    · exact hp.dummy_pi
  | _, _, _, sigma hp,       Γ => by
    cases Γ
    · exact ((hp.accum 𝚺).accum 𝚺).ex
    · exact (hp.accum 𝚺).dummy_pi
  | _, _, _, pi hp,          Γ => by
    cases Γ
    · exact (hp.accum 𝚷).dummy_sigma
    · exact ((hp.accum 𝚷).accum 𝚷).all
  | _, _, _, dummy_sigma hp, Γ => by
    cases Γ
    · exact (hp.accum 𝚷).dummy_sigma
    · exact ((hp.accum 𝚷).accum 𝚷).all
  | _, _, _, dummy_pi hp,    Γ => by
    cases Γ
    · exact ((hp.accum 𝚺).accum 𝚺).ex
    · exact (hp.accum 𝚺).dummy_pi

lemma strict_mono {Γ s} {p : Semiformula L ξ n} (hp : Hierarchy Γ s p) (Γ') {s'} (h : s < s') : Hierarchy Γ' s' p := by
  have : ∀ d, Hierarchy Γ' (s + d + 1) p := by
    intro d
    induction' d with s ih
    · simpa using hp.accum Γ'
    · simpa only [Nat.add_succ, add_zero] using ih.accum _
  simpa [show s + (s' - s.succ) + 1 = s' from by simpa [Nat.succ_add] using Nat.add_sub_of_le h] using this (s' - s.succ)

lemma mono {Γ} {s s' : ℕ} {p : Semiformula L ξ n} (hp : Hierarchy Γ s p) (h : s ≤ s') : Hierarchy Γ s' p := by
  rcases Nat.lt_or_eq_of_le h with (lt | rfl)
  · exact hp.strict_mono Γ lt
  · assumption

lemma of_zero {b b'} {s : ℕ} {p : Semiformula L ξ n} (hp : Hierarchy b 0 p) : Hierarchy b' s p := by
  rcases Nat.eq_or_lt_of_le (Nat.zero_le s) with (rfl | pos)
  · exact zero_iff.mp hp
  · exact strict_mono hp b' pos

section

variable {L : Language} [L.Eq] [L.LT]

@[simp] lemma equal {t u : Semiterm L ξ n} : Hierarchy Γ s “!!t = !!u” := by
  simp[Semiformula.Operator.operator, Matrix.fun_eq_vec₂,
    Semiformula.Operator.Eq.sentence_eq]

@[simp] lemma lt {t u : Semiterm L ξ n} : Hierarchy Γ s “!!t < !!u” := by
  simp[Semiformula.Operator.operator, Matrix.fun_eq_vec₂,
    Semiformula.Operator.Eq.sentence_eq, Semiformula.Operator.LT.sentence_eq]

@[simp] lemma le {t u : Semiterm L ξ n} : Hierarchy Γ s “!!t ≤ !!u” := by
  simp[Semiformula.Operator.operator, Matrix.fun_eq_vec₂,
    Semiformula.Operator.Eq.sentence_eq, Semiformula.Operator.LT.sentence_eq,
    Semiformula.Operator.LE.sentence_eq]

end

lemma neg {p : Semiformula L ξ n} : Hierarchy Γ s p → Hierarchy Γ.alt s (∼p) := by
  intro h; induction h <;> try simp[*]
  case bex pos _ ih => exact ball pos ih
  case ball pos _ ih => exact bex pos ih
  case ex ih => exact all ih
  case all ih => exact ex ih
  case sigma ih => exact pi ih
  case pi ih => exact sigma ih
  case dummy_pi ih => exact dummy_sigma ih
  case dummy_sigma ih => exact dummy_pi ih

@[simp] lemma neg_iff {p : Semiformula L ξ n} : Hierarchy Γ s (∼p) ↔ Hierarchy Γ.alt s p :=
  ⟨fun h => by simpa using neg h, fun h => by simpa using neg h⟩

@[simp] lemma imp_iff {p q : Semiformula L ξ n} : Hierarchy Γ s (p ➝ q) ↔ (Hierarchy Γ.alt s p ∧ Hierarchy Γ s q) := by simp[Semiformula.imp_eq]

@[simp] lemma ball_iff {Γ s n} {p : Semiformula L ξ (n + 1)} {t : Semiterm L ξ (n + 1)} (ht : t.Positive) :
    Hierarchy Γ s (∀[“x. x < !!t”] p) ↔ Hierarchy Γ s p :=
  ⟨by generalize hq : (∀[“x. x < !!t”] p) = q
      intro H
      induction H <;> try simp [LogicalConnective.ball, LogicalConnective.bex] at hq
      case ball p t pt hp ih =>
        rcases hq with ⟨rfl, rfl⟩
        assumption
      case all hp ih =>
        rcases hq with rfl
        simpa using hp
      case pi s _ _ hp ih =>
        rcases hq with rfl
        exact (show Hierarchy 𝚺 s p from by simpa using hp).accum _
      case dummy_sigma hp _ =>
        rcases hq with rfl
        simp at hp
        exact hp.accum _,
   by intro hp; exact hp.ball ht⟩

@[simp] lemma bex_iff {Γ s n} {p : Semiformula L ξ (n + 1)} {t : Semiterm L ξ (n + 1)} (ht : t.Positive) :
    Hierarchy Γ s (∃[“x. x < !!t”] p) ↔ Hierarchy Γ s p :=
  ⟨by generalize hq : (∃[“x. x < !!t”] p) = q
      intro H
      induction H <;> try simp [LogicalConnective.ball, LogicalConnective.bex] at hq
      case bex p t pt hp ih =>
        rcases hq with ⟨rfl, rfl⟩
        assumption
      case ex hp ih =>
        rcases hq with rfl
        simpa using hp
      case sigma s _ _ hp ih =>
        rcases hq with rfl
        exact (show Hierarchy 𝚷 s p from by simpa using hp).accum _
      case dummy_pi hp _ =>
        rcases hq with rfl
        simp at hp
        exact hp.accum _,
   by intro hp; exact hp.bex ht⟩

@[simp] lemma ballLT_iff {Γ s n} {p : Semiformula L ξ (n + 1)} {t : Semiterm L ξ n} :
    Hierarchy Γ s (p.ballLT t) ↔ Hierarchy Γ s p := by simp [Semiformula.ballLT]

@[simp] lemma bexLT_iff {Γ s n} {p : Semiformula L ξ (n + 1)} {t : Semiterm L ξ n} :
    Hierarchy Γ s (p.bexLT t) ↔ Hierarchy Γ s p := by simp [Semiformula.bexLT]

@[simp] lemma ballLTSucc_iff [L.Zero] [L.One] [L.Add] {Γ s n} {p : Semiformula L ξ (n + 1)} {t : Semiterm L ξ n} :
    Hierarchy Γ s (p.ballLTSucc t) ↔ Hierarchy Γ s p := by simp [Semiformula.ballLTSucc]

@[simp] lemma bexLTSucc_iff [L.Zero] [L.One] [L.Add] {Γ s n} {p : Semiformula L ξ (n + 1)} {t : Semiterm L ξ n} :
    Hierarchy Γ s (p.bexLTSucc t) ↔ Hierarchy Γ s p := by simp [Semiformula.bexLTSucc]

lemma pi_of_pi_all {p : Semiformula L ξ (n + 1)} : Hierarchy 𝚷 s (∀' p) → Hierarchy 𝚷 s p := by
  generalize hr : ∀' p = r
  generalize hb : (𝚷 : Polarity) = Γ
  intro H
  cases H <;> try simp [LogicalConnective.ball, LogicalConnective.bex] at hr
  case ball => rcases hr with rfl; simpa
  case all => rcases hr with rfl; simpa
  case pi hp => rcases hr with rfl; exact hp.accum _
  case dummy_sigma hp => rcases hr with rfl; exact hp.accum _

@[simp] lemma all_iff {p : Semiformula L ξ (n + 1)} : Hierarchy 𝚷 (s + 1) (∀' p) ↔ Hierarchy 𝚷 (s + 1) p :=
  ⟨pi_of_pi_all, all⟩

lemma sigma_of_sigma_ex {p : Semiformula L ξ (n + 1)} : Hierarchy 𝚺 s (∃' p) → Hierarchy 𝚺 s p := by
  generalize hr : ∃' p = r
  generalize hb : (𝚺 : Polarity) = Γ
  intro H
  cases H <;> try simp [LogicalConnective.ball, LogicalConnective.bex] at hr
  case bex => rcases hr with rfl; simpa
  case ex => rcases hr with rfl; simpa
  case sigma hp => rcases hr with rfl; exact hp.accum _
  case dummy_pi hp => rcases hr with rfl; exact hp.accum _

@[simp] lemma sigma_iff {p : Semiformula L ξ (n + 1)} : Hierarchy 𝚺 (s + 1) (∃' p) ↔ Hierarchy 𝚺 (s + 1) p :=
  ⟨sigma_of_sigma_ex, ex⟩

lemma rew (ω : Rew L ξ₁ n₁ ξ₂ n₂) {p : Semiformula L ξ₁ n₁} : Hierarchy Γ s p → Hierarchy Γ s (ω.hom p) := by
  intro h; induction h generalizing n₂ <;> try simp [*, Rew.rel,Rew.nrel]
  case sigma ih => exact (ih _).accum _
  case pi ih => exact (ih _).accum _
  case dummy_pi ih => exact (ih _).dummy_pi
  case dummy_sigma ih => exact (ih _).dummy_sigma

@[simp] lemma rew_iff {ω : Rew L ξ₁ n₁ ξ₂ n₂} {p : Semiformula L ξ₁ n₁} :
    Hierarchy Γ s (ω.hom p) ↔ Hierarchy Γ s p := by
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
    case dummy_sigma ih =>
      rcases eq with ⟨p, rfl, rfl⟩
      exact (ih rfl).dummy_sigma
    case dummy_pi ih =>
      rcases eq with ⟨p, rfl, rfl⟩
      exact (ih rfl).dummy_pi
  · exact rew _

lemma exClosure : {n : ℕ} → {p : Semiformula L ξ n} → Hierarchy 𝚺 (s + 1) p → Hierarchy 𝚺 (s + 1) (exClosure p)
  | 0,     _, hp => hp
  | n + 1, p, hp => by simpa using exClosure (hp.ex)

instance : LogicalConnective.AndOrClosed (Hierarchy Γ s : Semiformula L ξ k → Prop) where
  verum := verum _ _ _
  falsum := falsum _ _ _
  and := and
  or := or

instance : LogicalConnective.Closed (Hierarchy Γ 0 : Semiformula L ξ k → Prop) where
  not := by simp[neg_iff]
  imply := by simp[Semiformula.imp_eq, neg_iff]; intro p q hp hq; simp[*]

lemma of_open {p : Semiformula L ξ n} : p.Open → Hierarchy Γ s p := by
  induction p using Semiformula.rec' <;> simp
  case hand ihp ihq => intro hp hq; exact ⟨ihp hp, ihq hq⟩
  case hor ihp ihq => intro hp hq; exact ⟨ihp hp, ihq hq⟩

variable {L : Language} [L.ORing]

lemma oringEmb {p : Semiformula ℒₒᵣ ξ n} : Hierarchy Γ s p → Hierarchy Γ s (Semiformula.lMap (Language.oringEmb : ℒₒᵣ →ᵥ L) p) := by
  intro h; induction h <;> try simp [*, Semiformula.lMap_rel, Semiformula.lMap_nrel]
  case sigma ih => exact ih.accum _
  case pi ih => exact ih.accum _
  case dummy_pi ih => exact ih.dummy_pi
  case dummy_sigma ih => exact ih.dummy_sigma

lemma iff_iff {p q : Semiformula L ξ n} :
    Hierarchy b s (p ⭤ q) ↔ (Hierarchy b s p ∧ Hierarchy b.alt s p ∧ Hierarchy b s q ∧ Hierarchy b.alt s q) := by
  simp[Semiformula.iff_eq]; tauto

@[simp] lemma iff_iff₀ {p q : Semiformula L ξ n} :
    Hierarchy b 0 (p ⭤ q) ↔ (Hierarchy b 0 p ∧ Hierarchy b 0 q) := by
  simp[Semiformula.iff_eq]; tauto

@[simp] lemma matrix_conj_iff {b s n} {p : Fin m → Semiformula L ξ n} :
    Hierarchy b s (Matrix.conj fun j ↦ p j) ↔ ∀ j, Hierarchy b s (p j) := by
  cases m <;> simp

lemma remove_forall {p : Semiformula L ξ (n + 1)} : Hierarchy b s (∀' p) → Hierarchy b s p := by
  intro h; rcases h
  case ball => simpa
  case all => assumption
  case pi h => exact h.accum _
  case dummy_sigma h => exact h.accum _

lemma remove_exists {p : Semiformula L ξ (n + 1)} : Hierarchy b s (∃' p) → Hierarchy b s p := by
  intro h; rcases h
  case bex => simpa
  case ex => assumption
  case sigma h => exact h.accum _
  case dummy_pi h => exact h.accum _

end Hierarchy

section

variable {L : Language} [(k : ℕ) → DecidableEq (L.Func k)] [(k : ℕ) → DecidableEq (L.Rel k)]
  [L.LT] [Structure L ℕ]

abbrev Sigma1Sound (T : Theory L) := SoundOn T (Hierarchy 𝚺 1)

lemma consistent_of_sigma1Sound (T : Theory L) [Sigma1Sound T] :
    System.Consistent T := consistent_of_sound T (Hierarchy 𝚺 1) (by simp [Set.mem_def])

end

section LOR

lemma sigma₁_induction {P : (n : ℕ) → Semiformula ℒₒᵣ ξ n → Prop}
    (hVerum : ∀ n, P n ⊤)
    (hFalsum : ∀ n, P n ⊥)
    (hEQ : ∀ n t₁ t₂, P n (.rel Language.Eq.eq ![t₁, t₂]))
    (hNEQ : ∀ n t₁ t₂, P n (.nrel Language.Eq.eq ![t₁, t₂]))
    (hLT : ∀ n t₁ t₂, P n (.rel Language.LT.lt ![t₁, t₂]))
    (hNLT : ∀ n t₁ t₂, P n (.nrel Language.LT.lt ![t₁, t₂]))
    (hAnd : ∀ n p q, Hierarchy 𝚺 1 p → Hierarchy 𝚺 1 q → P n p → P n q → P n (p ⋏ q))
    (hOr : ∀ n p q, Hierarchy 𝚺 1 p → Hierarchy 𝚺 1 q → P n p → P n q → P n (p ⋎ q))
    (hBall : ∀ n t p, Hierarchy 𝚺 1 p → P (n + 1) p → P n (∀[“#0 < !!(Rew.bShift t)”] p))
    (hEx : ∀ n p, Hierarchy 𝚺 1 p → P (n + 1) p → P n (∃' p)) : ∀ n p, Hierarchy 𝚺 1 p → P n p
  | _, _, Hierarchy.verum _ _ _               => hVerum _
  | _, _, Hierarchy.falsum _ _ _              => hFalsum _
  | _, _, Hierarchy.rel _ _ Language.Eq.eq v  => by simpa [←Matrix.fun_eq_vec₂] using hEQ _ (v 0) (v 1)
  | _, _, Hierarchy.nrel _ _ Language.Eq.eq v => by simpa [←Matrix.fun_eq_vec₂] using hNEQ _ (v 0) (v 1)
  | _, _, Hierarchy.rel _ _ Language.LT.lt v  => by simpa [←Matrix.fun_eq_vec₂] using hLT _ (v 0) (v 1)
  | _, _, Hierarchy.nrel _ _ Language.LT.lt v => by simpa [←Matrix.fun_eq_vec₂] using hNLT _ (v 0) (v 1)
  | _, _, Hierarchy.and hp hq                 =>
    hAnd _ _ _ hp hq
      (sigma₁_induction hVerum hFalsum hEQ hNEQ hLT hNLT hAnd hOr hBall hEx _ _ hp)
      (sigma₁_induction hVerum hFalsum hEQ hNEQ hLT hNLT hAnd hOr hBall hEx _ _ hq)
  | _, _, Hierarchy.or hp hq                  =>
    hOr _ _ _ hp hq
      (sigma₁_induction hVerum hFalsum hEQ hNEQ hLT hNLT hAnd hOr hBall hEx _ _ hp)
      (sigma₁_induction hVerum hFalsum hEQ hNEQ hLT hNLT hAnd hOr hBall hEx _ _ hq)
  | _, _, Hierarchy.ball pt hp                => by
    rcases Rew.positive_iff.mp pt with ⟨t, rfl⟩
    exact hBall _ t _ hp (sigma₁_induction hVerum hFalsum hEQ hNEQ hLT hNLT hAnd hOr hBall hEx _ _ hp)
  | _, _, Hierarchy.bex pt hp                 => by
    apply hEx
    · simp [hp]
    · rcases Rew.positive_iff.mp pt with ⟨t, rfl⟩
      apply hAnd _ _ _ (by simp) hp (by simpa [Semiformula.Operator.lt_def] using hLT _ _ _)
        (sigma₁_induction hVerum hFalsum hEQ hNEQ hLT hNLT hAnd hOr hBall hEx _ _ hp)
  | _, _, Hierarchy.sigma (p := p) hp         => by
    have : Hierarchy 𝚺 1 p := hp.accum _
    exact hEx _ _ this (sigma₁_induction hVerum hFalsum hEQ hNEQ hLT hNLT hAnd hOr hBall hEx _ _ this)
  | _, _, Hierarchy.ex hp                     => by
    exact hEx _ _ hp (sigma₁_induction hVerum hFalsum hEQ hNEQ hLT hNLT hAnd hOr hBall hEx _ _ hp)

lemma sigma₁_induction' {n p} (hp : Hierarchy 𝚺 1 p)
    {P : (n : ℕ) → Semiformula ℒₒᵣ ξ n → Prop}
    (hVerum : ∀ n, P n ⊤)
    (hFalsum : ∀ n, P n ⊥)
    (hEQ : ∀ n t₁ t₂, P n (.rel Language.Eq.eq ![t₁, t₂]))
    (hNEQ : ∀ n t₁ t₂, P n (.nrel Language.Eq.eq ![t₁, t₂]))
    (hLT : ∀ n t₁ t₂, P n (.rel Language.LT.lt ![t₁, t₂]))
    (hNLT : ∀ n t₁ t₂, P n (.nrel Language.LT.lt ![t₁, t₂]))
    (hAnd : ∀ n p q, Hierarchy 𝚺 1 p → Hierarchy 𝚺 1 q → P n p → P n q → P n (p ⋏ q))
    (hOr : ∀ n p q, Hierarchy 𝚺 1 p → Hierarchy 𝚺 1 q → P n p → P n q → P n (p ⋎ q))
    (hBall : ∀ n t p, Hierarchy 𝚺 1 p → P (n + 1) p → P n (∀[“#0 < !!(Rew.bShift t)”] p))
    (hEx : ∀ n p, Hierarchy 𝚺 1 p → P (n + 1) p → P n (∃' p)) : P n p :=
  sigma₁_induction hVerum hFalsum hEQ hNEQ hLT hNLT hAnd hOr hBall hEx n p hp

end LOR

end Arith

end FirstOrder

end LO
