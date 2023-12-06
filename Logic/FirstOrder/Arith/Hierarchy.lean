import Logic.FirstOrder.Arith.Basic

namespace LO

namespace FirstOrder

variable {L : Language.{u}} [FirstOrder.ORing L] {μ : Type v}

namespace Arith

local notation "Σ" => Bool.true
local notation "Π" => Bool.false

inductive Hierarchy : Bool → ℕ → {n : ℕ} → Subformula L μ n → Prop
  | verum (b s n)                             : Hierarchy b s (⊤ : Subformula L μ n)
  | falsum (b s n)                            : Hierarchy b s (⊥ : Subformula L μ n)
  | rel (b s) {k} (r : L.Rel k) (v : Fin k → Subterm L μ n) : Hierarchy b s (Subformula.rel r v)
  | nrel (b s) {k} (r : L.Rel k) (v)          : Hierarchy b s (Subformula.nrel r v)
  | and {b s n} {p q : Subformula L μ n}      : Hierarchy b s p → Hierarchy b s q → Hierarchy b s (p ⋏ q)
  | or {b s n} {p q : Subformula L μ n}       : Hierarchy b s p → Hierarchy b s q → Hierarchy b s (p ⋎ q)
  | ball {b s n} {p : Subformula L μ (n + 1)} :
    (t : Subterm L μ n) → Hierarchy b s p → Hierarchy b s “∀[#0 < !!(Rew.bShift t)] !p”
  | bex {b s n} {p : Subformula L μ (n + 1)}  :
    (t : Subterm L μ n) → Hierarchy b s p → Hierarchy b s “∃[#0 < !!(Rew.bShift t)] !p”
  | ex {s n} {p : Subformula L μ (n + 1)}     : Hierarchy Σ (s + 1) p → Hierarchy Σ (s + 1) (∃' p)
  | all {s n} {p : Subformula L μ (n + 1)}    : Hierarchy Π (s + 1) p → Hierarchy Π (s + 1) (∀' p)
  | sigma {s n} {p : Subformula L μ (n + 1)}  : Hierarchy Π s p → Hierarchy Σ (s + 1) (∃' p)
  | pi {s n} {p : Subformula L μ (n + 1)}     : Hierarchy Σ s p → Hierarchy Π (s + 1) (∀' p)

attribute [simp] Hierarchy.verum Hierarchy.falsum Hierarchy.rel Hierarchy.nrel

abbrev Hierarchy.Sigma (s : ℕ) : Subformula L μ n → Prop := Hierarchy Σ s

abbrev Hierarchy.Pi (s : ℕ) : Subformula L μ n → Prop := Hierarchy Π s

namespace Hierarchy

lemma mono_succ {b} {s : ℕ} {p : Subformula L μ n} (hp : Hierarchy b s p) : Hierarchy b (s + 1) p := by
  induction hp
  case verum       => exact verum _ _ _
  case falsum      => exact falsum _ _ _
  case rel r v     => exact rel _ _ r v
  case nrel r v    => exact nrel _ _ r v
  case and ihp ihq => exact and ihp ihq
  case or ihp ihq  => exact or ihp ihq
  case ball ih     => exact ball _ ih
  case bex ih      => exact bex _ ih
  case ex ih       => exact ex ih
  case all ih      => exact all ih
  case sigma ih    => exact sigma ih
  case pi ih       => exact pi ih

lemma mono {b} {s s' : ℕ} (h : s ≤ s') {p : Subformula L μ n} (hp : Hierarchy b s p) : Hierarchy b s' p := by
  have : ∀ d, Hierarchy b (s + d) p := by
    intro d
    induction' d with s ih
    · exact hp
    · simpa[Nat.add_succ] using mono_succ ih
  simpa[Nat.add_sub_of_le h] using this (s' - s)

@[simp] lemma and_iff {p q : Subformula L μ n} : Hierarchy b s (p ⋏ q) ↔ Hierarchy b s p ∧ Hierarchy b s q :=
  ⟨by rintro ⟨⟩; simp[*], by rintro ⟨hp, hq⟩; exact Hierarchy.and hp hq⟩

@[simp] lemma or_iff {p q : Subformula L μ n} : Hierarchy b s (p ⋎ q) ↔ Hierarchy b s p ∧ Hierarchy b s q :=
  ⟨by rintro ⟨⟩; simp[*], by rintro ⟨hp, hq⟩; exact Hierarchy.or hp hq⟩

@[simp] lemma conj_iff {p : Fin m → Subformula L μ n} :
    Hierarchy b s (Matrix.conj p) ↔ ∀ i, Hierarchy b s (p i) := by
  induction m <;> simp[Matrix.conj, Matrix.vecTail, *]
  · exact ⟨by rintro ⟨hz, hs⟩ i; cases i using Fin.cases <;> simp[*],
           by intro h; exact ⟨h 0, fun _ => h _⟩⟩

lemma ball' {b s n} {p : Subformula L μ (n + 1)} (t : Subterm L μ n) {t' : Subterm L μ (n + 1)}
  (ht : Rew.bShift t = t') (hp : Hierarchy b s p) :
    Hierarchy b s “∀[#0 < !!t'] !p” := by rw[←ht]; exact hp.ball _

lemma ex' {b s n} {p : Subformula L μ (n + 1)} (t : Subterm L μ n) {t' : Subterm L μ (n + 1)}
  (ht : Rew.bShift t = t') (hp : Hierarchy b s p) :
    Hierarchy b s “∃[#0 < !!t'] !p” := by rw[←ht]; exact hp.bex _

lemma zero_eq_alt {p : Subformula L μ n} : Hierarchy b 0 p → Hierarchy (!b) 0 p := by
  generalize hz : 0 = z
  rw[eq_comm] at hz
  intro h
  induction h <;> try simp at hz ⊢
  case and _ _ ihp ihq =>
    exact ⟨ihp hz, ihq hz⟩
  case or _ _ ihp ihq => exact ⟨ihp hz, ihq hz⟩
  case ball _ _ ih => exact ball _ (ih hz)
  case bex _ _ ih => exact bex _ (ih hz)

lemma pi_zero_iff_sigma_zero {p : Subformula L μ n} : Pi 0 p ↔ Sigma 0 p := ⟨zero_eq_alt, zero_eq_alt⟩

lemma neg {p : Subformula L μ n} : Hierarchy b s p → Hierarchy (!b) s (~p) := by
  intro h; induction h <;> simp[*]
  case bex ih => exact ball _ ih
  case ball ih => exact bex _ ih
  case ex ih => exact all ih
  case all ih => exact ex ih
  case sigma ih => exact pi ih
  case pi ih => exact sigma ih

lemma rew (ω : Rew L μ₁ n₁ μ₂ n₂) {p : Subformula L μ₁ n₁} : Hierarchy b s p → Hierarchy b s (ω.hom p) := by
  intro h; induction h generalizing n₂ <;> simp[*, Rew.rel,Rew.nrel]
  case bex ih => exact bex _ (ih _)
  case ball ih => exact ball _ (ih _)
  case ex ih => exact ex (ih _)
  case all ih => exact all (ih _)
  case sigma ih => exact sigma (ih _)
  case pi ih => exact pi (ih _)

/-
lemma rew_iff (ω : Rew L μ₁ n₁ μ₂ n₂) {p : Subformula L μ₁ n₁} : Hierarchy b s (ω.hom p) ↔ Hierarchy b s p := by
  constructor
  · generalize eq : ω.hom p = q
    intro hq; induction hq generalizing p n₁
      <;> simp[Rew.eq_rel_iff, Rew.eq_nrel_iff, Rew.eq_ball_iff, Rew.eq_all_iff, Rew.eq_ex_iff] at eq
    case verum => rcases eq with rfl; simp
    case falsum => rcases eq with rfl; simp
    case rel => rcases eq with ⟨v', rfl, rfl⟩; simp
    case nrel => rcases eq with ⟨v', rfl, rfl⟩; simp
    case and ihp ihq =>
      rcases eq with ⟨p₁, rfl, p₂, rfl, rfl⟩
      simpa using ⟨ihp ω rfl, ihq ω rfl⟩
    case or ihp ihq =>
      rcases eq with ⟨p₁, rfl, p₂, rfl, rfl⟩
      simpa using ⟨ihp ω rfl, ihq ω rfl⟩
    case ball ih =>

    case all ih =>
      rcases eq with ⟨p, rfl, rfl⟩
      exact (ih ω.q rfl).all
    case ex ih =>
      rcases eq with ⟨p, rfl, rfl⟩
      exact (ih ω.q rfl).ex
-/

lemma neg_iff {p : Subformula L μ n} : Hierarchy b s (~p) ↔ Hierarchy (!b) s p :=
  ⟨fun h => by simpa using neg h, fun h => by simpa using neg h⟩

lemma exClosure : {n : ℕ} → {p : Subformula L μ n} → Sigma (s + 1) p → Sigma (s + 1) (exClosure p)
  | 0,     _, hp => hp
  | n + 1, p, hp => by simpa using exClosure (hp.ex)

end Hierarchy

variable {L : Language} [(k : ℕ) → DecidableEq (L.Func k)] [(k : ℕ) → DecidableEq (L.Rel k)]
  [ORing L] [Structure L ℕ]

abbrev SigmaOneSound (T : Theory L) := Sound (L := L) T (Hierarchy.Sigma 1)

lemma consistent_of_sigmaOneSound (T : Theory L) [SigmaOneSound T] :
    System.Consistent T := consistent_of_sound T (Hierarchy.Sigma 1) (by simp)

end Arith

end FirstOrder

end LO
