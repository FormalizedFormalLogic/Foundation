import Logic.FirstOrder.Arith.Hierarchy
import Logic.FirstOrder.Class.Class

namespace LO

namespace FirstOrder

variable {L : Language} [L.LT] {μ : Type v}

namespace Arith

inductive StrictHierarchy : Polarity → ℕ → {n : ℕ} → Semiformula L μ n → Prop
  | zero {Γ p}                                : DeltaZero p → StrictHierarchy Γ s p
  | sigma {s n} {p : Semiformula L μ (n + 1)} : StrictHierarchy Π s p → StrictHierarchy Σ (s + 1) (∃' p)
  | pi {s n} {p : Semiformula L μ (n + 1)}    : StrictHierarchy Σ s p → StrictHierarchy Π (s + 1) (∀' p)
  | ex {s n} {p : Semiformula L μ (n + 1)}    : StrictHierarchy Σ (s + 1) p → StrictHierarchy Σ (s + 1) (∃' p)
  | all {s n} {p : Semiformula L μ (n + 1)}   : StrictHierarchy Π (s + 1) p → StrictHierarchy Π (s + 1) (∀' p)

lemma DeltaZero.of_open {p : Semiformula L μ n} : p.Open → DeltaZero p := Hierarchy.of_open

namespace StrictHierarchy

lemma rew {p : Semiformula L μ₁ n₁} (h : StrictHierarchy Γ s p) (ω : Rew L μ₁ n₁ μ₂ n₂) :
    StrictHierarchy Γ s (ω.hom p) := by
  induction h generalizing μ₂ n₂ <;> try simp
  case zero h => exact zero <| (Hierarchy.rew_iff (ω := ω)).mpr h
  case sigma ih => exact (ih ω.q).sigma
  case pi ih => exact (ih ω.q).pi
  case ex ih => exact (ih ω.q).ex
  case all ih => exact (ih ω.q).all

lemma rew_iff {p : Semiformula L μ₁ n₁} (ω : Rew L μ₁ n₁ μ₂ n₂) :
    StrictHierarchy Γ s (ω.hom p) ↔ StrictHierarchy Γ s p :=
  ⟨by
    generalize hq : ω.hom p = q
    intro h;
    induction h generalizing n₁ <;> try simp [Rew.eq_ball_iff, Rew.eq_bex_iff, Rew.eq_all_iff, Rew.eq_ex_iff] at hq ⊢
    case zero q h =>
      rcases hq; exact zero (Hierarchy.rew_iff.mp h)
    case sigma h ih =>
      rcases hq with ⟨_, rfl, rfl⟩
      exact (ih ω.q rfl).sigma
    case pi h ih =>
      rcases hq with ⟨_, rfl, rfl⟩
      exact (ih ω.q rfl).pi
    case ex h ih =>
      rcases hq with ⟨_, rfl, rfl⟩
      exact (ih ω.q rfl).ex
    case all ih =>
      rcases hq with ⟨_, rfl, rfl⟩
      exact (ih ω.q rfl).all,
  fun h ↦ h.rew ω⟩

lemma succ {Γ} {p : Semiformula L μ₁ n₁} (h : StrictHierarchy Γ s p) :
    StrictHierarchy Γ (s + 1) p := by
  induction h
  case zero h => exact zero h
  case sigma ih => exact ih.sigma
  case pi ih => exact ih.pi
  case ex ih => exact ih.ex
  case all ih => exact ih.all

lemma zero_iff_delta_zero {Γ} {p : Semiformula L μ n} :
    StrictHierarchy Γ 0 p ↔ DeltaZero p := by
  constructor
  · rintro ⟨h⟩; exact h
  · intro h; exact zero h

end StrictHierarchy

def SHClass (L : Language) [L.LT] (Γ : Polarity) (s : ℕ) : Class L where
  Domain := StrictHierarchy Γ s
  rew_closed := by intro _ _ ω p hp; exact hp.rew ω

notation Γ "ᴴ("s")" => SHClass _ Γ s

abbrev SHClassIn (Γ s) (T : Theory L) := (SHClass L Γ s).eqvClosure T

notation Γ "ᴴ("s")[" T "]" => SHClassIn Γ s T

abbrev DeltaZeroIn (T : Theory L) := (SHClass L Σ 0).eqvClosure T

notation "Δ₀[" T "]" => DeltaZeroIn T

lemma SHClassIn.eqDeltaZero (T : Theory L) (Γ) : Γᴴ(0)[T] = Δ₀[T] := by
  simp [SHClassIn, DeltaZeroIn]; congr 1
  ext p; simp [SHClass, Set.mem_def, StrictHierarchy.zero_iff_delta_zero]

namespace SHClassIn

variable (Γ : Polarity) (s : ℕ) (T : Theory L)

open StrictHierarchy Semiformula

lemma accumlative_succ (Γ Γ' s) : Γᴴ(s)[T] ≤ Γ'ᴴ(s + 1)[T] := by
  rintro _ p ⟨p', hp', Hp⟩
  cases Γ <;> cases Γ'
  · exact ⟨p', hp'.succ, Hp⟩
  · exact ⟨∀' Rew.bShift.hom p', (rew hp' _).pi, Equivalent.trans (Equivalent.dummy_quantifier_all p') Hp⟩
  · exact ⟨∃' Rew.bShift.hom p', (rew hp' _).sigma, Equivalent.trans (Equivalent.dummy_quantifier_ex p') Hp⟩
  · exact ⟨p', hp'.succ, Hp⟩

lemma accumlative (Γ Γ') {s s'} (h : s < s') : Γᴴ(s)[T] ≤ Γ'ᴴ(s')[T] := by
  generalize hk : s' - s - 1 = k
  have : s' = s + 1 + k := by simp [←hk, Nat.sub_sub]; exact (Nat.sub_eq_iff_eq_add' h).mp rfl
  rcases this with rfl
  clear h hk
  induction' k with k ih
  · simp; exact accumlative_succ T Γ Γ' s
  · simp [show s + 1 + k.succ = s + 1 + k + 1 from by simp [Nat.add_succ]]
    exact Class.LE.trans ih (accumlative_succ T _ _ _)

@[simp] lemma delta_zero_le : Δ₀[T] ≤ Γᴴ(s)[T] := by
  cases s
  · simp [SHClassIn.eqDeltaZero]; rfl
  · rw [←SHClassIn.eqDeltaZero T Γ]; exact accumlative T Γ Γ (by simp)

lemma openClass_le : openClass L ≤ SHClass L Σ 0 := by
  intro _ p hp
  simp [SHClass, Set.mem_def, zero_iff_delta_zero]
  exact Hierarchy.of_open hp

lemma openClass_le' : openClass L ≤ Γᴴ(s)[T] :=
  Class.LE.trans openClass_le (Class.LE.trans (Class.le_eqvClosure _ _) (delta_zero_le Γ s T))

instance atom : (Γᴴ(s)[T]).Atom := Class.of_le (openClass L) _ (openClass_le' Γ s T)

end SHClassIn

namespace DeltaZeroIn

variable (Γ : Polarity) (s : ℕ) (T : Theory L)

open Hierarchy SHClassIn StrictHierarchy Semiformula

instance atom : (Δ₀[T]).Atom := SHClassIn.atom Σ 0 T

instance not : (Δ₀[T]).Not := ⟨by
  rintro _ p ⟨p', hp', Hp⟩
  exact ⟨~p',
    zero_iff_delta_zero.mpr
      (by simp [←Hierarchy.zero_iff_delta_zero (Γ := Σ), pi_zero_iff_sigma_zero]; exact zero_iff_delta_zero.mp hp'),
    Hp.not⟩⟩

instance and : (Δ₀[T]).And := ⟨by
  rintro _ p q ⟨p', hp', Hp⟩ ⟨q', hq', Hq⟩
  have hp' : DeltaZero p' := zero_iff_delta_zero.mp hp'
  have hq' : DeltaZero q' := zero_iff_delta_zero.mp hq'
  exact ⟨p' ⋏ q', zero_iff_delta_zero.mpr (Hierarchy.and hp' hq'), Hp.and Hq⟩⟩

instance or : (Δ₀[T]).Or := ⟨by
  rintro _ p q ⟨p', hp', Hp⟩ ⟨q', hq', Hq⟩
  have hp' : DeltaZero p' := zero_iff_delta_zero.mp hp'
  have hq' : DeltaZero q' := zero_iff_delta_zero.mp hq'
  exact ⟨p' ⋎ q', zero_iff_delta_zero.mpr (Hierarchy.or hp' hq'), Hp.or Hq⟩⟩

/-
instance ball : (Δ₀[T]).BAll := ⟨by {
  rintro _ p ⟨p', hp', H⟩
  have hp' : DeltaZero p' := zero_iff_delta_zero.mp hp'
  exact ⟨∀[“#0 < &0”] p', zero_iff_delta_zero.mpr (Hierarchy.ball (by simp) hp'), by {  }⟩
   }⟩
-/

end DeltaZeroIn
