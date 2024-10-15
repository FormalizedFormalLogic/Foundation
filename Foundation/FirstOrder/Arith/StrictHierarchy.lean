import Foundation.FirstOrder.Arith.PeanoMinus

namespace LO

namespace FirstOrder

namespace Arith

section

variable {L : Language} [L.LT]

inductive StrictHierarchy : Polarity → ℕ → {n : ℕ} → Semiformula L μ n → Prop
  | zero {Γ p}                                : DeltaZero p → StrictHierarchy Γ s p
  | sigma {s n} {p : Semiformula L μ (n + 1)} : StrictHierarchy 𝚷 s p → StrictHierarchy 𝚺 (s + 1) (∃' p)
  | pi {s n} {p : Semiformula L μ (n + 1)}    : StrictHierarchy 𝚺 s p → StrictHierarchy 𝚷 (s + 1) (∀' p)
  | ex {s n} {p : Semiformula L μ (n + 1)}    : StrictHierarchy 𝚺 (s + 1) p → StrictHierarchy 𝚺 (s + 1) (∃' p)
  | all {s n} {p : Semiformula L μ (n + 1)}   : StrictHierarchy 𝚷 (s + 1) p → StrictHierarchy 𝚷 (s + 1) (∀' p)

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

/-

def HClass (L : Language) [L.LT] (ξ : Type*) (Γ : Polarity) (s : ℕ) : Class L ξ where
  Domain := Hierarchy Γ s
  rew_closed := fun ω _ hp ↦ hp.rew ω

abbrev HClassIn (ξ : Type*) [DecidableEq ξ] (Γ s) (T : Theory L) := (HClass L ξ Γ s).eqvClosure T

abbrev DeltaZeroIn (ξ : Type*) [DecidableEq ξ] (T : Theory L) := HClassIn ξ 𝚺 0 T

namespace HClass

variable {L : Language} [L.LT] {ξ : Type*} [DecidableEq ξ]

open Hierarchy

instance not : (HClass L ξ Γ 0).Not := ⟨fun h ↦ by
  simpa [HClass, zero_iff_delta_zero] using Hierarchy.neg h⟩

instance and : (HClass L ξ Γ s).And := ⟨Hierarchy.and⟩

instance or : (HClass L ξ Γ s).Or := ⟨Hierarchy.or⟩

instance ball : (HClass L ξ Γ s).BAll := ⟨fun hp ht ↦ Hierarchy.ball ht hp⟩

instance bex : (HClass L ξ Γ s).BEx := ⟨fun hp ht ↦ Hierarchy.bex ht hp⟩

lemma accumlative_succ (Γ Γ' s) : HClass L ξ Γ s ≤ HClass L ξ Γ' (s + 1) := by
  intro _ p hp; exact Hierarchy.accum hp Γ'

lemma openClass_le (Γ s) : openClass L ξ ≤ HClass L ξ Γ s := by
  intro _ p hp
  simp [HClass, Set.mem_def, zero_iff_delta_zero]
  exact Hierarchy.of_open hp

instance atom : (HClass L ξ Γ s : Class L ξ).Atom := Class.of_le (openClass L ξ) _ (openClass_le Γ s)

end HClass

namespace HClassIn

variable [DecidableEq ξ]

instance atom : (HClassIn ξ Γ s T : Class L ξ).Atom := Class.eqvClosure_atom

instance and : (HClassIn ξ Γ s T : Class L ξ).And := Class.eqvClosure_and

instance or : (HClassIn ξ Γ s T : Class L ξ).Or := Class.eqvClosure_or

instance ball : (HClassIn ξ Γ s T : Class L ξ).BAll := Class.eqvClosure_ball

instance bex : (HClassIn ξ Γ s T : Class L ξ).BEx := Class.eqvClosure_bex

instance not : (DeltaZeroIn ξ T : Class L ξ).Not := Class.eqvClosure_not

end HClassIn

def SHClass (L : Language) [L.LT] (ξ : Type*) (Γ : Polarity) (s : ℕ) : Class L ξ where
  Domain := StrictHierarchy Γ s
  rew_closed := fun ω _ hp ↦ hp.rew ω

-- notation Γ "ᴴ("s")" => SHClass _ _ Γ s

abbrev SHClassIn (ξ : Type*) [DecidableEq ξ] (Γ s) (T : Theory L) := (SHClass L ξ Γ s).eqvClosure T

-- notation Γ "ᴴ("s")[" T "]" => SHClassIn _ Γ s T

-- notation "Δ₀[" T "]" => DeltaZeroIn _ T

/-
variable {ξ : Type*} [DecidableEq ξ]

namespace SHClassIn

variable (Γ : Polarity) (s : ℕ) (T : Theory L)

open StrictHierarchy Semiformula

lemma accumlative_succ (Γ Γ' s) : SHClassIn ξ Γ s T ≤ SHClassIn ξ Γ' (s + 1) T := by
  rintro _ p ⟨p', hp', Hp⟩
  cases Γ <;> cases Γ'
  · exact ⟨p', hp'.succ, Hp⟩
  · exact ⟨∀' Rew.bShift.hom p', (rew hp' _).pi, Equivalent.trans (Equivalent.dummy_quantifier_all p') Hp⟩
  · exact ⟨∃' Rew.bShift.hom p', (rew hp' _).sigma, Equivalent.trans (Equivalent.dummy_quantifier_ex p') Hp⟩
  · exact ⟨p', hp'.succ, Hp⟩

lemma accumlative (Γ Γ') {s s'} (h : s < s') : SHClassIn ξ Γ s T ≤ SHClassIn ξ Γ' s' T := by
  generalize hk : s' - s - 1 = k
  have : s' = s + 1 + k := by simp [←hk, Nat.sub_sub]; exact (Nat.sub_eq_iff_eq_add' h).mp rfl
  rcases this with rfl
  clear h hk
  induction' k with k ih
  · simp; exact accumlative_succ T Γ Γ' s
  · simp [show s + 1 + k.succ = s + 1 + k + 1 from by simp [Nat.add_succ]]
    exact Class.LE.trans ih (accumlative_succ T _ _ _)

/-
@[simp] lemma delta_zero_le : DeltaZeroIn ξ T ≤ SHClassIn ξ Γ s T := by
  cases s
  · simp [SHClassIn.eqDeltaZero]; rfl
  · rw [←SHClassIn.eqDeltaZero T Γ]; exact accumlative T Γ Γ (by simp)
-/

lemma openClass_le : openClass L ξ ≤ SHClass L ξ 𝚺 0 := by
  intro _ p hp
  simp [SHClass, Set.mem_def, zero_iff_delta_zero]
  exact Hierarchy.of_open hp

/-
lemma openClass_le' : openClass L ξ ≤ SHClassIn ξ Γ s T :=
  Class.LE.trans openClass_le (Class.LE.trans (Class.le_eqvClosure _ _) (delta_zero_le Γ s T))
-/

instance atom : (SHClassIn ξ Γ s T : Class L ξ).Atom := Class.of_le (openClass L ξ) _ (openClass_le' Γ s T)

variable {Γ s T} {ξ₁ : Type*} [DecidableEq ξ₁] {ξ₂ : Type*} [DecidableEq ξ₂]

@[formula_class] def rew {p : Semiformula L ξ₁ n₁} (hp : (SHClassIn ξ₁ Γ s T).Domain p) (ω : Rew L ξ₁ n₁ ξ₂ n₂) : (SHClassIn ξ₂ Γ s T).Domain (ω.hom p) := by
  rcases hp with ⟨p', hp', H⟩
  exact ⟨ω.hom p', StrictHierarchy.rew hp' ω, H.rew ω⟩

end SHClassIn

namespace DeltaZeroIn

variable (Γ : Polarity) (s : ℕ) (T : Theory L)

open Hierarchy SHClassIn StrictHierarchy Semiformula

instance atom : (DeltaZeroIn ξ T).Atom := SHClassIn.atom 𝚺 0 T

instance not : (DeltaZeroIn ξ T).Not := ⟨by
  rintro _ p ⟨p', hp', Hp⟩
  exact ⟨∼p',
    zero_iff_delta_zero.mpr
      (by simp [←Hierarchy.zero_iff_delta_zero (Γ := 𝚺), pi_zero_iff_sigma_zero]; exact zero_iff_delta_zero.mp hp'),
    Hp.not⟩⟩

instance and : (DeltaZeroIn ξ T).And := ⟨by
  rintro _ p q ⟨p', hp', Hp⟩ ⟨q', hq', Hq⟩
  have hp' : DeltaZero p' := zero_iff_delta_zero.mp hp'
  have hq' : DeltaZero q' := zero_iff_delta_zero.mp hq'
  exact ⟨p' ⋏ q', zero_iff_delta_zero.mpr (Hierarchy.and hp' hq'), Hp.and Hq⟩⟩

instance or : (DeltaZeroIn ξ T).Or := ⟨by
  rintro _ p q ⟨p', hp', Hp⟩ ⟨q', hq', Hq⟩
  have hp' : DeltaZero p' := zero_iff_delta_zero.mp hp'
  have hq' : DeltaZero q' := zero_iff_delta_zero.mp hq'
  exact ⟨p' ⋎ q', zero_iff_delta_zero.mpr (Hierarchy.or hp' hq'), Hp.or Hq⟩⟩

instance ball : (DeltaZeroIn ξ T).BAll := ⟨by
  rintro _ p t ⟨p', hp', H⟩ ht
  have hp' : DeltaZero p' := zero_iff_delta_zero.mp hp'
  exact ⟨∀[“#0 < !!t”] p', zero_iff_delta_zero.mpr (Hierarchy.ball ht hp'),
    Semiformula.Equivalent.ball (by rfl) H⟩⟩

instance bex : (DeltaZeroIn ξ T).BEx := ⟨by
  rintro _ p t ⟨p', hp', H⟩ ht
  have hp' : DeltaZero p' := zero_iff_delta_zero.mp hp'
  exact ⟨∃[“#0 < !!t”] p', zero_iff_delta_zero.mpr (Hierarchy.bex ht hp'),
    Semiformula.Equivalent.bex (by rfl) H⟩⟩

end DeltaZeroIn
-/

-/
end

end Arith
