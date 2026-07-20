module

public import Foundation.LinearLogic.MLL.Propositional
public import Foundation.Vorspiel.Algebra.IsNilpotent
public import Foundation.Vorspiel.GroupTheory.Perm

/-!
# A Toy Model of Geometry of Interaction
-/

@[expose] public section

namespace Equiv

@[simp] lemma sumComm_trans_sumComm (α β : Type*) :
    (Equiv.sumComm α β).trans (Equiv.sumComm β α) = 1 := by
  ext (_ | _) <;> rfl

end Equiv

namespace LO.Propositional.LinearLogic.Multiplicative

namespace GoI

open Equiv.Perm

@[ext]
structure Project (Carrier : Type*) : Type _ where
  /-- Wager, a remnant of self-closed cycles. -/
  wager : ℕ
  /-- A main gadget expresses permutation of _loci_. -/
  plot : Equiv.Perm Carrier

namespace Project

variable {α β : Type*}

def add (𝔞 : Project α) (𝔟 : Project β) : Project (α ⊕ β) where
  wager := 𝔞.wager + 𝔟.wager
  plot := 𝔞.plot.sumCongr 𝔟.plot

instance : HAdd (Project α) (Project β) (Project (α ⊕ β)) where
  hAdd := add

@[simp] lemma add_wager (𝔞 : Project α) (𝔟 : Project β) :
    (𝔞 + 𝔟).wager = 𝔞.wager + 𝔟.wager := rfl

lemma add_plot (𝔞 : Project α) (𝔟 : Project β) :
    (𝔞 + 𝔟).plot = 𝔞.plot.sumCongr 𝔟.plot := rfl

def one : Project α where
  wager := 0
  plot := Equiv.refl α

instance : One (Project α) where
  one := one

instance : Inhabited (Project α) where
  default := 1

@[simp] lemma one_wager : (1 : Project α).wager = 0 := rfl

lemma one_plot : (1 : Project α).plot = Equiv.refl α := rfl

def mul (𝔞 𝔟 : Project α) : Project α where
  wager := 𝔞.wager + 𝔟.wager
  plot := 𝔞.plot * 𝔟.plot

instance : Mul (Project α) where
  mul := mul

@[simp] lemma mul_wager (𝔞 𝔟 : Project α) :
    (𝔞 * 𝔟).wager = 𝔞.wager + 𝔟.wager := rfl

lemma mul_plot (𝔞 𝔟 : Project α) :
    (𝔞 * 𝔟).plot = 𝔞.plot * 𝔟.plot := rfl

@[simp] lemma mul_one (𝔞 : Project α) : 𝔞 * 1 = 𝔞 := by
  ext <;> simp [mul_plot, one_plot]

@[simp] lemma one_mul (𝔞 : Project α) : 1 * 𝔞 = 𝔞 := by
  ext <;> simp [mul_plot, one_plot]

@[simp] lemma mul_assoc (𝔞 𝔟 𝔠 : Project α) :
    (𝔞 * 𝔟) * 𝔠 = 𝔞 * (𝔟 * 𝔠) := by
  ext <;> simp [mul_plot, add_assoc]

lemma add_mul_add (𝔞₁ 𝔞₂ : Project α) (𝔟₁ 𝔟₂ : Project β) :
    (𝔞₁ + 𝔟₁) * (𝔞₂ + 𝔟₂) = 𝔞₁ * 𝔞₂ + 𝔟₁ * 𝔟₂ := by
  ext x
  · simp; omega
  · cases x <;> rfl

def delocate (𝔞 : Project α) (φ : α ≃ β) : Project β where
  wager := 𝔞.wager
  plot := (φ.symm.trans 𝔞.plot).trans φ

@[simp] lemma delocate_wager (𝔞 : Project α) (φ : α ≃ β) :
    (𝔞.delocate φ).wager = 𝔞.wager := rfl

lemma delocate_plot (𝔞 : Project α) (φ : α ≃ β) :
    (𝔞.delocate φ).plot = (φ.symm.trans 𝔞.plot).trans φ := rfl

@[simp] lemma delocate_sumComm_add {𝔠 : Project (α ⊕ β)} (𝔞 : Project α) (𝔟 : Project β) :
    𝔠.delocate (Equiv.sumComm α β) * (𝔟 + 𝔞) = (𝔠 * (𝔞 + 𝔟)).delocate (Equiv.sumComm α β) := by
  ext x
  · simp; omega
  · cases x <;> rfl

lemma delocate_comp (𝔞 : Project α) (φ : α ≃ β) (ψ : β ≃ γ) :
    𝔞.delocate (φ.trans ψ) = (𝔞.delocate φ).delocate ψ := rfl

@[simp] lemma delocate_one (𝔞 : Project α) : 𝔞.delocate 1 = 𝔞 := by
  ext <;> simp [delocate_plot]
  rfl

end Project

/-! ### Measurement and polarity -/

def Project.tr [Fintype α] [DecidableEq α] (𝔞 : Project α) : ℕ := 𝔞.wager + 𝔞.plot.tr

def Project.measurement [Fintype α] [DecidableEq α] (𝔞 𝔟 : Project α) : ℕ := (𝔞 * 𝔟).tr

scoped notation "⟪" 𝔞 " | " 𝔟 "⟫" => Project.measurement 𝔞 𝔟

def Project.IsPolar [Fintype α] [DecidableEq α] (𝔞 𝔟 : Project α) : Prop :=
  ⟪𝔞 | 𝔟⟫ = 1

scoped infix:50 " ⟂ " => Project.IsPolar

namespace Project

variable {α β γ : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]

@[simp] lemma tr_add (𝔞 𝔟 : Project α) : (𝔞 + 𝔟).tr = 𝔞.tr + 𝔟.tr := by
  simp [Project.tr, add_plot]; omega

@[simp] lemma tr_delocate (𝔞 : Project α) (φ : α ≃ β) : (𝔞.delocate φ).tr = 𝔞.tr := by
  unfold Project.tr
  congr 1
  change (φ.permCongr 𝔞.plot).tr = 𝔞.plot.tr
  exact Orbit.partition_parts_card_permCongr φ 𝔞.plot

lemma measurement_comm (𝔞 𝔟 : Project α) :
    ⟪𝔞 | 𝔟⟫ = ⟪𝔟 | 𝔞⟫ := by
  simp [measurement, tr, mul_plot, tr_comm]; omega

@[symm, grind =] lemma isPolar_symm {𝔞 𝔟 : Project α} :
    𝔞 ⟂ 𝔟 ↔ 𝔟 ⟂ 𝔞 := by
  simp [Project.IsPolar, measurement_comm]

/-! ### Projects -/

def fax (α : Type*) : Project (α ⊕ α) where
  wager := 0
  plot := Equiv.sumComm α α

@[simp] lemma fax_wager (α : Type*) : (fax α).wager = 0 := rfl

def daimon (r : ℕ) : Project PEmpty where
  wager := r
  plot := default

def subtypeExtend {P : α → Prop} [DecidablePred P] (𝔞 : Project {a : α // P a}) : Project α where
  wager := 𝔞.wager
  plot := 𝔞.plot.subtypeCongr 1

omit [Fintype α] [DecidableEq α] in
@[simp] lemma subtypeExtend_wager {P : α → Prop} [DecidablePred P] (𝔞 : Project {a : α // P a}) :
    𝔞.subtypeExtend.wager = 𝔞.wager := rfl

def permApp (F : Equiv.Perm (α ⊕ β)) (A : Equiv.Perm α) : Equiv.Perm (α ⊕ β) :=
  F * A.sumCongr 1

def IsLeftEquivLeft : { x : α ⊕ β // x.isLeft} ≃ α where
  toFun := fun x ↦ x.val.getLeft (by simpa using x.2)
  invFun := fun a ↦ ⟨.inl a, by simp⟩
  left_inv := by
    rintro ⟨_ | _, hx⟩
    · rfl
    · simp at hx
  right_inv := fun _ ↦ rfl

def notIsLeftEquivRight : { x : α ⊕ β // ¬x.isLeft} ≃ β where
  toFun := fun x ↦ x.val.getRight (by simpa using x.2)
  invFun := fun b ↦ ⟨.inr b, by simp⟩
  left_inv := by
    rintro ⟨_ | _, hx⟩
    · simp at hx
    · rfl
  right_inv := fun _ ↦ rfl

open Equiv.Perm.FirstReturn

omit [DecidableEq α] [DecidableEq β] in
lemma pow_mul_sumCongr_right_succ_of_lt_time
    (σ : Equiv.Perm (α ⊕ β)) (b : Equiv.Perm β) (x : β) {k : ℕ}
    (hk : k < time σ (⟨.inr (b x), by simp⟩ : {x : α ⊕ β // ¬x.isLeft})) :
    ((σ * ((1 : Equiv.Perm α).sumCongr b)) ^ (k + 1)) (.inr x) =
      (σ ^ (k + 1)) (.inr (b x)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hk' : k < time σ (⟨.inr (b x), by simp⟩ : {x : α ⊕ β // ¬x.isLeft}) :=
        Nat.lt_trans (Nat.lt_succ_self k) hk
      have hleft : Sum.isLeft ((σ ^ (k + 1)) (.inr (b x))) := by
        by_contra hright
        exact not_return_of_lt_time hk ⟨Nat.succ_pos k, hright⟩
      rw [pow_succ', Equiv.Perm.mul_apply, ih hk']
      change σ (((1 : Equiv.Perm α).sumCongr b) ((σ ^ (k + 1)) (.inr (b x)))) =
        (σ ^ (k + 1 + 1)) (.inr (b x))
      cases hσ : (σ ^ (k + 1)) (.inr (b x)) with
      | inl a =>
          calc
            σ (((1 : Equiv.Perm α).sumCongr b) (.inl a)) = σ (.inl a) := rfl
            _ = σ ((σ ^ (k + 1)) (.inr (b x))) := by rw [hσ]
            _ = (σ ^ (k + 1 + 1)) (.inr (b x)) := by
              simp [pow_succ', Equiv.Perm.mul_apply]
      | inr c =>
          simp [hσ] at hleft

omit [DecidableEq α] [DecidableEq β] in
lemma pow_mul_sumCongr_right_return_time
    (σ : Equiv.Perm (α ⊕ β)) (b : Equiv.Perm β) (x : β) :
    let n := time σ (⟨.inr (b x), by simp⟩ : {x : α ⊕ β // ¬x.isLeft})
    ((σ * ((1 : Equiv.Perm α).sumCongr b)) ^ n) (.inr x) =
      (σ ^ n) (.inr (b x)) := by
  intro n
  have hn : 0 < n := (time_spec σ (⟨.inr (b x), by simp⟩ :
    {x : α ⊕ β // ¬x.isLeft})).1
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [hk]
  have hklt : k < n := by rw [hk]; exact Nat.lt_succ_self k
  exact pow_mul_sumCongr_right_succ_of_lt_time σ b x (by change k < n; exact hklt)

omit [DecidableEq α] [DecidableEq β] in
lemma time_mul_sumCongr_right
    (σ : Equiv.Perm (α ⊕ β)) (b : Equiv.Perm β) (x : β) :
    time (σ * ((1 : Equiv.Perm α).sumCongr b))
        (⟨.inr x, by simp⟩ : {x : α ⊕ β // ¬x.isLeft}) =
      time σ (⟨.inr (b x), by simp⟩ : {x : α ⊕ β // ¬x.isLeft}) := by
  let τ := σ * ((1 : Equiv.Perm α).sumCongr b)
  let xτ : {x : α ⊕ β // ¬x.isLeft} := ⟨.inr x, by simp⟩
  let yσ : {x : α ⊕ β // ¬x.isLeft} := ⟨.inr (b x), by simp⟩
  have hreturn : ¬Sum.isLeft ((τ ^ time σ yσ) (.inr x)) := by
    have hpow := pow_mul_sumCongr_right_return_time σ b x
    change (τ ^ time σ yσ) (.inr x) = (σ ^ time σ yσ) (.inr (b x)) at hpow
    rw [hpow]
    exact (time_spec σ yσ).2
  apply le_antisymm
  · exact time_le_of_return ⟨(time_spec σ yσ).1, hreturn⟩
  · by_contra hle
    have hlt : time τ xτ < time σ yσ := Nat.lt_of_not_ge hle
    have hmpos : 0 < time τ xτ := (time_spec τ xτ).1
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hmpos)
    have hklt : k < time σ (⟨.inr (b x), by simp⟩ : {x : α ⊕ β // ¬x.isLeft}) := by
      change k < time σ yσ
      omega
    have hpow := pow_mul_sumCongr_right_succ_of_lt_time σ b x (k := k) hklt
    have hτreturn : ¬Sum.isLeft ((τ ^ time τ xτ) (.inr x)) := (time_spec τ xτ).2
    rw [hk] at hτreturn
    change ((σ * ((1 : Equiv.Perm α).sumCongr b)) ^ (k + 1)) (.inr x) =
      (σ ^ (k + 1)) (.inr (b x)) at hpow
    rw [hpow] at hτreturn
    exact not_return_of_lt_time (by omega : k + 1 < time σ yσ) ⟨by omega, hτreturn⟩

omit [DecidableEq α] [DecidableEq β] in
lemma trace_mul_sumCongr_right
    (σ : Equiv.Perm (α ⊕ β)) (b : Equiv.Perm β) :
    notIsLeftEquivRight.permCongr
      ((σ * ((1 : Equiv.Perm α).sumCongr b)).trace (Sum.isLeft ·)) =
    notIsLeftEquivRight.permCongr (σ.trace (Sum.isLeft ·)) * b := by
  ext x
  rw [Equiv.permCongr_apply, Equiv.Perm.mul_apply, Equiv.permCongr_apply]
  simp [Equiv.Perm.trace, Equiv.Perm.FirstReturn.map, notIsLeftEquivRight,
    time_mul_sumCongr_right σ b x, pow_mul_sumCongr_right_return_time σ b x]

omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
lemma pow_mul_sumCongr_right_eq_pow_of_mul_closed
    (σ : Equiv.Perm (α ⊕ β)) (b : Equiv.Perm β) (z : α ⊕ β)
    (hclosed : ¬Orbit.Meets (σ * ((1 : Equiv.Perm α).sumCongr b)) (fun x ↦ ¬Sum.isLeft x)
      (⟦z⟧ : (σ * ((1 : Equiv.Perm α).sumCongr b)).Orbit)) :
    ∀ n : ℕ, ((σ * ((1 : Equiv.Perm α).sumCongr b)) ^ n) z = (σ ^ n) z := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      let τ := σ * ((1 : Equiv.Perm α).sumCongr b)
      have hleft : Sum.isLeft ((τ ^ n) z) := by
        by_contra hright
        have hsame : τ.SameCycle z ((τ ^ n) z) := ⟨(n : ℤ), by rw [zpow_natCast]⟩
        exact hclosed ⟨⟨(τ ^ n) z, hright⟩, Quotient.sound hsame⟩
      rw [pow_succ', Equiv.Perm.mul_apply, ih]
      change σ (((1 : Equiv.Perm α).sumCongr b) ((σ ^ n) z)) = (σ ^ (n + 1)) z
      cases hσ : (σ ^ n) z with
      | inl a =>
          rw [pow_succ', Equiv.Perm.mul_apply]
          rw [hσ]
          rfl
      | inr c =>
          have : ¬Sum.isLeft ((τ ^ n) z) := by rw [ih, hσ]; simp
          exact False.elim (this hleft)

omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
lemma pow_mul_sumCongr_right_eq_pow_of_base_closed
    (σ : Equiv.Perm (α ⊕ β)) (b : Equiv.Perm β) (z : α ⊕ β)
    (hclosed : ¬Orbit.Meets σ (fun x ↦ ¬Sum.isLeft x) (⟦z⟧ : σ.Orbit)) :
    ∀ n : ℕ, ((σ * ((1 : Equiv.Perm α).sumCongr b)) ^ n) z = (σ ^ n) z := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      have hleft : Sum.isLeft ((σ ^ n) z) := by
        by_contra hright
        have hsame : σ.SameCycle z ((σ ^ n) z) := ⟨(n : ℤ), by rw [zpow_natCast]⟩
        exact hclosed ⟨⟨(σ ^ n) z, hright⟩, Quotient.sound hsame⟩
      rw [pow_succ', Equiv.Perm.mul_apply, ih]
      change σ (((1 : Equiv.Perm α).sumCongr b) ((σ ^ n) z)) = (σ ^ (n + 1)) z
      cases hσ : (σ ^ n) z with
      | inl a =>
          rw [pow_succ', Equiv.Perm.mul_apply]
          rw [hσ]
          rfl
      | inr c =>
          have : ¬Sum.isLeft ((σ ^ n) z) := by rw [hσ]; simp
          exact False.elim (this hleft)

omit [DecidableEq α] [DecidableEq β] in
lemma sameCycle_of_mul_sumCongr_right_closed
    (σ : Equiv.Perm (α ⊕ β)) (b : Equiv.Perm β) (z y : α ⊕ β)
    (hclosed : ¬Orbit.Meets (σ * ((1 : Equiv.Perm α).sumCongr b)) (fun x ↦ ¬Sum.isLeft x)
      (⟦z⟧ : (σ * ((1 : Equiv.Perm α).sumCongr b)).Orbit))
    (h : (σ * ((1 : Equiv.Perm α).sumCongr b)).SameCycle z y) :
    σ.SameCycle z y := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  refine ⟨(n : ℤ), ?_⟩
  rw [zpow_natCast]
  exact (pow_mul_sumCongr_right_eq_pow_of_mul_closed σ b z hclosed n).symm.trans hn

omit [DecidableEq α] [DecidableEq β] in
lemma sameCycle_mul_sumCongr_right_of_base_closed
    (σ : Equiv.Perm (α ⊕ β)) (b : Equiv.Perm β) (z y : α ⊕ β)
    (hclosed : ¬Orbit.Meets σ (fun x ↦ ¬Sum.isLeft x) (⟦z⟧ : σ.Orbit))
    (h : σ.SameCycle z y) :
    (σ * ((1 : Equiv.Perm α).sumCongr b)).SameCycle z y := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  refine ⟨(n : ℤ), ?_⟩
  rw [zpow_natCast]
  exact (pow_mul_sumCongr_right_eq_pow_of_base_closed σ b z hclosed n).trans hn

omit [DecidableEq α] [DecidableEq β] in
lemma sameCycle_mul_sumCongr_right_of_mul_closed
    (σ : Equiv.Perm (α ⊕ β)) (b : Equiv.Perm β) (z y : α ⊕ β)
    (hclosed : ¬Orbit.Meets (σ * ((1 : Equiv.Perm α).sumCongr b)) (fun x ↦ ¬Sum.isLeft x)
      (⟦z⟧ : (σ * ((1 : Equiv.Perm α).sumCongr b)).Orbit))
    (h : σ.SameCycle z y) :
    (σ * ((1 : Equiv.Perm α).sumCongr b)).SameCycle z y := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  refine ⟨(n : ℤ), ?_⟩
  rw [zpow_natCast]
  exact (pow_mul_sumCongr_right_eq_pow_of_mul_closed σ b z hclosed n).trans hn

omit [DecidableEq α] [DecidableEq β] in
lemma sameCycle_of_mul_sumCongr_right_base_closed
    (σ : Equiv.Perm (α ⊕ β)) (b : Equiv.Perm β) (z y : α ⊕ β)
    (hclosed : ¬Orbit.Meets σ (fun x ↦ ¬Sum.isLeft x) (⟦z⟧ : σ.Orbit))
    (h : (σ * ((1 : Equiv.Perm α).sumCongr b)).SameCycle z y) :
    σ.SameCycle z y := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  refine ⟨(n : ℤ), ?_⟩
  rw [zpow_natCast]
  exact (pow_mul_sumCongr_right_eq_pow_of_base_closed σ b z hclosed n).symm.trans hn

lemma closedCycles_mul_sumCongr_right
    (σ : Equiv.Perm (α ⊕ β)) (b : Equiv.Perm β) :
    (σ * ((1 : Equiv.Perm α).sumCongr b)).closedCycles (Sum.isLeft ·) =
      σ.closedCycles (Sum.isLeft ·) := by
  classical
  let τ := σ * ((1 : Equiv.Perm α).sumCongr b)
  let toClosed : Orbit.Closed τ (Sum.isLeft ·) → Orbit.Closed σ (Sum.isLeft ·) := fun q ↦
    let z := Quotient.out q.val
    ⟨⟦z⟧, by
      have hzq : (⟦z⟧ : τ.Orbit) = q.val := Quotient.out_eq q.val
      have hqclosed : ¬Orbit.Meets τ (fun x ↦ ¬Sum.isLeft x) (⟦z⟧ : τ.Orbit) := by
        intro hmeet
        exact q.property (hzq ▸ hmeet)
      change ¬Orbit.Meets σ (fun x ↦ ¬Sum.isLeft x) (⟦z⟧ : σ.Orbit)
      intro hmeet
      obtain ⟨y, hy⟩ := hmeet
      apply hqclosed
      refine ⟨y, ?_⟩
      exact Quotient.sound
        (sameCycle_mul_sumCongr_right_of_mul_closed σ b z y hqclosed (Quotient.eq.mp hy))⟩
  have hbij : Function.Bijective toClosed := by
    constructor
    · intro q r hqr
      apply Subtype.ext
      let zq := Quotient.out q.val
      let zr := Quotient.out r.val
      have hzq : (⟦zq⟧ : τ.Orbit) = q.val := Quotient.out_eq q.val
      have hzr : (⟦zr⟧ : τ.Orbit) = r.val := Quotient.out_eq r.val
      have hqclosed : ¬Orbit.Meets τ (fun x ↦ ¬Sum.isLeft x) (⟦zq⟧ : τ.Orbit) := by
        intro hmeet
        exact q.property (hzq ▸ hmeet)
      have hσ : σ.SameCycle zq zr := by
        have hval := congrArg Subtype.val hqr
        change (⟦zq⟧ : σ.Orbit) = ⟦zr⟧ at hval
        exact Quotient.eq.mp hval
      have hτ : τ.SameCycle zq zr :=
        sameCycle_mul_sumCongr_right_of_mul_closed σ b zq zr hqclosed hσ
      exact hzq.symm.trans ((Quotient.sound hτ).trans hzr)
    · intro q
      let z := Quotient.out q.val
      have hzq : (⟦z⟧ : σ.Orbit) = q.val := Quotient.out_eq q.val
      have hqclosed : ¬Orbit.Meets σ (fun x ↦ ¬Sum.isLeft x) (⟦z⟧ : σ.Orbit) := by
        intro hmeet
        exact q.property (hzq ▸ hmeet)
      let qτ : Orbit.Closed τ (Sum.isLeft ·) :=
        ⟨⟦z⟧, by
          change ¬Orbit.Meets τ (fun x ↦ ¬Sum.isLeft x) (⟦z⟧ : τ.Orbit)
          intro hmeet
          obtain ⟨y, hy⟩ := hmeet
          apply hqclosed
          refine ⟨y, ?_⟩
          exact Quotient.sound
            (sameCycle_of_mul_sumCongr_right_base_closed σ b z y hqclosed
              (Quotient.eq.mp hy))⟩
      refine ⟨qτ, ?_⟩
      apply Subtype.ext
      let w := Quotient.out (⟦z⟧ : τ.Orbit)
      have hwτ : (⟦w⟧ : τ.Orbit) = (⟦z⟧ : τ.Orbit) := Quotient.out_eq (⟦z⟧ : τ.Orbit)
      have hqτclosed : ¬Orbit.Meets τ (fun x ↦ ¬Sum.isLeft x) (⟦w⟧ : τ.Orbit) := by
        intro hmeet
        apply qτ.property
        change Orbit.Meets τ (fun x ↦ ¬Sum.isLeft x) (⟦z⟧ : τ.Orbit)
        exact hwτ ▸ hmeet
      have hσ : σ.SameCycle w z :=
        sameCycle_of_mul_sumCongr_right_closed σ b w z hqτclosed (Quotient.eq.mp hwτ)
      exact (Quotient.sound hσ).trans hzq
  unfold Equiv.Perm.closedCycles
  exact Fintype.card_of_bijective hbij

omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
@[simp] lemma subtypeExtend_delocate_IsLeftEquivLeft_symm (𝔞 : Project α) :
    (𝔞.delocate IsLeftEquivLeft.symm).subtypeExtend = 𝔞 + (1 : Project β) := by
  ext x
  · rfl
  · cases x <;> rfl

def trace (𝔣 : Project γ) (P : γ → Prop) [DecidablePred P] : Project {x : γ // ¬P x } where
  wager := 𝔣.wager + 𝔣.plot.closedCycles P
  plot := 𝔣.plot.trace P

variable {P : γ → Prop} [DecidablePred P]

@[simp] lemma trace_wager (𝔣 : Project γ) :
    (𝔣.trace P).wager = 𝔣.wager + 𝔣.plot.closedCycles P := rfl

lemma trace_plot (𝔣 : Project γ) :
    (𝔣.trace P).plot = 𝔣.plot.trace P := rfl

@[simp] lemma trace_tr (𝔣 : Project γ) :
    (𝔣.trace P).tr = 𝔣.wager + 𝔣.plot.closedCycles P + (𝔣.trace P).plot.tr := by
  simp [Project.tr, trace_wager, closedCycles]

def execution (𝔣 : Project γ) (𝔞 : Project {x : γ // P x}) : Project {x : γ // ¬P x } :=
  (𝔣 * 𝔞.subtypeExtend).trace P

@[simp] lemma execution_wager (𝔣 : Project γ) (𝔞 : Project {x : γ // P x}) :
    (𝔣.execution 𝔞).wager = 𝔣.wager + 𝔞.wager + (𝔣 * 𝔞.subtypeExtend).plot.closedCycles P := by
  simp [Project.execution, Project.trace]

def executionSum (𝔣 : Project (α ⊕ β)) (𝔞 : Project α) : Project β :=
  (execution 𝔣 (𝔞.delocate IsLeftEquivLeft.symm)).delocate notIsLeftEquivRight

scoped infix:60 " ∷ " => Project.executionSum

@[simp] lemma executionSum_wager (𝔣 : Project (α ⊕ β)) (𝔞 : Project α) :
    (𝔣 ∷ 𝔞).wager = 𝔣.wager + 𝔞.wager + (𝔣 * (𝔞 + (1 : Project β))).plot.closedCycles (Sum.isLeft ·) := by
  simp [Project.execution, Project.executionSum]

@[simp] lemma executionSum_tr (𝔣 : Project (α ⊕ β)) (𝔞 : Project α) :
    (𝔣 ∷ 𝔞).tr =
    𝔣.wager + 𝔞.wager +
    (𝔣 * (𝔞 + (1 : Project β))).plot.closedCycles (Sum.isLeft ·) +
    ((𝔣 * (𝔞 + (1 : Project β))).trace (Sum.isLeft ·)).plot.tr := by
  simp [Project.execution, Project.executionSum]

theorem execution_mul
    (𝔣 : Project γ) (𝔞 : Project {x : γ // P x}) (𝔟 : Project {x : γ // ¬P x}) :
    (𝔣.execution 𝔞) * 𝔟 = (𝔣 * 𝔟.subtypeExtend).execution 𝔞 := by
  ext
  · simp; sorry
  · simp [execution, trace, mul_plot]; sorry

theorem executionSum_mul
    (𝔣 : Project (α ⊕ β)) (𝔞 : Project α) (𝔟 : Project β) :
    (𝔣 ∷ 𝔞) * 𝔟 = 𝔣 * ((1 : Project α) + 𝔟) ∷ 𝔞 := by
  sorry

theorem execution_adjoint
    (𝔣 : Project (α ⊕ β)) (𝔞 : Project α) (𝔟 : Project β) :
    ⟪𝔣 | 𝔞 + 𝔟⟫ = ⟪𝔣 ∷ 𝔞 | 𝔟⟫ := by
  classical
  let 𝔣𝔟 : Project (α ⊕ β) := 𝔣 * ((1 : Project α) + 𝔟)
  let 𝔣𝔟𝔞 := 𝔣𝔟 * (𝔞 + (1 : Project β))
  have 𝔣𝔟_wager : 𝔣𝔟.wager = 𝔣.wager + 𝔟.wager := by simp [𝔣𝔟]
  have e3 : (𝔣 ∷ 𝔞) * 𝔟 = 𝔣𝔟 ∷ 𝔞 := by
    have hproj :
        𝔣𝔟 * (𝔞 + (1 : Project β)) =
          (𝔣 * (𝔞 + (1 : Project β))) * ((1 : Project α) + 𝔟) := by
      calc
        𝔣𝔟 * (𝔞 + (1 : Project β))
            = (𝔣 * ((1 : Project α) + 𝔟)) * (𝔞 + (1 : Project β)) := rfl
        _ = 𝔣 * (((1 : Project α) + 𝔟) * (𝔞 + (1 : Project β))) := by
          rw [mul_assoc]
        _ = 𝔣 * (𝔞 + 𝔟) := by
          rw [add_mul_add, one_mul, mul_one]
        _ = 𝔣 * ((𝔞 + (1 : Project β)) * ((1 : Project α) + 𝔟)) := by
          rw [add_mul_add, mul_one, one_mul]
        _ = (𝔣 * (𝔞 + (1 : Project β))) * ((1 : Project α) + 𝔟) := by
          rw [mul_assoc]
    have hclosed :
        (𝔣𝔟 * (𝔞 + (1 : Project β))).plot.closedCycles (Sum.isLeft ·) =
          (𝔣 * (𝔞 + (1 : Project β))).plot.closedCycles (Sum.isLeft ·) := by
      rw [hproj, Project.mul_plot, Project.add_plot, one_plot]
      exact closedCycles_mul_sumCongr_right ((𝔣 * (𝔞 + (1 : Project β))).plot) 𝔟.plot
    have htrace :
        notIsLeftEquivRight.permCongr
            (((𝔣 * (𝔞 + (1 : Project β))) * ((1 : Project α) + 𝔟)).plot.trace
              (Sum.isLeft ·)) =
          notIsLeftEquivRight.permCongr
              ((𝔣 * (𝔞 + (1 : Project β))).plot.trace (Sum.isLeft ·)) * 𝔟.plot := by
      rw [Project.mul_plot, Project.add_plot, one_plot]
      exact trace_mul_sumCongr_right ((𝔣 * (𝔞 + (1 : Project β))).plot) 𝔟.plot
    ext x
    · simp [Project.executionSum, Project.execution, hclosed]
      omega
    · calc
        ((𝔣 ∷ 𝔞) * 𝔟).plot x =
            (notIsLeftEquivRight.permCongr
                ((𝔣 * (𝔞 + (1 : Project β))).plot.trace (Sum.isLeft ·)) *
              𝔟.plot) x := by
          simp [Project.executionSum, Project.execution, Project.trace_plot, Project.mul_plot,
            Project.delocate_plot]
        _ =
            (notIsLeftEquivRight.permCongr
              (((𝔣 * (𝔞 + (1 : Project β))) * ((1 : Project α) + 𝔟)).plot.trace
                (Sum.isLeft ·))) x := by
          rw [htrace]
        _ = (𝔣𝔟 ∷ 𝔞).plot x := by
          simp [Project.executionSum, Project.execution, Project.trace_plot, Project.delocate_plot,
            hproj]
  have e1 : (𝔣𝔟 ∷ 𝔞).tr = 𝔣.wager + 𝔞.wager + 𝔟.wager + (𝔣𝔟𝔞.trace (Sum.isLeft ·)).plot.tr + 𝔣𝔟𝔞.plot.closedCycles (Sum.isLeft ·) := by
    simp [𝔣𝔟_wager, 𝔣𝔟𝔞, ]; omega
  have e2 : (𝔣 * (𝔞 + 𝔟)).tr = 𝔣.wager + 𝔞.wager + 𝔟.wager + 𝔣𝔟𝔞.plot.tr := by
    simp [𝔣𝔟𝔞, 𝔣𝔟 , tr, add_mul_add]; omega
  calc
    ⟪𝔣 | 𝔞 + 𝔟⟫ = 𝔣.wager + 𝔞.wager + 𝔟.wager + 𝔣𝔟𝔞.plot.tr := by simpa [measurement] using e2
              _ = 𝔣.wager + 𝔞.wager + 𝔟.wager + (𝔣𝔟𝔞.trace (Sum.isLeft ·)).plot.tr + 𝔣𝔟𝔞.plot.closedCycles (Sum.isLeft ·) := by
                simp [tr_eq_trace_tr_add_closedCycles 𝔣𝔟𝔞.plot (P := (Sum.isLeft ·)), trace_plot];
                omega
              _ = (𝔣𝔟 ∷ 𝔞).tr := by symm; exact e1
              _ = ⟪𝔣 ∷ 𝔞 | 𝔟⟫ := by unfold measurement; simp [e3]

end Project

/-! ### Polarity and Conduct -/

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

def poler (A : Set (Project α)) : Set (Project α) :=
  {𝔟 | ∀ 𝔞 ∈ A, 𝔞 ⟂ 𝔟}

scoped postfix:max "ᗮ" => poler

def IsConduct (A : Set (Project α)) : Prop :=
  A = Aᗮᗮ

structure Conduct (α : Type*) [Fintype α] [DecidableEq α] where
  set : Set (Project α)
  set_isConduct : IsConduct set

instance : SetLike (Conduct α) (Project α) where
  coe := Conduct.set
  coe_injective p q h := by cases p; cases q; congr

@[simp] lemma mem_poler_iff (A : Set (Project α)) (𝔟 : Project α) :
    𝔟 ∈ Aᗮ ↔ ∀ 𝔞 ∈ A, 𝔞 ⟂ 𝔟 := by rfl

@[simp] lemma tripoler_eq_poler (A : Set (Project α)) : Aᗮᗮᗮ = Aᗮ := by
  ext 𝔟; simp; grind

@[simp] lemma subset_bipoler (A : Set (Project α)) : A ⊆ Aᗮᗮ := by
  intro 𝔞 h𝔞; simp; grind

lemma isConduct_iff_subset_bipoler {A : Set (Project α)} : IsConduct A ↔ Aᗮᗮ ⊆ A := by
  simp [IsConduct, subset_antisymm_iff]

@[simp] lemma poler_isConduct (A : Set (Project α)) : IsConduct Aᗮ := by
  simp [IsConduct]

namespace Conduct

def tensor (A : Conduct α) (B : Conduct β) : Conduct (α ⊕ β) where
  set := {𝔠 | ∃ 𝔞 ∈ A, ∃ 𝔟 ∈ B, 𝔠 = 𝔞 + 𝔟}ᗮᗮ
  set_isConduct := by simp

def par (A : Conduct α) (B : Conduct β) : Conduct (α ⊕ β) where
  set := {𝔠 | ∃ 𝔞 ∈ Aᗮ, ∃ 𝔟 ∈ Bᗮ, 𝔠 = 𝔞 + 𝔟}ᗮ
  set_isConduct := by simp

end Conduct

/-! ### Successful Project -/

structure Project.IsSuccessful (𝔞 : Project α) : Prop where
  square_eq_one : 𝔞 * 𝔞 = 1
  trace_zero : 𝔞.plot.support = Finset.univ

def Conduct.IsSuccessful (A : Conduct α) : Prop :=
  ∃ 𝔞 ∈ A, 𝔞.IsSuccessful

end GoI

end LO.Propositional.LinearLogic.Multiplicative
