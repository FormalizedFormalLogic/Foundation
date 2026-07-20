module

public import Foundation.LinearLogic.MLL.Propositional
public import Foundation.Vorspiel.Algebra.IsNilpotent
public import Foundation.Vorspiel.GroupTheory.Perm

/-!
# A Toy Model of Geometry of Interaction
-/

@[expose] public section

namespace LO.Propositional.LinearLogic.Multiplicative

namespace GoI

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

@[simp] lemma add_plot (𝔞 : Project α) (𝔟 : Project β) :
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
  plot := 𝔞.plot.trans 𝔟.plot

instance : Mul (Project α) where
  mul := mul

@[simp] lemma mul_wager (𝔞 𝔟 : Project α) :
    (𝔞 * 𝔟).wager = 𝔞.wager + 𝔟.wager := rfl

lemma mul_plot (𝔞 𝔟 : Project α) :
    (𝔞 * 𝔟).plot = 𝔞.plot.trans 𝔟.plot := rfl

@[simp] lemma mul_one (𝔞 : Project α) : 𝔞 * 1 = 𝔞 := by
  ext <;> simp [mul_plot, one_plot]

@[simp] lemma mul_assoc (𝔞 𝔟 𝔠 : Project α) :
    (𝔞 * 𝔟) * 𝔠 = 𝔞 * (𝔟 * 𝔠) := by
  ext <;> simp [mul_plot, add_assoc, Equiv.trans_assoc]

def delocate (𝔞 : Project α) (φ : α ≃ β) : Project β where
  wager := 𝔞.wager
  plot := φ.symm.trans (𝔞.plot.trans φ)

@[simp] lemma delocate_wager (𝔞 : Project α) (φ : α ≃ β) :
    (𝔞.delocate φ).wager = 𝔞.wager := rfl

lemma delocate_plot (𝔞 : Project α) (φ : α ≃ β) :
    (𝔞.delocate φ).plot = φ.symm.trans (𝔞.plot.trans φ) := rfl

end Project

/-! ### Measurement and polarity -/

def Project.cycles [Fintype α] [DecidableEq α] (𝔞 𝔟 : Project α) : (Fintype.card α).Partition :=
  (𝔞 * 𝔟).plot.partition

def Project.measurement [Fintype α] [DecidableEq α] (𝔞 𝔟 : Project α) : ℕ :=
  𝔞.wager + 𝔟.wager + (𝔞.cycles 𝔟).parts.card

scoped notation "⟪" 𝔞 " | " 𝔟 "⟫" => Project.measurement 𝔞 𝔟

def Project.IsPolar [Fintype α] [DecidableEq α] (𝔞 𝔟 : Project α) : Prop :=
  ⟪𝔞 | 𝔟⟫ = 1

scoped infix:50 " ⟂ " => Project.IsPolar

namespace Project

variable {α : Type*} [Fintype α] [DecidableEq α]

lemma cycles_comm (𝔞 𝔟 : Project α) :
    𝔞.cycles 𝔟 = 𝔟.cycles 𝔞 := by
  apply Equiv.Perm.partition_eq_of_isConj.mp
  rw [isConj_iff]
  refine ⟨𝔞.plot, ?_⟩
  change 𝔞.plot * (𝔟.plot * 𝔞.plot) * 𝔞.plot⁻¹ = 𝔞.plot * 𝔟.plot
  group

lemma measurement_comm (𝔞 𝔟 : Project α) :
    ⟪𝔞 | 𝔟⟫ = ⟪𝔟 | 𝔞⟫ := by
  simp [Project.measurement, cycles_comm]
  grind

@[symm, grind =] lemma isPolar_symm {𝔞 𝔟 : Project α} :
    𝔞 ⟂ 𝔟 ↔ 𝔟 ⟂ 𝔞 := by
  simp [Project.IsPolar, measurement_comm]

/-! ### Projects -/

def fax (α : Type*) : Project (α ⊕ α) where
  wager := 0
  plot := Equiv.sumComm α α

@[simp] lemma fax_wager (α : Type*) : (fax α).wager = 0 := rfl

@[simp] lemma measurement_fax_one : ⟪fax α | 1⟫ = Fintype.card α := by
  suffices h : (Equiv.Perm.partition (Equiv.sumComm α α)).parts.card = Fintype.card α by
    simpa [Project.measurement, Project.cycles, fax] using h
  have hsupp : Equiv.Perm.support (Equiv.sumComm α α) = Finset.univ := by
    ext (_ | _) <;> simp [Equiv.Perm.mem_support]
  have hpow : (Equiv.sumComm α α : Equiv.Perm (α ⊕ α)) ^ 2 = 1 := by
    ext (_ | _) <;> rfl
  have hsum := Equiv.Perm.sum_cycleType (Equiv.sumComm α α)
  rw [Equiv.Perm.cycleType_of_pow_prime_eq_one hpow] at hsum
  simp_all [Equiv.Perm.parts_partition, Multiset.sum_replicate, Nat.mul_two]
  grind

def daimon (r : ℕ) : Project PEmpty where
  wager := r
  plot := default

def permApp (F : Equiv.Perm (α ⊕ β)) (A : Equiv.Perm α) : Equiv.Perm (α ⊕ β) :=
  F.trans (A.sumCongr (Equiv.refl _))

def notIsLeftEquivRight : { x : α ⊕ β // ¬x.isLeft} ≃ β where
  toFun := fun x ↦ x.val.getRight (by simpa using x.2)
  invFun := fun b ↦ ⟨.inr b, by simp⟩
  left_inv := by
    rintro ⟨_ | _, hx⟩
    · simp at hx
    · rfl
  right_inv := fun _ ↦ rfl

def executionAux [DecidableEq β] [Fintype β]
    (𝔣 : Project (α ⊕ β)) (𝔞 : Project α) : Project { x : α ⊕ β // ¬x.isLeft} where
  wager := 𝔣.wager + 𝔞.wager + (permApp 𝔣.plot 𝔞.plot).closedCycles (Sum.isLeft ·)
  plot := (permApp 𝔣.plot 𝔞.plot).trace (Sum.isLeft ·)

def execution [DecidableEq β] [Fintype β]
    (𝔣 : Project (α ⊕ β)) (𝔞 : Project α) : Project β :=
  (executionAux 𝔣 𝔞).delocate notIsLeftEquivRight

scoped infix:80 " ∷ " => Project.execution

lemma execution_wager [DecidableEq β] [Fintype β]
    (𝔣 : Project (α ⊕ β)) (𝔞 : Project α) :
    (𝔣 ∷ 𝔞).wager = 𝔣.wager + 𝔞.wager + (permApp 𝔣.plot 𝔞.plot).closedCycles (Sum.isLeft ·) := by
  simp [Project.execution, Project.executionAux, Project.delocate]

omit [DecidableEq α] in
private lemma pow_trans_sumCongr_right_of_lt_return [DecidableEq β] [Fintype β]
    (π : Equiv.Perm (α ⊕ β)) (b : Equiv.Perm β) (x : β)
    {k : ℕ}
    (hk : k < Equiv.Perm.FirstReturn.time π (⟨.inr x, by simp⟩ :
        {x : α ⊕ β // ¬x.isLeft})) :
    ((π.trans ((Equiv.refl α).sumCongr b) : Equiv.Perm (α ⊕ β)) ^ k) (.inr x) =
      (π ^ k) (.inr x) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      rcases k with _ | k
      · rfl
      · have hk' :
            k < Equiv.Perm.FirstReturn.time π (⟨.inr x, by simp⟩ :
              {x : α ⊕ β // ¬x.isLeft}) := Nat.lt_trans (Nat.lt_succ_self k) hk
        have hleft : Sum.isLeft ((π ^ (k + 1)) (.inr x)) := by
          by_contra hright
          exact Equiv.Perm.FirstReturn.not_return_of_lt_time hk
            ⟨Nat.succ_pos k, hright⟩
        rw [pow_succ', Equiv.Perm.mul_apply, ih k (Nat.lt_succ_self k) hk']
        change ((Equiv.refl α).sumCongr b) (π ((π ^ k) (.inr x))) =
          (π ^ (k + 1)) (.inr x)
        rw [pow_succ', Equiv.Perm.mul_apply]
        cases hπ : (π ^ (k + 1)) (.inr x) with
        | inl a =>
            have hstep : π ((π ^ k) (.inr x)) = Sum.inl a := by
              simpa [pow_succ', Equiv.Perm.mul_apply] using hπ
            rw [hstep]
            simp
        | inr c =>
            simp [hπ] at hleft

omit [DecidableEq α] in
private lemma pow_trans_sumCongr_right_return [DecidableEq β] [Fintype β]
    (π : Equiv.Perm (α ⊕ β)) (b : Equiv.Perm β) (x : β) :
    let n := Equiv.Perm.FirstReturn.time π (⟨.inr x, by simp⟩ :
      {x : α ⊕ β // ¬x.isLeft})
    ((π.trans ((Equiv.refl α).sumCongr b) : Equiv.Perm (α ⊕ β)) ^ n) (.inr x) =
      ((Equiv.refl α).sumCongr b) ((π ^ n) (.inr x)) := by
  intro n
  have hn : 0 < n :=
    (Equiv.Perm.FirstReturn.time_spec π
      (⟨.inr x, by simp⟩ : {x : α ⊕ β // ¬x.isLeft})).1
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [hm, pow_succ', Equiv.Perm.mul_apply]
  have hm_lt :
      m < Equiv.Perm.FirstReturn.time π
        (⟨.inr x, by simp⟩ : {x : α ⊕ β // ¬x.isLeft}) := by
    change m < n
    omega
  rw [pow_trans_sumCongr_right_of_lt_return π b x hm_lt]
  change (π.trans ((Equiv.refl α).sumCongr b) : Equiv.Perm (α ⊕ β))
      ((π ^ m) (.inr x)) =
    ((Equiv.refl α).sumCongr b) ((π ^ (m + 1)) (.inr x))
  rw [pow_succ', Equiv.Perm.mul_apply]
  rfl

omit [DecidableEq α] in
private lemma time_trans_sumCongr_right [DecidableEq β] [Fintype β]
    (π : Equiv.Perm (α ⊕ β)) (b : Equiv.Perm β) (x : β) :
    Equiv.Perm.FirstReturn.time
        (π.trans ((Equiv.refl α).sumCongr b) : Equiv.Perm (α ⊕ β))
        (⟨.inr x, by simp⟩ : {x : α ⊕ β // ¬x.isLeft}) =
      Equiv.Perm.FirstReturn.time π
        (⟨.inr x, by simp⟩ : {x : α ⊕ β // ¬x.isLeft}) := by
  let y : {x : α ⊕ β // ¬x.isLeft} := ⟨.inr x, by simp⟩
  let σ : Equiv.Perm (α ⊕ β) := π.trans ((Equiv.refl α).sumCongr b)
  let n := Equiv.Perm.FirstReturn.time π y
  have hn : 0 < n := (Equiv.Perm.FirstReturn.time_spec π y).1
  have hπn : ¬Sum.isLeft ((π ^ n) (.inr x)) := (Equiv.Perm.FirstReturn.time_spec π y).2
  have hσn : ¬Sum.isLeft ((σ ^ n) (.inr x)) := by
    rw [show σ = (π.trans ((Equiv.refl α).sumCongr b) : Equiv.Perm (α ⊕ β)) from rfl]
    rw [pow_trans_sumCongr_right_return π b x]
    cases hπ : (π ^ n) (.inr x) with
    | inl a => simp [hπ] at hπn
    | inr c => simp
  apply le_antisymm
  · exact Equiv.Perm.FirstReturn.time_le_of_return ⟨hn, hσn⟩
  · by_contra hle
    have hlt :
        Equiv.Perm.FirstReturn.time σ y < n := Nat.lt_of_not_ge hle
    have hpow :=
      pow_trans_sumCongr_right_of_lt_return π b x hlt
    have hσreturn : ¬Sum.isLeft ((σ ^ Equiv.Perm.FirstReturn.time σ y) (.inr x)) :=
      (Equiv.Perm.FirstReturn.time_spec σ y).2
    exact Equiv.Perm.FirstReturn.not_return_of_lt_time hlt
      ⟨(Equiv.Perm.FirstReturn.time_spec σ y).1, by rwa [← hpow]⟩

lemma closedCycles_trans_sumCongr_right [DecidableEq β] [Fintype β]
    (π : Equiv.Perm (α ⊕ β)) (b : Equiv.Perm β) :
    Equiv.Perm.closedCycles
        (π.trans ((Equiv.refl α).sumCongr b) : Equiv.Perm (α ⊕ β)) (Sum.isLeft ·) =
      π.closedCycles (Sum.isLeft ·) := by
  sorry

omit [DecidableEq α] in
lemma trace_trans_sumCongr_right [DecidableEq β] [Fintype β]
    (π : Equiv.Perm (α ⊕ β)) (b : Equiv.Perm β) :
    notIsLeftEquivRight.permCongr
      (Equiv.Perm.trace
        (π.trans ((Equiv.refl α).sumCongr b) : Equiv.Perm (α ⊕ β)) (Sum.isLeft ·)) =
    (notIsLeftEquivRight.permCongr (π.trace (Sum.isLeft ·))).trans b := by
  ext x
  rw [Equiv.permCongr_apply, Equiv.trans_apply, Equiv.permCongr_apply]
  simp [Equiv.Perm.trace, Equiv.Perm.FirstReturn.map, notIsLeftEquivRight,
    time_trans_sumCongr_right π b x, pow_trans_sumCongr_right_return π b x]
  let z :=
    (π ^ Equiv.Perm.FirstReturn.time π
      (⟨.inr x, by simp⟩ : {x : α ⊕ β // ¬x.isLeft})) (.inr x)
  have hznotLeft : ¬Sum.isLeft z :=
    (Equiv.Perm.FirstReturn.time_spec π
      (⟨.inr x, by simp⟩ : {x : α ⊕ β // ¬x.isLeft})).2
  have hzright : Sum.isRight z := by
    unfold z at hznotLeft ⊢
    cases hπ : (π ^ Equiv.Perm.FirstReturn.time π
        (⟨.inr x, by simp⟩ : {x : α ⊕ β // ¬x.isLeft})) (.inr x) with
    | inl a => simp [hπ] at hznotLeft
    | inr c => rfl
  change Sum.map id b z = Sum.inr (b (z.getRight _))
  calc
    Sum.map id b z = Sum.map id b (Sum.inr (z.getRight hzright)) := by
      rw [Sum.inr_getRight z hzright]
    _ = Sum.inr (b (z.getRight hzright)) := rfl
    _ = Sum.inr (b (z.getRight _)) := by
      congr

theorem execution_adjoint [DecidableEq β] [Fintype β]
    (𝔣 : Project (α ⊕ β)) (𝔞 : Project α) (𝔟 : Project β) :
    ⟪𝔣 | 𝔞 + 𝔟⟫ = ⟪𝔣 ∷ 𝔞 | 𝔟⟫ := by
  suffices
    (𝔣.cycles (𝔞 + 𝔟)).parts.card =
    ((𝔣 ∷ 𝔞).cycles 𝔟).parts.card + (permApp 𝔣.plot 𝔞.plot).closedCycles (Sum.isLeft ·) by
      simp [execution_wager, Project.measurement]; omega
  let σ : Equiv.Perm (α ⊕ β) :=
    (permApp 𝔣.plot 𝔞.plot).trans ((Equiv.refl α).sumCongr 𝔟.plot)
  have h :=
    Equiv.Perm.partition_card_eq_trace_partition_card_add_closedCycles
      (P := (Sum.isLeft ·)) σ
  have htrace :
      (Equiv.Perm.trace σ (Sum.isLeft ·)).partition.parts.card =
        ((𝔣 ∷ 𝔞).cycles 𝔟).parts.card := by
    calc
      (Equiv.Perm.trace σ (Sum.isLeft ·)).partition.parts.card
          = (notIsLeftEquivRight.permCongr
              (Equiv.Perm.trace σ (Sum.isLeft ·))).partition.parts.card := by
        exact (Equiv.Perm.Orbit.partition_parts_card_permCongr
          notIsLeftEquivRight (Equiv.Perm.trace σ (Sum.isLeft ·))).symm
      _ = (Equiv.Perm.partition
              ((notIsLeftEquivRight.permCongr
                ((permApp 𝔣.plot 𝔞.plot).trace (Sum.isLeft ·))).trans 𝔟.plot :
                  Equiv.Perm β)).parts.card := by
        rw [show σ =
            (permApp 𝔣.plot 𝔞.plot).trans ((Equiv.refl α).sumCongr 𝔟.plot) from rfl]
        rw [trace_trans_sumCongr_right]
      _ = ((𝔣 ∷ 𝔞).cycles 𝔟).parts.card := by
        simp [Project.cycles, Project.execution, Project.executionAux, Project.delocate,
          Project.mul_plot, Equiv.permCongr_def, permApp, Equiv.trans_assoc]
  have hclosed :
      Equiv.Perm.closedCycles σ (Sum.isLeft ·) =
        (permApp 𝔣.plot 𝔞.plot).closedCycles (Sum.isLeft ·) := by
    rw [show σ =
        (permApp 𝔣.plot 𝔞.plot).trans ((Equiv.refl α).sumCongr 𝔟.plot) from rfl]
    exact closedCycles_trans_sumCongr_right (permApp 𝔣.plot 𝔞.plot) 𝔟.plot
  calc
    (𝔣.cycles (𝔞 + 𝔟)).parts.card
        = (Equiv.Perm.partition σ).parts.card := by
      simp [Project.cycles, Project.mul_plot, Project.add_plot, permApp, σ, Equiv.trans_assoc]
    _ = (Equiv.Perm.trace σ (Sum.isLeft ·)).partition.parts.card +
          Equiv.Perm.closedCycles σ (Sum.isLeft ·) := h
    _ = ((𝔣 ∷ 𝔞).cycles 𝔟).parts.card +
          (permApp 𝔣.plot 𝔞.plot).closedCycles (Sum.isLeft ·) := by
      rw [htrace, hclosed]

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
