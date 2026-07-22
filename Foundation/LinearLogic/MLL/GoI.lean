module

public import Foundation.LinearLogic.MLL.Propositional
public import Foundation.Vorspiel.Algebra.IsNilpotent
public import Foundation.Vorspiel.GroupTheory.Perm

/-!
# A Simplified Geometry of Interaction

## References
- [Jean-Yves Girard, *Geometry of interaction. V: Logic in the hyperfinite factor*][Gir11]
- [Thomas Seiller, *Interaction graphs: multiplicatives*][Sei12]
-/

@[expose] public section

namespace LO.Propositional.LinearLogic.Multiplicative.GoI

open Equiv.Perm

/-! ### Project -/

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

@[simp] lemma delocate_mul (𝔞 𝔟 : Project α) (φ : α ≃ β) :
    (𝔞 * 𝔟).delocate φ = 𝔞.delocate φ * 𝔟.delocate φ := by
  ext x
  · rfl
  · simp [delocate_plot, mul_plot]

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

/-! ### Measurement and Polarity -/

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

omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
@[simp] lemma subtypeExtend_delocate_IsLeftEquivLeft_symm (𝔞 : Project α) :
    (𝔞.delocate IsLeftEquivLeft.symm).subtypeExtend = 𝔞 + (1 : Project β) := by
  ext x
  · rfl
  · cases x <;> rfl

omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
@[simp] lemma subtypeExtend_delocate_notIsLeftEquivRight_symm (𝔟 : Project β) :
    (𝔟.delocate notIsLeftEquivRight.symm).subtypeExtend = (1 : Project α) + 𝔟 := by
  ext x
  · simp
  · cases x <;> rfl

/-! ### Execution and Adjoint -/

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

scoped[LO.Propositional.LinearLogic.Multiplicative.GoI] infix:60 " ∷ " => Project.executionSum

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
  ext x
  · have hclosed :=
      Equiv.Perm.closedCycles_mul_subtypeCongr_not_mul_subtypeCongr
        (P := P) 𝔣.plot 𝔞.plot 𝔟.plot
    simp [execution, trace, mul_plot, subtypeExtend, hclosed]
    omega
  · have htrace :=
      (Equiv.Perm.trace_mul_subtypeCongr_not_mul_subtypeCongr
        (P := P) 𝔣.plot 𝔞.plot 𝔟.plot).symm
    simpa [execution, trace, mul_plot, subtypeExtend] using
      congrArg (fun σ : Equiv.Perm {x : γ // ¬P x} ↦ (σ x : γ)) htrace

theorem executionSum_mul
    (𝔣 : Project (α ⊕ β)) (𝔞 : Project α) (𝔟 : Project β) :
    (𝔣 ∷ 𝔞) * 𝔟 = 𝔣 * ((1 : Project α) + 𝔟) ∷ 𝔞 := by
  let 𝔞' : Project {x : α ⊕ β // x.isLeft} :=
    𝔞.delocate IsLeftEquivLeft.symm
  let 𝔟' : Project {x : α ⊕ β // ¬x.isLeft} :=
    𝔟.delocate notIsLeftEquivRight.symm
  have h := congrArg (fun 𝔠 ↦ 𝔠.delocate notIsLeftEquivRight)
    (execution_mul 𝔣 𝔞' 𝔟')
  have hb : 𝔟'.delocate notIsLeftEquivRight = 𝔟 := by
    ext x <;> simp [𝔟', delocate_plot]
  simpa [executionSum, 𝔞', 𝔟', hb, delocate_comp] using h

theorem execution_adjoint
    (𝔣 : Project (α ⊕ β)) (𝔞 : Project α) (𝔟 : Project β) :
    ⟪𝔣 | 𝔞 + 𝔟⟫ = ⟪𝔣 ∷ 𝔞 | 𝔟⟫ := by
  classical
  let 𝔣𝔟 : Project (α ⊕ β) := 𝔣 * ((1 : Project α) + 𝔟)
  let 𝔣𝔟𝔞 := 𝔣𝔟 * (𝔞 + (1 : Project β))
  have 𝔣𝔟_wager : 𝔣𝔟.wager = 𝔣.wager + 𝔟.wager := by simp [𝔣𝔟]
  calc
    ⟪𝔣 | 𝔞 + 𝔟⟫ = (𝔣 * (𝔞 + 𝔟)).tr                          := by unfold measurement; rfl
              _ = 𝔣.wager + 𝔞.wager + 𝔟.wager + 𝔣𝔟𝔞.plot.tr := by simp [𝔣𝔟𝔞, 𝔣𝔟 , tr, add_mul_add]; omega
              _ = 𝔣.wager + 𝔞.wager + 𝔟.wager
                  + (𝔣𝔟𝔞.trace (Sum.isLeft ·)).plot.tr
                  + 𝔣𝔟𝔞.plot.closedCycles (Sum.isLeft ·)    := by simp [tr_eq_trace_tr_add_closedCycles 𝔣𝔟𝔞.plot (P := (Sum.isLeft ·)), trace_plot]; omega
              _ = (𝔣𝔟 ∷ 𝔞).tr                               := by simp [𝔣𝔟_wager, 𝔣𝔟𝔞, ]; omega
              _ = ((𝔣 ∷ 𝔞) * 𝔟).tr                          := by simp [𝔣𝔟, executionSum_mul 𝔣 𝔞 𝔟]
              _ = ⟪𝔣 ∷ 𝔞 | 𝔟⟫                               := by unfold measurement; rfl

@[grind =] theorem execution_adjoint_polar
    (𝔣 : Project (α ⊕ β)) (𝔞 : Project α) (𝔟 : Project β) :
    𝔣 ∷ 𝔞 ⟂ 𝔟 ↔ 𝔣 ⟂ 𝔞 + 𝔟 := by
  simp [Project.IsPolar, execution_adjoint]

end Project

/-! ### Conducts -/

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

open Project

@[grind =] lemma set_polar_polar (A : Conduct α) : A.setᗮᗮ = A.set := by
  symm; simpa [IsConduct] using A.set_isConduct

@[grind =, simp] lemma mem_set_polar_polar (A : Conduct α) : a ∈ A.setᗮᗮ ↔ a ∈ A := by
  simp [set_polar_polar]; rfl

def tensor (A : Conduct α) (B : Conduct β) : Conduct (α ⊕ β) where
  set := {𝔠 | ∃ 𝔞 ∈ A, ∃ 𝔟 ∈ B, 𝔠 = 𝔞 + 𝔟}ᗮᗮ
  set_isConduct := by simp

def par (A : Conduct α) (B : Conduct β) : Conduct (α ⊕ β) where
  set := {𝔠 | ∃ 𝔞 ∈ Aᗮ, ∃ 𝔟 ∈ Bᗮ, 𝔠 = 𝔞 + 𝔟}ᗮ
  set_isConduct := by simp

def lollipop (A : Conduct α) (B : Conduct β) : Conduct (α ⊕ β) where
  set := {𝔣 | ∀ 𝔞 ∈ A, 𝔣 ∷ 𝔞 ∈ B}
  set_isConduct := isConduct_iff_subset_bipoler.mpr <| by
    intro 𝔣 H 𝔞 h𝔞
    suffices ∀ 𝔟', (∀ 𝔟 ∈ B, 𝔟 ⟂ 𝔟') → 𝔟' ⟂ 𝔣 ∷ 𝔞 by
      have : 𝔣 ∷ 𝔞 ∈ B.setᗮᗮ := by simpa
      grind
    intro 𝔟' h𝔟'
    have H : ∀ 𝔠', (∀ 𝔠, (∀ 𝔞 ∈ A, 𝔠 ∷ 𝔞 ∈ B) → 𝔠 ⟂ 𝔠') → 𝔠' ⟂ 𝔣 := by simpa using H
    have : 𝔞 + 𝔟' ⟂ 𝔣 := H (𝔞 + 𝔟') fun 𝔠 h𝔠 ↦ by
      simpa [←execution_adjoint_polar] using h𝔟' _ (h𝔠 𝔞 h𝔞)
    grind

end Conduct

/-! ### Successful Projects and Conducts -/

structure Project.IsSuccessful (𝔞 : Project α) : Prop where
  square_eq_one : 𝔞 * 𝔞 = 1
  trace_zero : 𝔞.plot.support = Finset.univ

def Conduct.IsSuccessful (A : Conduct α) : Prop :=
  ∃ 𝔞 ∈ A, 𝔞.IsSuccessful

end GoI

end LO.Propositional.LinearLogic.Multiplicative
