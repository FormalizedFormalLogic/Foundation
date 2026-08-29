module

public import Foundation.FirstOrder.Arithmetic.HFS.PRF

/-!

# Superexponential Function in $\mathsf{I} \Sigma_1$

-/

@[expose] public section

namespace LO.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

section iterExp

def iterExp.blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y x. y = x”
  succ := .mkSigma “y ih n x. !(expDef.ofZero 𝚺₁) y ih”

noncomputable def iterExp.construction : PR.Construction V iterExp.blueprint where
  zero := fun v ↦ v 0
  succ := fun _ _ ih ↦ Exp.exp ih
  zero_defined := .mk fun v ↦ by simp [iterExp.blueprint]
  succ_defined := .mk fun v ↦ by simp [iterExp.blueprint, expDef, exponential_graph]

/-- `iterExp x y = 2^x_y` (iterated exponentiation). -/
noncomputable def iterExp (x y : V) : V := iterExp.construction.result ![x] y

@[simp] lemma iterExp_zero (x : V) : iterExp x 0 = x := by simp [iterExp, iterExp.construction]

@[simp] lemma iterExp_succ (x y : V) : iterExp x (y + 1) = Exp.exp (iterExp x y) := by
  simp [iterExp, iterExp.construction]

def _root_.LO.FirstOrder.Arithmetic.iterExpDef : 𝚺₁.Semisentence 3 :=
  iterExp.blueprint.resultDef |>.rew (Rew.subst ![#0, #2, #1])

instance iterExp_defined : 𝚺₁-Function₂[V] iterExp via iterExpDef := .mk
  fun v ↦ by simp [iterExp.construction.result_defined_iff, iterExpDef]; rfl

instance iterExp_definable : 𝚺₁-Function₂[V] iterExp := iterExp_defined.to_definable

instance iterExp_definable' (Γ) : Γ-[m + 1]-Function₂ (iterExp : V → V → V) := iterExp_definable.of_sigmaOne

end iterExp

section superexp

noncomputable instance : Superexp V := ⟨fun x ↦ iterExp x x⟩

lemma superexp_eq (x : V) : Superexp.superexp x = iterExp x x := rfl

@[simp] lemma superexp_zero : Superexp.superexp (0 : V) = 0 := by simp [superexp_eq]

@[simp] lemma superexp_one : Superexp.superexp (1 : V) = 2 := by
  rw [superexp_eq, congrArg (iterExp 1) (zero_add 1).symm, iterExp_succ, iterExp_zero, exp_one]

@[simp] lemma superexp_two : Superexp.superexp (2 : V) = 16 := by
  have exp_two : Exp.exp (2 : V) = 4 := by
    rw [show (2 : V) = 1 + 1 from one_add_one_eq_two.symm, exp_succ, exp_one]; norm_num
  have exp_four : Exp.exp (4 : V) = 16 := by
    rw [show (4 : V) = 3 + 1 from three_add_one_eq_four.symm, exp_succ,
      show (3 : V) = 2 + 1 from two_add_one_eq_three.symm, exp_succ, exp_two]
    norm_num
  rw [superexp_eq, congrArg (iterExp 2) (one_add_one_eq_two (R := V)).symm, iterExp_succ,
    congrArg (iterExp 2) (zero_add 1).symm, iterExp_succ, iterExp_zero, exp_two, exp_four]

@[simp] lemma superexp_three : Superexp.superexp (3 : V) = Exp.exp 256 := by
  have exp_two : Exp.exp (2 : V) = 4 := by
    rw [show (2 : V) = 1 + 1 from one_add_one_eq_two.symm, exp_succ, exp_one]; norm_num
  have exp_three : Exp.exp (3 : V) = 8 := by
    rw [show (3 : V) = 2 + 1 from two_add_one_eq_three.symm, exp_succ, exp_two]; norm_num
  have exp_four : Exp.exp (4 : V) = 16 := by
    rw [show (4 : V) = 3 + 1 from three_add_one_eq_four.symm, exp_succ, exp_three]; norm_num
  have exp_eight : Exp.exp (8 : V) = 256 := by
    rw [show (8 : V) = 2 * 4 from by norm_num, exp_even, exp_four]; norm_num
  rw [superexp_eq, congrArg (iterExp 3) (two_add_one_eq_three (R := V)).symm, iterExp_succ,
    congrArg (iterExp 3) (one_add_one_eq_two (R := V)).symm, iterExp_succ,
    congrArg (iterExp 3) (zero_add 1).symm, iterExp_succ, iterExp_zero, exp_three, exp_eight]

def _root_.LO.FirstOrder.Arithmetic.superexpDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y x. !iterExpDef y x x”

instance superexp_defined : 𝚺₁-Function₁[V] Superexp.superexp via superexpDef := .mk
  fun v ↦ by simp [superexpDef, superexp_eq, iterExp_defined.iff]

instance superexp_definable : 𝚺₁-Function₁[V] Superexp.superexp := superexp_defined.to_definable

end superexp

end LO.FirstOrder.Arithmetic
