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

def _root_.LO.FirstOrder.Arithmetic.superexpDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y x. !iterExpDef y x x”

instance superexp_defined : 𝚺₁-Function₁[V] Superexp.superexp via superexpDef := .mk
  fun v ↦ by simp [superexpDef, superexp_eq, iterExp_defined.iff]

instance superexp_definable : 𝚺₁-Function₁[V] Superexp.superexp := superexp_defined.to_definable

end superexp

end LO.FirstOrder.Arithmetic
