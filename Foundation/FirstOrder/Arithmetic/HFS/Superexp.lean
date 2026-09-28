module

public import Foundation.FirstOrder.Arithmetic.HFS.PRF

/-!

# Superexponential Function in $\mathsf{I} \Sigma_1$

-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open scoped FFL.FirstOrder.Bounding

open scoped FFL.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

section iterExp

def iterExp.blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y x. y = x”
  succ := .mkSigma “y ih n x. !(expDef.ofZero 𝚺ᴬ₁) y ih”

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

def _root_.FFL.FirstOrder.Arithmetic.iterExpDef : 𝚺ᴬ₁.Semisentence 3 :=
  iterExp.blueprint.resultDef |>.rew (Rew.subst ![#0, #2, #1])

instance iterExp_defined : 𝚺ᴬ₁-Function₂[V] iterExp via iterExpDef := .mk
  fun v ↦ by simp [iterExp.construction.result_defined_iff, iterExpDef]; rfl

instance iterExp_definable : 𝚺ᴬ₁-Function₂[V] iterExp := iterExp_defined.to_definable

instance iterExp_definable' (Γ) {m : ℕ} : Γᴬ-[m + 1]-Function₂ (iterExp : V → V → V) :=
  iterExp_definable.of_sigmaOne

lemma le_iterExp (x n : V) : x ≤ iterExp x n := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ n ih => simpa using le_exp_of_le ih

lemma iterExp_add (x m n : V) : iterExp x (m + n) = iterExp (iterExp x m) n := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ n ih => rw [← add_assoc, iterExp_succ, ih, iterExp_succ]

@[gcongr] lemma iterExp_le_iterExp {x y m n : V} (hxy : x ≤ y) (hmn : m ≤ n) :
    iterExp x m ≤ iterExp y n := by
  have (m : V) : iterExp x m ≤ iterExp y m := by
    induction m using ISigma1.sigma1_succ_induction
    · definability
    case zero => simpa using hxy
    case succ m ih => simpa using ih
  obtain ⟨k, rfl⟩ := le_iff_exists_add.mp hmn
  exact (this m).trans (by simpa [iterExp_add] using le_iterExp (iterExp y m) k)

lemma iterExp_natCast (x : V) (k : ℕ) : iterExp x k = Exp.exp^[k] x := by
  induction k with
  | zero => simp
  | succ k ih => simp [Function.iterate_succ_apply', ih]

@[simp] lemma iterExp_ofNat (x : V) (k : ℕ) [k.AtLeastTwo] :
    iterExp x (no_index (OfNat.ofNat k : V)) = Exp.exp^[k] x :=
  iterExp_natCast x k

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
    rw [show (8 : V) = 2 * 4 from by norm_num, exp_even, exp_four]; norm_num [sq]
  rw [superexp_eq, congrArg (iterExp 3) (two_add_one_eq_three (R := V)).symm, iterExp_succ,
    congrArg (iterExp 3) (one_add_one_eq_two (R := V)).symm, iterExp_succ,
    congrArg (iterExp 3) (zero_add 1).symm, iterExp_succ, iterExp_zero, exp_three, exp_eight]

def _root_.FFL.FirstOrder.Arithmetic.superexpDef : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
  “y x. !iterExpDef y x x”

instance superexp_defined : 𝚺ᴬ₁-Function₁[V] Superexp.superexp via superexpDef := .mk
  fun v ↦ by simp [superexpDef, superexp_eq, iterExp_defined.iff]

instance superexp_definable : 𝚺ᴬ₁-Function₁[V] Superexp.superexp := superexp_defined.to_definable

end superexp

end FFL.FirstOrder.Arithmetic
