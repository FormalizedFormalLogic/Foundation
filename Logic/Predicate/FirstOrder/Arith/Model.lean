import Logic.Predicate.FirstOrder.Completeness.Completeness
import Logic.Predicate.FirstOrder.Arith.Theory

namespace LO

namespace FirstOrder

namespace Arith
open Language

namespace Semantics

instance standardModel : Structure oRing ℕ where
  func := fun _ f =>
    match f with
    | ORingFunc.zero => fun _ => 0
    | ORingFunc.one  => fun _ => 1
    | ORingFunc.add  => fun v => v 0 + v 1
    | ORingFunc.mul  => fun v => v 0 * v 1
  rel := fun _ r =>
    match r with
    | ORingRel.eq => fun v => v 0 = v 1
    | ORingRel.lt => fun v => v 0 < v 1

instance : Structure.Eq oRing ℕ := ⟨by simp[standardModel]⟩

namespace standardModel
variable {μ : Type v} (e : Fin n → ℕ) (ε : μ → ℕ)

@[simp] lemma zero_eq_zero :
    standardModel.func Language.Zero.zero = 0 :=
  rfl

@[simp] lemma one_eq_one :
    standardModel.func Language.One.one = 1 :=
  rfl

@[simp] lemma add_eq_add : standardModel.func lang(+) ![x, y] = x + y := rfl

@[simp] lemma mul_eq_mul : standardModel.func lang(*) ![x, y] = x * y := rfl

@[simp] lemma numeral_eq_numeral (n : ℕ) :
    Subterm.val standardModel e ε (Subterm.natLit oRing n) = n := by 
  induction' n with n ih
  { simp[Subterm.natLit_zero] }
  { cases' n with n <;> simp[Subterm.natLit_one, ←Nat.one_eq_succ_zero, Subterm.natLit_succ, Nat.succ_eq_add_one] at ih ⊢
    simp[ih] }

@[simp] lemma lt_eq_lt : standardModel.rel lang(<) ![x, y] ↔ x < y := of_eq rfl

@[simp] lemma le_eq_le (t u : Subterm oRing μ n) :
    Subformula.Eval standardModel e ε “ᵀ!t ≤ ᵀ!u”  ↔ t.val standardModel e ε ≤ u.val standardModel e ε :=
  by simp[Subformula.le_eq, le_iff_eq_or_lt]

theorem modelsTheoryPAminus : ℕ ⊧* Theory.PAminus oRing := by
  intro σ h
  rcases h <;> simp[models_def]
  case addAssoc => intro l m n; exact add_assoc n m l
  case addComm  => intro m n; exact add_comm n m
  case mulAssoc => intro l m n; exact mul_assoc n m l
  case mulComm  => intro m n; exact mul_comm n m
  case addEqOfLt => intro m n h; exact ⟨m - n, Nat.add_sub_of_le (le_of_lt h)⟩
  case oneLeOfZeroLt => intro n hn; exact hn
  case mulLtMul => rintro l m n h hl; exact (mul_lt_mul_right hl).mpr h
  case distr => intro l m n; exact Nat.mul_add n m l
  case ltTrans => intro l m n; exact Nat.lt_trans
  case ltTri => intro n m; simp[or_assoc]; exact Nat.lt_trichotomy m n

theorem modelsTheoryRobinson : ℕ ⊧* Theory.Robinson oRing := by
  intro σ h
  rcases h <;> simp[models_def]
  case q₃ => intro x; cases x <;> simp
  case q₅ => simp[add_assoc]
  case q₇ => simp[mul_add]
  case q₈ =>
    intro x y
    simp[Subformula.le_eq, Nat.lt_iff_add_one_le, le_iff_exists_add];
    exact ⟨by rintro ⟨z, rfl⟩; exact ⟨z, by simp[add_comm]⟩, by rintro ⟨z, rfl⟩; exact ⟨z, by simp[add_comm]⟩⟩

@[simp] theorem modelsRobinson : ℕ ⊧* Axiom.Robinson oRing := by
  simp[Axiom.Robinson, modelsTheoryRobinson]

lemma modelsSuccInd (σ : Subsentence oRing (k + 1)) : ℕ ⊧ (Arith.succInd σ) := by
  simp[succInd, models_iff, Matrix.constant_eq_singleton, Matrix.comp_vecCons', Subformula.eval_substs]
  intro e hzero hsucc x; induction' x with x ih
  · exact hzero
  · exact hsucc x ih

lemma modelsPeano : ℕ ⊧* Axiom.Peano oRing :=
  by simp[Axiom.Peano, Axiom.Ind, Theory.IndScheme, modelsSuccInd]

end standardModel

theorem Peano.Consistent : Logic.System.Consistent (Axiom.Peano oRing) :=
  Logic.Sound.consistent_of_model standardModel.modelsPeano

variable (L : Language.{u}) [L.ORing]

structure Cut (M : Type w) [s : Structure L M] where
  domain : Set M
  closedSucc : ∀ x ∈ domain, (ᵀ“#0 + 1”).bVal s ![x] ∈ domain
  closedLt : ∀ x y : M, Subformula.BVal s ![x, y] “#0 < #1” → y ∈ domain → x ∈ domain

structure ClosedCut (M : Type w) [s : Structure L M] extends Structure.ClosedSubset L M where
  closedLt : ∀ x y : M, Subformula.BVal s ![x, y] “#0 < #1” → y ∈ domain → x ∈ domain

end Semantics

end Arith

end FirstOrder