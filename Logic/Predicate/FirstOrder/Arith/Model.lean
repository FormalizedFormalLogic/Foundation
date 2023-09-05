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
    SubTerm.val standardModel e ε (SubTerm.natLit oRing n) = n := by 
  induction' n with n ih
  { simp[SubTerm.natLit_zero] }
  { cases' n with n <;> simp[SubTerm.natLit_one, ←Nat.one_eq_succ_zero, SubTerm.natLit_succ, Nat.succ_eq_add_one] at ih ⊢
    simp[ih] }

@[simp] lemma lt_eq_lt : standardModel.rel lang(<) ![x, y] ↔ x < y := of_eq rfl

@[simp] lemma le_eq_le (t u : SubTerm oRing μ n) :
    SubFormula.Eval standardModel e ε “ᵀ!t ≤ ᵀ!u”  ↔ t.val standardModel e ε ≤ u.val standardModel e ε :=
  by simp[SubFormula.le_eq, le_iff_eq_or_lt]

theorem modelsTheoryRobinson : ℕ ⊧* Theory.Robinson oRing := by
  intro σ h
  rcases h <;> simp[realize_def]
  case q₃ => intro x; cases x <;> simp
  case q₅ => simp[add_assoc]
  case q₇ => simp[mul_add]
  case q₈ =>
    intro x y
    simp[SubFormula.le_eq, Nat.lt_iff_add_one_le, le_iff_exists_add];
    exact ⟨by rintro ⟨z, rfl⟩; exact ⟨z, by simp[add_comm]⟩, by rintro ⟨z, rfl⟩; exact ⟨z, by simp[add_comm]⟩⟩

@[simp] theorem modelsRobinson : ℕ ⊧* Axiom.Robinson oRing := by
  simp[Axiom.Robinson, modelsTheoryRobinson]

lemma modelsSuccInd (σ : SubSentence oRing (k + 1)) : ℕ ⊧ (Arith.succInd σ) := by
  simp[succInd, models_iff, Matrix.constant_eq_singleton, Matrix.comp_vecCons', SubFormula.eval_substs]
  intro e hzero hsucc x; induction' x with x ih
  · exact hzero
  · exact hsucc x ih

lemma modelsPeano : ℕ ⊧* Axiom.Peano oRing :=
  by simp[Axiom.Peano, Axiom.Ind, Theory.IndScheme, modelsSuccInd]

end standardModel

theorem Peano.IsConsistent : Logic.System.Consistent (Axiom.Peano oRing) :=
  Logic.Sound.consistent_of_model standardModel.modelsPeano

variable (L : Language.{u}) [L.ORing]

structure Cut (M : Type w) [s : Structure L M] where
  domain : Set M
  closedSucc : ∀ x ∈ domain, (ᵀ“#0 + 1”).bVal s ![x] ∈ domain
  closedLt : ∀ x y : M, SubFormula.BVal s ![x, y] “#0 < #1” → y ∈ domain → x ∈ domain

structure ClosedCut (M : Type w) [s : Structure L M] extends Structure.ClosedSubset L M where
  closedLt : ∀ x y : M, SubFormula.BVal s ![x, y] “#0 < #1” → y ∈ domain → x ∈ domain

end Semantics

end Arith

end FirstOrder