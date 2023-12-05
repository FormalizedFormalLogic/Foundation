import Logic.FirstOrder.Completeness.Completeness
import Logic.FirstOrder.Arith.Theory

namespace LO

namespace FirstOrder

namespace Arith
open Language

namespace Semantics

instance standardModel : Structure ℒₒᵣ ℕ where
  func := fun _ f =>
    match f with
    | ORing.Func.zero => fun _ => 0
    | ORing.Func.one  => fun _ => 1
    | ORing.Func.add  => fun v => v 0 + v 1
    | ORing.Func.mul  => fun v => v 0 * v 1
  rel := fun _ r =>
    match r with
    | ORing.Rel.eq => fun v => v 0 = v 1
    | ORing.Rel.lt => fun v => v 0 < v 1

instance : Structure.Eq ℒₒᵣ ℕ :=
  ⟨by intro a b; simp[standardModel, Subformula.Operator.val, Subformula.Operator.Eq.sentence_eq, Subformula.eval_rel]⟩

namespace standardModel
variable {μ : Type v} (e : Fin n → ℕ) (ε : μ → ℕ)

instance : Structure.Zero ℒₒᵣ ℕ := ⟨rfl⟩

instance : Structure.One ℒₒᵣ ℕ := ⟨rfl⟩

instance : Structure.Add ℒₒᵣ ℕ := ⟨fun _ _ => rfl⟩

instance : Structure.Mul ℒₒᵣ ℕ := ⟨fun _ _ => rfl⟩

instance : Structure.Eq ℒₒᵣ ℕ := ⟨fun _ _ => iff_of_eq rfl⟩

instance : Structure.LT ℒₒᵣ ℕ := ⟨fun _ _ => iff_of_eq rfl⟩

instance : ORing ℒₒᵣ := ORing.mk

lemma modelsTheoryPAminusAux : ℕ ⊧* Theory.PAminus ℒₒᵣ := by
  intro σ h
  rcases h <;> simp[models_def, ←le_iff_eq_or_lt]
  case addAssoc => intro l m n; exact add_assoc l m n
  case addComm  => intro m n; exact add_comm m n
  case mulAssoc => intro l m n; exact mul_assoc l m n
  case mulComm  => intro m n; exact mul_comm m n
  case addEqOfLt => intro m n h; exact ⟨n - m, Nat.add_sub_of_le (le_of_lt h)⟩
  case oneLeOfZeroLt => intro n hn; exact hn
  case mulLtMul => rintro l m n h hl; exact (mul_lt_mul_right hl).mpr h
  case distr => intro l m n; exact Nat.mul_add l m n
  case ltTrans => intro l m n; exact Nat.lt_trans
  case ltTri => intro n m; exact Nat.lt_trichotomy n m

theorem modelsTheoryPAminus : ℕ ⊧* Axiom.PAminus ℒₒᵣ := by
  simp[Axiom.PAminus, modelsTheoryPAminusAux]

lemma modelsSuccInd (σ : Subsentence ℒₒᵣ (k + 1)) : ℕ ⊧ (Arith.succInd σ) := by
  simp[succInd, models_iff, Matrix.constant_eq_singleton, Matrix.comp_vecCons', Subformula.eval_substs]
  intro e hzero hsucc x; induction' x with x ih
  · exact hzero
  · exact hsucc x ih

lemma modelsPeano : ℕ ⊧* Axiom.Peano ℒₒᵣ :=
  by simp[Axiom.Peano, Axiom.Ind, Theory.IndScheme, modelsSuccInd, modelsTheoryPAminus]

end standardModel

theorem Peano.Consistent : System.Consistent (Axiom.Peano ℒₒᵣ) :=
  Sound.consistent_of_model standardModel.modelsPeano

variable (L : Language.{u}) [ORing L]

structure Cut (M : Type w) [s : Structure L M] where
  domain : Set M
  closedSucc : ∀ x ∈ domain, (ᵀ“#0 + 1”).bVal s ![x] ∈ domain
  closedLt : ∀ x y : M, Subformula.PVal s ![x, y] “#0 < #1” → y ∈ domain → x ∈ domain

structure ClosedCut (M : Type w) [s : Structure L M] extends Structure.ClosedSubset L M where
  closedLt : ∀ x y : M, Subformula.PVal s ![x, y] “#0 < #1” → y ∈ domain → x ∈ domain

end Semantics

end Arith

end FirstOrder

end LO
