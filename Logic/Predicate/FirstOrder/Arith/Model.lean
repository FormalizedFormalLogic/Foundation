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
    | ORing.Func.zero => fun _ => 0
    | ORing.Func.one  => fun _ => 1
    | ORing.Func.add  => fun v => v 0 + v 1
    | ORing.Func.mul  => fun v => v 0 * v 1
  rel := fun _ r =>
    match r with
    | ORing.Rel.eq => fun v => v 0 = v 1
    | ORing.Rel.lt => fun v => v 0 < v 1

instance : Structure.Eq oRing ℕ :=
  ⟨by intro a b; simp[standardModel, Subformula.Operator.val, Subformula.Operator.Eq.sentence_eq, Subformula.eval_rel]⟩

namespace standardModel
variable {μ : Type v} (e : Fin n → ℕ) (ε : μ → ℕ)

instance : Structure.Zero oRing ℕ := ⟨rfl⟩

instance : Structure.One oRing ℕ := ⟨rfl⟩

instance : Structure.Add oRing ℕ := ⟨fun _ _ => rfl⟩

instance : Structure.Mul oRing ℕ := ⟨fun _ _ => rfl⟩

instance : Structure.Eq oRing ℕ := ⟨fun _ _ => iff_of_eq rfl⟩

instance : Structure.LT oRing ℕ := ⟨fun _ _ => iff_of_eq rfl⟩

instance : ORing oRing := ORing.mk

lemma modelsTheoryPAminusAux : ℕ ⊧* Theory.PAminus oRing := by
  intro σ h
  rcases h <;> simp[models_def, ←le_iff_eq_or_lt]
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

theorem modelsTheoryPAminus : ℕ ⊧* Axiom.PAminus oRing := by
  simp[Axiom.PAminus, modelsTheoryPAminusAux]

lemma modelsSuccInd (σ : Subsentence oRing (k + 1)) : ℕ ⊧ (Arith.succInd σ) := by
  simp[succInd, models_iff, Matrix.constant_eq_singleton, Matrix.comp_vecCons', Subformula.eval_substs]
  intro e hzero hsucc x; induction' x with x ih
  · exact hzero
  · exact hsucc x ih

lemma modelsPeano : ℕ ⊧* Axiom.Peano oRing :=
  by simp[Axiom.Peano, Axiom.Ind, Theory.IndScheme, modelsSuccInd, modelsTheoryPAminus]

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

class MPAminus (M : Type*) [Zero M] [One M] [Add M] [Mul M] [LT M] where
  add_zero          : ∀ x : M, x + 0 = x
  add_assoc         : ∀ x y z : M, (x + y) + z = x + (y + z)
  add_comm          : ∀ x y : M, x + y = y + x
  add_eq_of_lt      : ∀ x y : M, x < y → ∃ z, x + z = y
  zero_le           : ∀ x, 0 = x ∨ 0 < x
  zero_lt_one       : 0 < 1
  one_le_of_zero_lt : ∀ x : M, 0 < x → 1 = x ∨ 1 < x
  add_lt_add        : ∀ x y z : M, x < y → x + z < y + z
  mul_zero          : ∀ x : M, x * 0 = 0
  mul_one           : ∀ x : M, x * 1 = x
  mul_assoc         : ∀ x y z : M, (x * y) * z = x * (y * z)
  mul_comm          : ∀ x y : M, x * y = y * x
  mul_lt_mul        : ∀ x y z : M, x < y → 0 < z → x * z < y * z
  distr             : ∀ x y z : M, x * (y + z) = x * y + x * z
  lt_irrefl         : ∀ x : M, ¬x < x
  lt_trans          : ∀ x y z : M, x < y → y < z → x < z
  lt_tri            : ∀ x y : M, x < y ∨ x = y ∨ y < x

variable {M : Type*} [Zero M] [One M] [Add M] [Mul M] [LT M] [MPAminus M]


instance : AddCommMonoid M where
  add_assoc := MPAminus.add_assoc
  zero_add := fun x => MPAminus.add_comm x 0 ▸ MPAminus.add_zero x
  add_zero := MPAminus.add_zero
  add_comm := MPAminus.add_comm

instance  : LinearOrder M where
  le := fun x y => x = y ∨ x < y
  le_refl := fun x => Or.inl (by simp)
  le_trans := by
    rintro x y z (rfl | hx) (rfl | hy) <;> simp[*]
    · exact Or.inr (MPAminus.lt_trans _ _ _ hx hy)
  le_antisymm := by
    rintro x y (rfl | hx) <;> simp
    rintro (rfl | hy) <;> try simp
    exact False.elim $ MPAminus.lt_irrefl _ (MPAminus.lt_trans _ _ _ hx hy)
  le_total := by
    intro x y
    rcases MPAminus.lt_tri x y with (h | rfl | h) <;> simp[*]
  lt_iff_le_not_le := by { sorry }
  decidableLE := by { sorry }

end Arith

end FirstOrder

end LO
