import Logic.Predicate.FirstOrder.Semantics
import Logic.Predicate.FirstOrder.Arith.Theory

namespace FirstOrder

namespace Arith
open Language

namespace Semantics

instance StandardModel : Structure oring ℕ where
  func := fun f =>
    match f with
    | ORingFunc.zero => fun _ => 0
    | ORingFunc.one  => fun _ => 1
    | ORingFunc.add  => fun v => v 0 + v 1
    | ORingFunc.mul  => fun v => v 0 * v 1
  rel := fun r =>
    match r with
    | ORingRel.eq => fun v => v 0 = v 1
    | ORingRel.lt => fun v => v 0 < v 1

instance : Structure.Eq oring ℕ := ⟨by simp[StandardModel]⟩

namespace StandardModel
variable {μ : Type v} (e : Fin n → ℕ) (ε : μ → ℕ)

@[simp] lemma zero_eq_zero :
    StandardModel.func Language.Zero.zero = 0 :=
  rfl

@[simp] lemma one_eq_one :
    StandardModel.func Language.One.one = 1 :=
  rfl

@[simp] lemma add_eq_add : StandardModel.func lang(+) ![x, y] = x + y := rfl

@[simp] lemma mul_eq_mul : StandardModel.func lang(*) ![x, y] = x * y := rfl

@[simp] lemma numeral_eq_numeral (n : ℕ) :
    SubTerm.val StandardModel e ε (SubTerm.natLit oring n) = n := by 
  induction' n with n ih <;> simp[SubTerm.natLit_zero]
  cases' n with n <;> simp[SubTerm.natLit_one, ←Nat.one_eq_succ_zero, SubTerm.natLit_succ, Nat.succ_eq_add_one] at ih ⊢
  simp[ih]

@[simp] lemma lt_eq_lt : StandardModel.rel lang(<) ![x, y] ↔ x < y := of_eq rfl

theorem ModelsRobinson : ℕ ⊧₁* Robinson oring := by
  intro σ h
  rcases h <;> simp[realize_def]
  case q₃ => intro x; cases x <;> simp
  case q₅ => simp[add_assoc]
  case q₇ => simp[mul_add]
  case q₈ =>
    intro x y
    simp[Nat.lt_iff_add_one_le, le_iff_exists_add]
    exact ⟨by rintro ⟨x, rfl⟩; exact ⟨x, by rw[add_comm (y + 1), add_assoc]⟩,
      by rintro ⟨x, rfl⟩; exact ⟨x, by rw[add_comm (y + 1), add_assoc]⟩⟩

end StandardModel

theorem Robinson.IsConsistent : Logic.Proof.IsConsistent (Robinson oring) :=
  Logic.Sound.consistent_of_model StandardModel.ModelsRobinson

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