import Foundation.FirstOrder.Order.Le

namespace LO

class ORingStructure (α : Type*) extends Zero α, One α, Add α, Mul α, LT α

instance [Zero α] [One α] [Add α] [Mul α] [LT α] : ORingStructure α where

namespace ORingStructure

variable {α : Type*} [ORingStructure α]

def numeral : ℕ → α
  |     0 => 0
  |     1 => 1
  | n + 2 => numeral (n + 1) + 1

 @[simp] lemma zero_eq_zero : (numeral 0 : α) = 0 := rfl

 @[simp] lemma one_eq_one : (numeral 1 : α) = 1 := rfl

end ORingStructure

@[simp] lemma Nat.numeral_eq : (n : ℕ) → ORingStructure.numeral n = n
  |     0 => rfl
  |     1 => rfl
  | n + 2 => by simp [ORingStructure.numeral, Nat.numeral_eq (n + 1)]

namespace FirstOrder

section ToString

variable {L : Language} [L.ORing]

variable [ToString ξ]

def Semiterm.toStringORing : Semiterm ℒₒᵣ ξ n → String
  |                        #x => "x_{" ++ toString (n - 1 - (x : ℕ)) ++ "}"
  |                        &x => "a_{" ++ toString x ++ "}"
  | func Language.Zero.zero _ => "0"
  |   func Language.One.one _ => "1"
  |   func Language.Add.add v => "(" ++ toStringORing (v 0) ++ " + " ++ toStringORing (v 1) ++ ")"
  |   func Language.Mul.mul v => "(" ++ toStringORing (v 0) ++ " \\cdot " ++ toStringORing (v 1) ++ ")"

instance : Repr (Semiterm ℒₒᵣ ξ n) := ⟨fun t _ ↦ t.toStringORing⟩

instance : ToString (Semiterm ℒₒᵣ ξ n) := ⟨Semiterm.toStringORing⟩

def Semiformula.toStringORing : ∀ {n}, Semiformula ℒₒᵣ ξ n → String
  | _,                             ⊤ => "\\top"
  | _,                             ⊥ => "\\bot"
  | _,          rel Language.Eq.eq v => (v 0).toStringORing ++ " = " ++ (v 1).toStringORing
  | _,          rel Language.LT.lt v => (v 0).toStringORing ++ " < " ++ (v 1).toStringORing
  | _,         nrel Language.Eq.eq v => (v 0).toStringORing ++ " \\not = " ++ (v 1).toStringORing
  | _,         nrel Language.LT.lt v => (v 0).toStringORing ++ " \\not < " ++ (v 1).toStringORing
  | _,                         φ ⋏ ψ => "[" ++ φ.toStringORing ++ "]" ++ " \\land " ++ "[" ++ ψ.toStringORing ++ "]"
  | _,                         φ ⋎ ψ => "[" ++ φ.toStringORing ++ "]" ++ " \\lor "  ++ "[" ++ ψ.toStringORing ++ "]"
  | n, ∀' (rel Language.LT.lt v ➝ φ) => "(\\forall x_{" ++ toString n ++ "} < " ++ (v 1).toStringORing ++ ") " ++ "[" ++ φ.toStringORing ++ "]"
  | n, ∃' (rel Language.LT.lt v ⋏ φ) => "(\\exists x_{" ++ toString n ++ "} < " ++ (v 1).toStringORing ++ ") " ++ "[" ++ φ.toStringORing ++ "]"
  | n,                          ∀' φ => "(\\forall x_{" ++ toString n ++ "}) " ++ "[" ++ φ.toStringORing ++ "]"
  | n,                          ∃' φ => "(\\exists x_{" ++ toString n ++ "}) " ++ "[" ++ φ.toStringORing ++ "]"

instance : Repr (Semiformula ℒₒᵣ ξ n) := ⟨fun φ _ ↦ φ.toStringORing⟩

instance : ToString (Semiformula ℒₒᵣ ξ n) := ⟨Semiformula.toStringORing⟩

end ToString

namespace Arithmetic

open Encodable Semiterm.Operator.GoedelNumber

variable {α} [Encodable α]

instance : Semiterm.Operator.GoedelNumber ℒₒᵣ α :=
  Semiterm.Operator.GoedelNumber.ofEncodable

lemma goedelNumber_def (a : α) :
  goedelNumber a = Semiterm.Operator.encode ℒₒᵣ a := rfl

lemma goedelNumber'_def (a : α) :
  (⌜a⌝ : Semiterm ℒₒᵣ ξ n) = Semiterm.Operator.encode ℒₒᵣ a := rfl

lemma goedelNumber'_eq_coe_encode (a : α) :
  (⌜a⌝ : Semiterm ℒₒᵣ ξ n) = ↑(Encodable.encode a) := rfl

@[simp] lemma encode_encode_eq (a : α) :
    (goedelNumber (encode a) : Semiterm.Const ℒₒᵣ) = goedelNumber a := by simp [Semiterm.Operator.encode, goedelNumber_def]

@[simp] lemma rew_goedelNumber' (ω : Rew ℒₒᵣ ξ₁ n₁ ξ₂ n₂) (a : α) :
    ω ⌜a⌝ = ⌜a⌝ := by
  simp [goedelNumber'_def]

end Arithmetic

/-! ### Semantics of arithmetic  -/

class Structure.ORing (L : Language) [L.ORing] (M : Type w) [ORingStructure M] [Structure L M] extends
  Structure.Zero L M, Structure.One L M, Structure.Add L M, Structure.Mul L M, Structure.Eq L M, Structure.LT L M

attribute [instance] Structure.ORing.mk

namespace Structure

open Semiterm Semiformula

variable [Operator.Zero L] [Operator.One L] [Operator.Add L] {M : Type u} [ORingStructure M]
  [Structure L M] [Structure.Zero L M] [Structure.One L M] [Structure.Add L M]

@[simp] lemma numeral_eq_numeral : (z : ℕ) → (Semiterm.Operator.numeral L z).val ![] = (ORingStructure.numeral z : M)
  | 0     => by simp [ORingStructure.numeral, Semiterm.Operator.numeral_zero]
  | 1     => by simp [ORingStructure.numeral, Semiterm.Operator.numeral_one]
  | z + 2 => by simp [ORingStructure.numeral, Semiterm.Operator.numeral_add_two,
                  Semiterm.Operator.val_comp, Matrix.fun_eq_vec_two, numeral_eq_numeral (z + 1)]

end Structure

namespace Semiformula

variable {L : Language} [L.LT] [L.Zero] [L.One] [L.Add]

def ballLTSucc (t : Semiterm L ξ n) (φ : Semiformula L ξ (n + 1)) : Semiformula L ξ n := φ.ballLT ‘!!t + 1’

def bexLTSucc (t : Semiterm L ξ n) (φ : Semiformula L ξ (n + 1)) : Semiformula L ξ n := φ.bexLT ‘!!t + 1’

variable {M : Type*} {s : Structure L M} [LT M] [One M] [Add M] [Structure.LT L M] [Structure.One L M] [Structure.Add L M]

variable {t : Semiterm L ξ n} {φ : Semiformula L ξ (n + 1)}

lemma eval_ballLTSucc {e ε} :
    Eval s e ε (φ.ballLTSucc t) ↔ ∀ x < t.val s e ε + 1, Eval s (x :> e) ε φ := by
  simp [ballLTSucc, Semiterm.Operator.numeral]

lemma eval_bexLTSucc {e ε} :
    Eval s e ε (φ.bexLTSucc t) ↔ ∃ x < t.val s e ε + 1, Eval s (x :> e) ε φ := by
  simp [bexLTSucc, Semiterm.Operator.numeral]

end Semiformula

namespace BinderNotation

open Lean PrettyPrinter Delaborator SubExpr

syntax:max "∀ " ident " <⁺ " first_order_term ", " first_order_formula:0 : first_order_formula

syntax:max "∃ " ident " <⁺ " first_order_term ", " first_order_formula:0 : first_order_formula

macro_rules
  | `(⤫formula(lit)[ $binders* | $fbinders* | ∀ $x <⁺ $t, $φ]) => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
    let binders' := binders.insertIdx 0 x
    `(Semiformula.ballLTSucc ⤫term(lit)[ $binders* | $fbinders* | $t ] ⤫formula(lit)[ $binders'* | $fbinders* | $φ ])
  | `(⤫formula(lit)[ $binders* | $fbinders* | ∃ $x <⁺ $t, $φ]) => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
    let binders' := binders.insertIdx 0 x
    `(Semiformula.bexLTSucc ⤫term(lit)[ $binders* | $fbinders* | $t ] ⤫formula(lit)[ $binders'* | $fbinders* | $φ ])

end BinderNotation

abbrev ArithmeticTheory := Theory ℒₒᵣ

end FirstOrder

end LO
