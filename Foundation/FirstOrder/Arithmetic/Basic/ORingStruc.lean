import Foundation.FirstOrder.Order.Le

namespace LO

class ORingStruc (α : Type*) extends Zero α, One α, Add α, Mul α, LT α

instance [Zero α] [One α] [Add α] [Mul α] [LT α] : ORingStruc α where

namespace ORingStruc

variable {α : Type*} [ORingStruc α]

def numeral : ℕ → α
  |     0 => 0
  |     1 => 1
  | n + 2 => numeral (n + 1) + 1

 @[simp] lemma zero_eq_zero : (numeral 0 : α) = 0 := rfl

 @[simp] lemma one_eq_one : (numeral 1 : α) = 1 := rfl

end ORingStruc

@[simp] lemma Nat.numeral_eq : (n : ℕ) → ORingStruc.numeral n = n
  |     0 => rfl
  |     1 => rfl
  | n + 2 => by simp [ORingStruc.numeral, Nat.numeral_eq (n + 1)]

namespace FirstOrder

namespace Language

variable {L : Language} [L.ORing]

def oringEmb : ℒₒᵣ →ᵥ L where
  func := fun {k} f ↦
    match k, f with
    | _, Zero.zero => Zero.zero
    | _,   One.one => One.one
    | _,   Add.add => Add.add
    | _,   Mul.mul => Mul.mul
  rel := fun {k} r ↦
    match k, r with
    | _, Eq.eq => Eq.eq
    | _, LT.lt => LT.lt

@[simp] lemma oringEmb_zero : (oringEmb : ℒₒᵣ →ᵥ L).func Zero.zero = Zero.zero := rfl

@[simp] lemma oringEmb_one : (oringEmb : ℒₒᵣ →ᵥ L).func One.one = One.one := rfl

@[simp] lemma oringEmb_add : (oringEmb : ℒₒᵣ →ᵥ L).func Add.add = Add.add := rfl

@[simp] lemma oringEmb_mul : (oringEmb : ℒₒᵣ →ᵥ L).func Mul.mul = Mul.mul := rfl

@[simp] lemma oringEmb_eq : (oringEmb : ℒₒᵣ →ᵥ L).rel Eq.eq = Eq.eq := rfl

@[simp] lemma oringEmb_lt : (oringEmb : ℒₒᵣ →ᵥ L).rel LT.lt = LT.lt := rfl

end Language

section

variable {L : Language} [L.ORing]

namespace Semiterm

instance : Coe (Semiterm ℒₒᵣ ξ n) (Semiterm L ξ n) := ⟨lMap Language.oringEmb⟩

@[simp] lemma oringEmb_zero :
    Semiterm.lMap (Language.oringEmb : ℒₒᵣ →ᵥ L) (Operator.Zero.zero.const : Semiterm ℒₒᵣ ξ n) = Operator.Zero.zero.const := by
  simp [Operator.const, lMap_func, Operator.operator, Operator.Zero.term_eq, Matrix.empty_eq]

@[simp] lemma oringEmb_one :
    Semiterm.lMap (Language.oringEmb : ℒₒᵣ →ᵥ L) (Operator.One.one.const : Semiterm ℒₒᵣ ξ n) = Operator.One.one.const := by
  simp [Operator.const, lMap_func, Operator.operator, Operator.One.term_eq, Matrix.empty_eq]

@[simp] lemma oringEmb_add (v : Fin 2 → Semiterm ℒₒᵣ ξ n) :
    Semiterm.lMap (Language.oringEmb : ℒₒᵣ →ᵥ L) (Operator.Add.add.operator v) = Operator.Add.add.operator ![(v 0 : Semiterm L ξ n), (v 1 : Semiterm L ξ n)] := by
  simpa [lMap_func, Rew.func, Operator.operator, Operator.Add.term_eq, Matrix.empty_eq] using Matrix.fun_eq_vec_two

@[simp] lemma oringEmb_mul (v : Fin 2 → Semiterm ℒₒᵣ ξ n) :
    Semiterm.lMap (Language.oringEmb : ℒₒᵣ →ᵥ L) (Operator.Mul.mul.operator v) = Operator.Mul.mul.operator ![(v 0 : Semiterm L ξ n), (v 1 : Semiterm L ξ n)] := by
  simpa [lMap_func, Rew.func, Operator.operator, Operator.Mul.term_eq, Matrix.empty_eq] using Matrix.fun_eq_vec_two

@[simp] lemma oringEmb_numeral (z : ℕ) :
    lMap (Language.oringEmb : ℒₒᵣ →ᵥ L) ((Operator.numeral ℒₒᵣ z).const : Semiterm ℒₒᵣ ξ n) = (Operator.numeral L z).const :=
  match z with
  |     0 => oringEmb_zero
  |     1 => oringEmb_one
  | z + 2 => by simp [Operator.numeral_add_two, Matrix.fun_eq_vec_two, oringEmb_numeral (z + 1)]

section ToString

variable [ToString ξ]

def toStringORing : Semiterm ℒₒᵣ ξ n → String
  |                        #x => "x_{" ++ toString (n - 1 - (x : ℕ)) ++ "}"
  |                        &x => "a_{" ++ toString x ++ "}"
  | func Language.Zero.zero _ => "0"
  |   func Language.One.one _ => "1"
  |   func Language.Add.add v => "(" ++ toStringORing (v 0) ++ " + " ++ toStringORing (v 1) ++ ")"
  |   func Language.Mul.mul v => "(" ++ toStringORing (v 0) ++ " \\cdot " ++ toStringORing (v 1) ++ ")"

instance : Repr (Semiterm ℒₒᵣ ξ n) := ⟨fun t _ ↦ t.toStringORing⟩

instance : ToString (Semiterm ℒₒᵣ ξ n) := ⟨toStringORing⟩

end ToString

end Semiterm

namespace Semiformula

@[simp] lemma oringEmb_eq (v : Fin 2 → Semiterm ℒₒᵣ ξ n) :
    Semiformula.lMap (Language.oringEmb : ℒₒᵣ →ᵥ L) (op(=).operator v) = op(=).operator ![(v 0 : Semiterm L ξ n), (v 1 : Semiterm L ξ n)] := by
  simpa [lMap_rel, rew_rel, Operator.operator, Operator.Eq.sentence_eq] using Matrix.fun_eq_vec_two

@[simp] lemma oringEmb_lt (v : Fin 2 → Semiterm ℒₒᵣ ξ n) :
    Semiformula.lMap (Language.oringEmb : ℒₒᵣ →ᵥ L) (op(<).operator v) = op(<).operator ![(v 0 : Semiterm L ξ n), (v 1 : Semiterm L ξ n)] := by
  simpa [lMap_rel, rew_rel, Operator.operator, Operator.LT.sentence_eq] using Matrix.fun_eq_vec_two

section ToString

variable [ToString ξ]

def toStringORing : ∀ {n}, Semiformula ℒₒᵣ ξ n → String
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

instance : ToString (Semiformula ℒₒᵣ ξ n) := ⟨toStringORing⟩

end ToString

end Semiformula

end

open Semiterm Semiformula

abbrev Polynomial (n : ℕ) : Type := ClosedSemiterm ℒₒᵣ n

class Structure.ORing (L : Language) [L.ORing] (M : Type w) [ORingStruc M] [Structure L M] extends
  Structure.Zero L M, Structure.One L M, Structure.Add L M, Structure.Mul L M, Structure.Eq L M, Structure.LT L M

attribute [instance] Structure.ORing.mk

namespace Structure

variable [Operator.Zero L] [Operator.One L] [Operator.Add L] {M : Type u} [ORingStruc M]
  [Structure L M] [Structure.Zero L M] [Structure.One L M] [Structure.Add L M]

@[simp] lemma numeral_eq_numeral : (z : ℕ) → (Semiterm.Operator.numeral L z).val ![] = (ORingStruc.numeral z : M)
  | 0     => by simp [ORingStruc.numeral, Semiterm.Operator.numeral_zero]
  | 1     => by simp [ORingStruc.numeral, Semiterm.Operator.numeral_one]
  | z + 2 => by simp [ORingStruc.numeral, Semiterm.Operator.numeral_add_two,
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
  simp [ballLTSucc, Operator.numeral]

lemma eval_bexLTSucc {e ε} :
    Eval s e ε (φ.bexLTSucc t) ↔ ∃ x < t.val s e ε + 1, Eval s (x :> e) ε φ := by
  simp [bexLTSucc, Operator.numeral]

end Semiformula

namespace BinderNotation

open Lean PrettyPrinter Delaborator SubExpr

syntax:max "∀ " ident " <⁺ " first_order_term ", " first_order_formula:0 : first_order_formula

syntax:max "∃ " ident " <⁺ " first_order_term ", " first_order_formula:0 : first_order_formula

macro_rules
  | `(⤫formula[ $binders* | $fbinders* | ∀ $x <⁺ $t, $φ]) => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
    let binders' := binders.insertIdx 0 x
    `(Semiformula.ballLTSucc ⤫term[ $binders* | $fbinders* | $t ] ⤫formula[ $binders'* | $fbinders* | $φ ])
  | `(⤫formula[ $binders* | $fbinders* | ∃ $x <⁺ $t, $φ]) => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
    let binders' := binders.insertIdx 0 x
    `(Semiformula.bexLTSucc ⤫term[ $binders* | $fbinders* | $t ] ⤫formula[ $binders'* | $fbinders* | $φ ])

end BinderNotation

namespace Arithmetic

section

variable {L : Language.{u}} [L.ORing] (T : Theory L)

lemma consequence_of [𝗘𝗤 ⪯ T] (φ : Sentence L)
  (H : ∀ (M : Type (max u w))
         [ORingStruc M]
         [Structure L M]
         [Structure.ORing L M]
         [M ⊧ₘ* T],
         M ⊧ₘ φ) :
    T ⊨ φ := consequence_iff_consequence.{u, w}.mp <| consequence_iff_eq.mpr fun M _ _ _ hT =>
  letI : Structure.Model L M ⊧ₘ* T :=
    ((Structure.ElementaryEquiv.modelsTheory (Structure.Model.elementaryEquiv L M)).mp hT)
  (Structure.ElementaryEquiv.models (Structure.Model.elementaryEquiv L M)).mpr (H (Structure.Model L M))

end

section

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

end

end Arithmetic

end FirstOrder

end LO
