import Foundation.FirstOrder.Basic
import Foundation.Modal.NNFormula
import Foundation.Modal.Kripke.NNFormula

namespace LO.FirstOrder

namespace Language

namespace Frame

inductive Rel : ℕ → Type _
  /-- propositional variable -/
  | pred : ℕ → Rel 1
  /-- binary relation -/
  | lt : Rel 2

end Frame

/-- Language of Kripke frame for mono modal logic. -/
@[reducible]
def frame : Language where
  Func _ := PEmpty
  Rel := Frame.Rel

notation:max "𝓛𝓕" => frame

instance : Language.LT 𝓛𝓕 := ⟨Frame.Rel.lt⟩

end Language

namespace Frame

variable {α : Type*}

def pmem (a : ℕ) : Semiformula.Operator 𝓛𝓕 1 := ⟨Semiformula.rel (Language.Frame.Rel.pred a) ![#0]⟩

open Lean PrettyPrinter Delaborator

syntax:45 first_order_term:45 " ⊩ " term :max : first_order_formula

macro_rules
  | `(⤫formula[ $binders* | $fbinders* | $t:first_order_term ⊩ $a:term]) => `(Semiformula.Operator.operator (pmem $a) ![⤫term[ $binders* | $fbinders* | $t ]])

def transitive : Sentence 𝓛𝓕 := “∀ x y z, x < y → y < z → x < z”

def monotone (a : ℕ) : Sentence 𝓛𝓕 := “∀ x y, x < y → x ⊩ a → y ⊩ a”

end Frame

end LO.FirstOrder


namespace LO.Modal

open NNFormula

def standardTranslation : NNFormula ℕ → LO.FirstOrder.Semisentence 𝓛𝓕 1
  | .atom  a => “x. x ⊩ a”
  | .natom a => “x. ¬x ⊩ a”
  | .verum   => “⊤”
  | .falsum  => “⊥”
  | .and φ ψ => “x. (!(standardTranslation φ) x) ∧ (!(standardTranslation ψ) x)”
  | .or φ ψ  => “x. (!(standardTranslation φ) x) ∨ (!(standardTranslation ψ) x)”
  | .box φ   => “x. ∀ y, x < y → !(standardTranslation φ) y”
  | .dia φ   => “x. ∃ y, x < y ∧ !(standardTranslation φ) y”

local postfix:80 "¹" => standardTranslation

#check (◇((.atom 0) ➝ □(.atom 0)))¹


namespace Kripke

variable {φ : NNFormula ℕ} {M : Kripke.Model}

lemma standardTranslation_satisfies {M : Model} {x : M} : x ⊧ φ := by sorry;

lemma standardTranslation_validOnModel {M : Model} : M ⊧ φ := by sorry;

end Kripke



end LO.Modal
