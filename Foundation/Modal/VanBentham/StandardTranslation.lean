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

/-- Language of Kripke frame for basic modal logic. -/
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

def standardTranslation : NNFormula ℕ → FirstOrder.Semisentence 𝓛𝓕 1
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

open FirstOrder.Frame (pmem)
open FirstOrder.Semiterm

variable {M : Kripke.Model} {x : M.World} {φ : NNFormula ℕ}

noncomputable instance {M : Model} : FirstOrder.Structure 𝓛𝓕 M.World where
  func := fun _ f a => M.world_nonempty.some -- TODO: ?
  rel := fun _ r =>
    match r with
    | .pred p => fun v => M (v 0) p
    | .lt     => fun v => v 0 ≺ v 1

lemma standardTranslation_satisfies : x ⊧ φ ↔ M ⊧ₘ₀ !(φ¹)/[x] := by sorry;

#check LO.FirstOrder.models₀_and_iff

lemma standardTranslation_validOnModel : M ⊧ φ ↔ M ⊧ₘ₀ “∀ x, !(φ¹) x” := by
  induction φ with
  | verum   => tauto;
  | falsum  => tauto;
  | atom a =>
    constructor;
    . intro h;
      sorry;
    . sorry;
  | natom a => sorry;
  | and φ ψ ihφ ihψ =>
    simp_all [standardTranslation]
    constructor;
    . intro h;
      replace ihφ := ihφ.mp $ by intro x; exact h x |>.1;
      replace ihψ := ihψ.mp $ by intro x; exact h x |>.2;
      sorry;
    . sorry;
  | or φ ψ ihφ ihψ =>
    constructor;
    . intro h;
      sorry;
    . sorry;
  | box φ ihφ =>
    simp_all [standardTranslation];
    constructor;
    . intro h;
      sorry;
    . intro h;
      sorry;
  | dia φ ihφ =>
    constructor;
    . intro h;
      dsimp [standardTranslation];
      sorry;
    . sorry;

end Kripke



end LO.Modal
