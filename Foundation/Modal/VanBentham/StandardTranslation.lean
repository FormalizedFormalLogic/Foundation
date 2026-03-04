module

public import Foundation.FirstOrder.Basic
public import Foundation.Modal.Kripke.NNFormula

@[expose] public section

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

notation:max "ℒₖᵣ" => frame

instance : Language.LT ℒₖᵣ := ⟨Frame.Rel.lt⟩

end Language


abbrev KripkeFrameSemisentence := Semisentence ℒₖᵣ

abbrev KripkeFrameSentence := Sentence ℒₖᵣ


namespace Frame

variable {α : Type*}

def forces (a : ℕ) : Semiformula.Operator ℒₖᵣ 1 := ⟨Semiformula.rel (Language.Frame.Rel.pred a) ![#0]⟩

open Lean PrettyPrinter Delaborator

syntax:45 first_order_term:45 " ⊩ " term :max : first_order_formula

macro_rules
  | `(⤫formula(lit)[ $binders* | $fbinders* | $t:first_order_term ⊩ $a:term]) => `(Semiformula.Operator.operator (forces $a) ![⤫term(lit)[ $binders* | $fbinders* | $t ]])

def transitive : KripkeFrameSentence := “∀ x y z, x < y → y < z → x < z”

def monotone (a : ℕ) : KripkeFrameSentence := “∀ x y, x < y → x ⊩ a → y ⊩ a”

end Frame

end LO.FirstOrder


namespace LO.Modal

open NNFormula FirstOrder

def standardTranslation : NNFormula ℕ → FirstOrder.KripkeFrameSemisentence 1
  | .atom  a => “x. x ⊩ a”
  | .natom a => “x. ¬x ⊩ a”
  | .verum   => “⊤”
  | .falsum  => “⊥”
  | .and φ ψ => “x. (!(standardTranslation φ) x) ∧ (!(standardTranslation ψ) x)”
  | .or φ ψ  => “x. (!(standardTranslation φ) x) ∨ (!(standardTranslation ψ) x)”
  | .box φ   => “x. ∀ y, x < y → !(standardTranslation φ) y”
  | .dia φ   => “x. ∃ y, x < y ∧ !(standardTranslation φ) y”

postfix:max "¹" => standardTranslation


namespace Kripke.FirstOrder

open FirstOrder.Frame (forces)
open FirstOrder.Semiformula (Operator)

variable {M : Kripke.Model} {x y : M.World} {φ : NNFormula ℕ} {a : ℕ}

instance {M : Model} : FirstOrder.Structure ℒₖᵣ M.World where
  func := fun _ f => PEmpty.elim f
  rel := fun _ r =>
    match r with
    | .pred p => fun v => M p (v 0)
    | .lt     => fun v => v 0 ≺ v 1

@[simp] lemma forces_iff_val : (forces a).val ![x] ↔ M.Val a x:= by rfl

@[simp] lemma lt_iff_rel : (@Operator.LT.lt ℒₖᵣ _).val ![x, y] ↔ x ≺ y := by rfl

/-- BdRV Prop 2.47 (i) -/
lemma correspondence_satisfies : x ⊧ φ ↔ M ⊧/![x] φ¹ := by
  induction φ using NNFormula.rec' generalizing x with
  | hBox φ ihφ =>
    suffices x ⊧ □φ ↔ ∀ y, x ≺ y → M ⊧/![y] (φ¹) by
      simp [standardTranslation];
      convert this;
      simp;
    constructor;
    . intro h y Rxy;
      exact ihφ.mp $ h y Rxy;
    . intro h y Rxy;
      exact ihφ.mpr $ h y Rxy;
  | hDia φ ihφ =>
    suffices x ⊧ ◇φ ↔ ∃ y, x ≺ y ∧ M ⊧/![y] (φ¹) by
      simp [standardTranslation];
      convert this;
      simp;
    constructor;
    . rintro ⟨y, Rxy, hy⟩;
      use y;
      constructor;
      . assumption;
      . exact ihφ.mp hy;
    . rintro ⟨y, Rxy, hy⟩;
      use y;
      constructor;
      . assumption;
      . exact ihφ.mpr hy;
  | _ => simp_all [standardTranslation];

/-- BdRV Prop 2.47 (ii) -/
lemma correspondence_validOnModel : M ⊧ φ ↔ M ⊧ₘ ∀⁰ φ¹ := by
  suffices M ⊧ φ ↔ ∀ x : M.World, M ⊧/![x] φ¹ by simpa [FirstOrder.models_iff];
  constructor;
  . intro h x; apply correspondence_satisfies.mp $ h x;
  . intro h x; exact correspondence_satisfies.mpr $ h x;

end Kripke.FirstOrder



end LO.Modal
end
