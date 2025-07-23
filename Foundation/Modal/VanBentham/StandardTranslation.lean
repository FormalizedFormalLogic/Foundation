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

def forces (a : ℕ) : Semiformula.Operator 𝓛𝓕 1 := ⟨Semiformula.rel (Language.Frame.Rel.pred a) ![#0]⟩

open Lean PrettyPrinter Delaborator

syntax:45 first_order_term:45 " ⊩ " term :max : first_order_formula

macro_rules
  | `(⤫formula[ $binders* | $fbinders* | $t:first_order_term ⊩ $a:term]) => `(Semiformula.Operator.operator (forces $a) ![⤫term[ $binders* | $fbinders* | $t ]])

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

postfix:max "¹" => standardTranslation


namespace Kripke.FirstOrder

open FirstOrder.Frame (forces)
open FirstOrder.Semiformula (Operator)

variable {M : Kripke.Model} {x y : M.World} {φ : NNFormula ℕ} {a : ℕ}

instance {M : Model} : FirstOrder.Structure 𝓛𝓕 M.World where
  func := fun _ f => PEmpty.elim f
  rel := fun _ r =>
    match r with
    | .pred p => fun v => M (v 0) p
    | .lt     => fun v => v 0 ≺ v 1

@[simp] lemma forces_iff_val : (forces a).val ![x] ↔ M.Val x a:= by rfl

@[simp] lemma lt_iff_rel : (@Operator.LT.lt 𝓛𝓕 _).val ![x, y] ↔ x ≺ y := by rfl

/-- BdRV Prop 2.47 (i) -/
lemma correspondence_satisfies : x ⊧ φ ↔ M ⊧/![x] φ¹ := by
  induction φ using NNFormula.rec' generalizing x with
  | hBox φ ihφ =>
    suffices  x ⊧ □φ ↔ ∀ y, x ≺ y → M ⊧/![y] (φ¹) by
      simp [standardTranslation];
      convert this;
      simp;
    constructor;
    . intro h y Rxy;
      exact ihφ.mp $ h y Rxy;
    . intro h y Rxy;
      exact ihφ.mpr $ h y Rxy;
  | hDia φ ihφ =>
    suffices  x ⊧ ◇φ ↔ ∃ y, x ≺ y ∧ M ⊧/![y] (φ¹) by
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
lemma correspondence_validOnModel : M ⊧ φ ↔ M ⊧ₘ₀ “∀ x, !φ¹ x” := by
  induction φ using NNFormula.cases' with
  | hVerum => tauto;
  | hFalsum => tauto;
  | hAtom a => simp [standardTranslation, Kripke.ValidOnModel, FirstOrder.models₀_iff]; tauto;
  | hNatom a => simp [standardTranslation, Kripke.ValidOnModel, FirstOrder.models₀_iff]; tauto;
  | hAnd φ ψ =>
    suffices (∀ x : M.World, x ⊧ φ ∧ x ⊧ ψ) ↔ (∀ x : M.World, M ⊧/![x] φ¹ ∧ M ⊧/![x] ψ¹) by
      simpa [Kripke.ValidOnModel, FirstOrder.models₀_iff, standardTranslation];
    constructor;
    · intro h x;
      constructor;
      . apply correspondence_satisfies.mp; exact h x |>.1;
      . apply correspondence_satisfies.mp; exact h x |>.2;
    . intro h x;
      constructor;
      . apply correspondence_satisfies.mpr; exact h x |>.1;
      . apply correspondence_satisfies.mpr; exact h x |>.2;
  | hOr φ ψ =>
    suffices (∀ x : M.World, x ⊧ φ ∨ x ⊧ ψ) ↔ (∀ x : M.World, M ⊧/![x] φ¹ ∨ M ⊧/![x] ψ¹) by
      simpa [Kripke.ValidOnModel, FirstOrder.models₀_iff, standardTranslation];
    constructor;
    . intro h x;
      rcases h x with (hφ | hψ);
      . left; apply correspondence_satisfies.mp hφ;
      . right; apply correspondence_satisfies.mp hψ;
    . intro h x;
      rcases h x with (hφ | hψ);
      . left; apply correspondence_satisfies.mpr hφ;
      . right; apply correspondence_satisfies.mpr hψ;
  | hBox φ =>
    /-
    suffices (∀ x : M.World, x ⊧ □φ) ↔ ∀ x : M.World, ∀ y, x ≺ y → M ⊧/![y] φ¹ by
      simpa [standardTranslation, Kripke.ValidOnModel, FirstOrder.models₀_iff];
    -/
    suffices (∀ x : M.World, x ⊧ □φ) ↔ ∀ x : M.World, ∀ y, x ≺ y →
      (FirstOrder.Semiformula.Eval instStructureFrameWorld ![y, x] Empty.elim)
      ((FirstOrder.Rewriting.app (FirstOrder.Rew.substs ![FirstOrder.Semiterm.bvar 0]).q)
      (φ¹/[FirstOrder.Semiterm.bvar 0])) by
      simpa [standardTranslation, Kripke.ValidOnModel, FirstOrder.models₀_iff];
    constructor;
    . intro h x y Rxy;
      have := correspondence_satisfies.mp $ @h x y Rxy;
      sorry;
    . intro h x y Rxy;
      apply correspondence_satisfies.mpr;
      have := h x y Rxy;
      sorry;
  | hDia φ =>
    /-
    suffices (∀ x : M.World, x ⊧ ◇φ) ↔ ∀ x : M.World, ∃ y, x ≺ y ∧ M ⊧/![y] φ¹ by
      simpa [standardTranslation, Kripke.ValidOnModel, FirstOrder.models₀_iff];
    -/
    suffices (∀ x : M.World, x ⊧ ◇φ) ↔ ∀ x : M.World, ∃ y, x ≺ y ∧
      (FirstOrder.Semiformula.Eval instStructureFrameWorld ![y, x] Empty.elim)
      ((FirstOrder.Rewriting.app (FirstOrder.Rew.substs ![FirstOrder.Semiterm.bvar 0]).q)
      (φ¹/[FirstOrder.Semiterm.bvar 0])) by
      simpa [standardTranslation, Kripke.ValidOnModel, FirstOrder.models₀_iff];
    constructor;
    . intro h x;
      obtain ⟨y, Rxy, hy⟩ := @h x;
      use y;
      constructor;
      . exact Rxy;
      . have := correspondence_satisfies.mp hy;
        sorry;
    . intro h x;
      obtain ⟨y, Rxy, hy⟩ := @h x;
      use y;
      constructor;
      . exact Rxy;
      . apply correspondence_satisfies.mpr;
        sorry;

end Kripke.FirstOrder



end LO.Modal
