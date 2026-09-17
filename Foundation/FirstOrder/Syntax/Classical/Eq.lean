module

public import Foundation.FirstOrder.Syntax.Classical.BinderNotation
public import Foundation.Vorspiel.Finset.Card

@[expose] public section
set_option autoImplicit true
set_option linter.style.longLine false

namespace Matrix

variable {α : Type*}

def iget [Inhabited α] (v : Fin k → α) (x : ℕ) : α := if h : x < k then v ⟨x, h⟩ else default

end Matrix

namespace FFL

namespace FirstOrder

variable {L : Language} {ξ : Type*} [Semiformula.Operator.Eq L]

namespace Theory

section Eq

variable (L)

abbrev Eq.refl : Sentence L := “∀ x, x = x”

abbrev Eq.symm : Sentence L := “∀ x y, x = y → y = x”

abbrev Eq.trans : Sentence L := “∀ x y z, x = y → y = z → x = z”

variable {L}

abbrev Eq.funcExt {k} (f : L.Func k) : Sentence L :=
  let σ : Semisentence L (k + k) :=
    (Matrix.conj fun i : Fin k ↦ “#(i.addCast k) = #(i.addNat k)”) 🡒
      op(=).operator ![Semiterm.func f (fun i ↦ #(i.addCast k)), Semiterm.func f (fun i ↦ #(i.addNat k))]
  ∀¹* σ

abbrev Eq.relExt {k} (r : L.Rel k) : Sentence L :=
  let σ : Semisentence L (k + k) :=
    (Matrix.conj fun i : Fin k ↦ “#(i.addCast k) = #(i.addNat k)”) 🡒
      Semiformula.rel r (fun i ↦ #(i.addCast k)) 🡒 Semiformula.rel r (fun i ↦ #(i.addNat k))
  ∀¹* σ

variable (L)

inductive eqAxiom : Theory L
  | refl : eqAxiom (Eq.refl L)
  | symm : eqAxiom (Eq.symm L)
  | trans : eqAxiom (Eq.trans L)
  | funcExt {k} (f : L.Func k) : eqAxiom (Eq.funcExt f)
  | relExt {k} (r : L.Rel k) : eqAxiom (Eq.relExt r)

notation "𝗘𝗤" => eqAxiom

variable {L}

lemma Eq.defeq :
    𝗘𝗤 L = {Eq.refl L, Eq.symm L, Eq.trans L}
      ∪ Set.range (fun f : (k : ℕ) × L.Func k ↦ Eq.funcExt f.2)
      ∪ Set.range (fun f : (k : ℕ) × L.Rel k ↦ Eq.relExt f.2) := by
  ext φ; constructor
  · rintro ⟨⟩
    case refl => simp
    case symm => simp
    case trans => simp
    case funcExt k f =>
      left; right; exact ⟨⟨k, f⟩, rfl⟩
    case relExt k r =>
      right; exact ⟨⟨k, r⟩, rfl⟩
  · rintro (((rfl | rfl | rfl) | ⟨f, rfl⟩) | ⟨r, rfl⟩)
    · exact eqAxiom.refl
    · exact eqAxiom.symm
    · exact eqAxiom.trans
    · exact eqAxiom.funcExt _
    · exact eqAxiom.relExt _

@[simp] lemma EqAxiom.finite [L.Finite] : Set.Finite (𝗘𝗤 L) := by
  have : Fintype ((k : ℕ) × L.Func k) := Language.Finite.func
  have : Fintype ((k : ℕ) × L.Rel k) := Language.Finite.rel
  rw [Eq.defeq]
  simp [Set.finite_range]

end Eq

end Theory

namespace Semiformula

def existsUnique {ξ} (φ : Semiformula L ξ (n + 1)) : Semiformula L ξ n :=
  “∃ y, !φ y ⋯ ∧ ∀ z, !φ z ⋯ → z = y”

prefix:64 "∃¹! " => existsUnique

end Semiformula

namespace BinderNotation

open Lean PrettyPrinter Delaborator SubExpr

syntax:max "∃! " first_order_formula:0 : first_order_formula
syntax:max "∃! " ident ", " first_order_formula:0 : first_order_formula

macro_rules
  | `(⤫formula($type)[ $binders* | $fbinders* | ∃! $φ:first_order_formula ]) => do
    let v := mkIdent (Name.mkSimple ("var" ++ toString binders.size))
    let binders' := binders.insertIdx 0 v
    `(∃¹! ⤫formula($type)[ $binders'* | $fbinders* | $φ])
  | `(⤫formula($type)[ $binders* | $fbinders* | ∃! $x, $φ ])                 => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
    let binders' := binders.insertIdx 0 x
    `(∃¹! ⤫formula($type)[ $binders'* | $fbinders* | $φ ])

end BinderNotation

end FirstOrder

end FFL

end
