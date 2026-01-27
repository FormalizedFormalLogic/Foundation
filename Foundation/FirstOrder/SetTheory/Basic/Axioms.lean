module

public import Foundation.FirstOrder.SetTheory.Basic.Misc

@[expose] public section
/-!
# Basic axioms of set theory

reference: Ralf Schindler, "Set Theory, Exploring Independence and Truth"
-/

namespace LO.FirstOrder.SetTheory

def isSubsetOf : Semisentence ℒₛₑₜ 2 := “x y. ∀ z ∈ x, z ∈ y”

syntax:45 first_order_term:45 " ⊆ " first_order_term:0 : first_order_formula

open Lean Elab PrettyPrinter Delaborator SubExpr in
macro_rules
  | `(⤫formula($type)[ $binders* | $fbinders* | $t:first_order_term ⊆ $u:first_order_term ]) =>
    `(⤫formula($type)[ $binders* | $fbinders* | !isSubsetOf $t:first_order_term $u:first_order_term ])

def isEmpty : Semisentence ℒₛₑₜ 1 := “x. ∀ y, y ∉ x”

def isNonempty : Semisentence ℒₛₑₜ 1 := “x. ∃ y, y ∈ x”

def isSucc : Semisentence ℒₛₑₜ 2 := “y x. ∀ z, z ∈ y ↔ z = x ∨ z ∈ x”

namespace Axiom

/-- Axiom of empty set. -/
def empty : Sentence ℒₛₑₜ := “∃ e, ∀ y, y ∉ e”

/-- Axiom of extentionality. -/
def extentionality : Sentence ℒₛₑₜ := “∀ x y, x = y ↔ ∀ z, z ∈ x ↔ z ∈ y”

/-- Axiom of pairing. -/
def pairing : Sentence ℒₛₑₜ := “∀ x y, ∃ z, ∀ w, w ∈ z ↔ w = x ∨ w = y”

/-- Axiom of union. -/
def union : Sentence ℒₛₑₜ := “∀ x, ∃ y, ∀ z, z ∈ y ↔ ∃ w ∈ x, z ∈ w”

/-- Axiom of power set. -/
def power : Sentence ℒₛₑₜ := “∀ x, ∃ y, ∀ z, z ∈ y ↔ z ⊆ x”

/-- Axiom of infinity. -/
def infinity : Sentence ℒₛₑₜ := “∃ I, (∀ e, !isEmpty e → e ∈ I) ∧ (∀ x ∈ I, ∀ x', !isSucc x' x → x' ∈ I)”

/-- Axiom of foundation. -/
def foundation : Sentence ℒₛₑₜ := “∀ x, !isNonempty x → ∃ y ∈ x, ∀ z ∈ x, z ∉ y”

/-- Axiom schema of separation (Aussonderungsaxiom). -/
def separationSchema (φ : SyntacticSemiformula ℒₛₑₜ 1) : Sentence ℒₛₑₜ :=
  .univCl “∀ x, ∃ y, ∀ z, z ∈ y ↔ z ∈ x ∧ !φ z”

/-- Axiom schema of replacement. -/
def replacementSchema (φ : SyntacticSemiformula ℒₛₑₜ 2) : Sentence ℒₛₑₜ :=
  .univCl “(∀ x, ∃! y, !φ x y) → ∀ X, ∃ Y, ∀ y, y ∈ Y ↔ ∃ x ∈ X, !φ x y”

/-- Axiom of choice. -/
def choice : Sentence ℒₛₑₜ :=
  “∀ 𝓧, (∀ X ∈ 𝓧, !isNonempty X) ∧ (∀ X ∈ 𝓧, ∀ Y ∈ 𝓧, (∃ z, z ∈ X ∧ z ∈ Y) → X = Y) → ∃ C, ∀ X ∈ 𝓧, ∃! x, x ∈ C ∧ x ∈ X”

end Axiom

/-! ### Zermelo set theory-/

/-- Zermelo set theory. -/
inductive Zermelo : Theory ℒₛₑₜ
  /-- Axiom of equality. -/
  | axiom_of_equality : ∀ φ ∈ 𝗘𝗤, Zermelo φ
  /-- Axiom of empty set. -/
  | axiom_of_empty_set : Zermelo Axiom.empty
  /-- Axiom of extentionality. -/
  | axiom_of_extentionality : Zermelo Axiom.extentionality
  /-- Axiom of pairing. -/
  | axiom_of_pairing : Zermelo Axiom.pairing
  /-- Axiom of empty union. -/
  | axiom_of_union : Zermelo Axiom.union
  /-- Axiom of power set. -/
  | axiom_of_power_set : Zermelo Axiom.power
  /-- Axiom of infinity. -/
  | axiom_of_infinity : Zermelo Axiom.infinity
  /-- Axiom of foundation. -/
  | axiom_of_foundation : Zermelo Axiom.foundation
  /-- Axiom schema of separation. -/
  | axiom_of_separation (φ : SyntacticSemiformula ℒₛₑₜ 1) : Zermelo (Axiom.separationSchema φ)

notation "𝗭" => Zermelo

instance : 𝗘𝗤 ⪯ 𝗭 := Entailment.WeakerThan.ofSubset Zermelo.axiom_of_equality

/-! ### Zermelo-Fraenkel set theory -/

/-- Zermelo-Fraenkel set theory. -/
inductive ZermeloFraenkel : Theory ℒₛₑₜ
  /-- Axiom of equality. -/
  | axiom_of_equality : ∀ φ ∈ 𝗘𝗤, ZermeloFraenkel φ
  /-- Axiom of empty set. -/
  | axiom_of_empty_set : ZermeloFraenkel Axiom.empty
  /-- Axiom of extentionality. -/
  | axiom_of_extentionality : ZermeloFraenkel Axiom.extentionality
  /-- Axiom of pairing. -/
  | axiom_of_pairing : ZermeloFraenkel Axiom.pairing
  /-- Axiom of union. -/
  | axiom_of_union : ZermeloFraenkel Axiom.union
  /-- Axiom of power set. -/
  | axiom_of_power_set : ZermeloFraenkel Axiom.power
  /-- Axiom of infinity. -/
  | axiom_of_infinity : ZermeloFraenkel Axiom.infinity
  /-- Axiom of foundation. -/
  | axiom_of_foundation : ZermeloFraenkel Axiom.foundation
  /-- Axiom schema of separation. -/
  | axiom_of_separation (φ : SyntacticSemiformula ℒₛₑₜ 1) : ZermeloFraenkel (Axiom.separationSchema φ)
  /-- Axiom schema of replacement. -/
  | axiom_of_replacement (φ : SyntacticSemiformula ℒₛₑₜ 2) : ZermeloFraenkel (Axiom.replacementSchema φ)

notation "𝗭𝗙" => ZermeloFraenkel

instance : 𝗘𝗤 ⪯ 𝗭𝗙 := Entailment.WeakerThan.ofSubset ZermeloFraenkel.axiom_of_equality

lemma z_subset_zf : 𝗭 ⊆ 𝗭𝗙 := by
  rintro φ ⟨h⟩
  · exact ZermeloFraenkel.axiom_of_equality φ (by assumption)
  · exact ZermeloFraenkel.axiom_of_empty_set
  · exact ZermeloFraenkel.axiom_of_extentionality
  · exact ZermeloFraenkel.axiom_of_pairing
  · exact ZermeloFraenkel.axiom_of_union
  · exact ZermeloFraenkel.axiom_of_power_set
  · exact ZermeloFraenkel.axiom_of_infinity
  · exact ZermeloFraenkel.axiom_of_foundation
  · exact ZermeloFraenkel.axiom_of_separation _

instance : 𝗭 ⪯ 𝗭𝗙 := Entailment.WeakerThan.ofSubset z_subset_zf

/-! ### Zermelo set theory with axiom of choice -/

/-- AC: Axiom of choice. -/
def AxiomOfChoice : Theory ℒₛₑₜ := {Axiom.choice}

notation "𝗔𝗖" => AxiomOfChoice

/-- Zermelo set theory with axiom of choice. -/
abbrev ZermeloChoice : Theory ℒₛₑₜ := 𝗭 + 𝗔𝗖

notation "𝗭𝗖" => ZermeloChoice

instance : 𝗭 ⪯ 𝗭𝗖 := inferInstance

instance : 𝗘𝗤 ⪯ 𝗭𝗖 := Entailment.WeakerThan.trans (inferInstanceAs (𝗘𝗤 ⪯ 𝗭)) inferInstance

/-! ### Zermelo-Fraenkel set theory with axiom of choice -/

/-- Zermelo-Fraenkel set theory with axiom of choice. -/
abbrev ZermeloFraenkelChoice : Theory ℒₛₑₜ := 𝗭𝗙 + 𝗔𝗖

notation "𝗭𝗙𝗖" => ZermeloFraenkelChoice

instance : 𝗭𝗙 ⪯ 𝗭𝗙𝗖 := inferInstance

instance : 𝗘𝗤 ⪯ 𝗭𝗙𝗖 := Entailment.WeakerThan.trans (inferInstanceAs (𝗘𝗤 ⪯ 𝗭𝗙)) inferInstance

lemma zc_subset_zfc : 𝗭𝗖 ⊆ 𝗭𝗙𝗖 := Set.union_subset_union_left _ z_subset_zf

instance : 𝗭𝗖 ⪯ 𝗭𝗙𝗖 := Entailment.WeakerThan.ofSubset zc_subset_zfc

end LO.FirstOrder.SetTheory
