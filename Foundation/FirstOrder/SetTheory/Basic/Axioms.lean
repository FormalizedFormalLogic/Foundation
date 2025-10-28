import Foundation.FirstOrder.SetTheory.Basic.Misc

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

def empty : Sentence ℒₛₑₜ := “∃ e, ∀ y, y ∉ e”

def extentionality : Sentence ℒₛₑₜ := “∀ x y, x = y ↔ ∀ z, z ∈ x ↔ z ∈ y”

def pairing : Sentence ℒₛₑₜ := “∀ x y, ∃ z, ∀ w, w ∈ z ↔ w = x ∨ w = y”

def union : Sentence ℒₛₑₜ := “∀ x, ∃ y, ∀ z, z ∈ y ↔ ∃ w ∈ x, z ∈ w”

def power : Sentence ℒₛₑₜ := “∀ x, ∃ y, ∀ z, z ∈ y ↔ z ⊆ x”

def infinity : Sentence ℒₛₑₜ := “∃ I, (∀ e, !isEmpty e → e ∈ I) ∧ (∀ x ∈ I, ∀ x', !isSucc x' x → x' ∈ I)”

def foundation : Sentence ℒₛₑₜ := “∀ x, !isNonempty x → ∃ y ∈ x, ∀ z ∈ x, z ∉ y”

def separationSchema (φ : SyntacticSemiformula ℒₛₑₜ 1) : Sentence ℒₛₑₜ :=
  .univCl “∀ x, ∃ y, ∀ z, z ∈ y ↔ z ∈ x ∧ !φ z”

def replacementSchema (φ : SyntacticSemiformula ℒₛₑₜ 2) : Sentence ℒₛₑₜ :=
  .univCl “(∀ x, ∃! y, !φ x y) → ∀ X, ∃ Y, ∀ y, y ∈ Y ↔ ∃ x ∈ X, !φ x y”

def choice : Sentence ℒₛₑₜ :=
  “∀ x, (∀ y ∈ x, !isNonempty y) ∧ (∀ y ∈ x, ∀ z ∈ x, y ≠ z → ¬∃ w, w ∈ y ∧ w ∈ z) → ∃ c, ∀ y ∈ x, ∃ u ∈ c, u ∈ y”

end Axiom

/-! ### Zermelo set theory-/

inductive Zermelo : Theory ℒₛₑₜ
  | axiom_of_equality : ∀ φ ∈ 𝗘𝗤, Zermelo φ
  | axiom_of_empty_set : Zermelo Axiom.empty
  | axiom_of_extentionality : Zermelo Axiom.extentionality
  | axiom_of_pairing : Zermelo Axiom.pairing
  | axiom_of_union : Zermelo Axiom.union
  | axiom_of_power_set : Zermelo Axiom.power
  | axiom_of_infinity : Zermelo Axiom.infinity
  | axiom_of_foundation : Zermelo Axiom.foundation
  | axiom_of_separation (φ : SyntacticSemiformula ℒₛₑₜ 1) : Zermelo (Axiom.separationSchema φ)

notation "𝗭" => Zermelo

instance : 𝗘𝗤 ⪯ 𝗭 := Entailment.WeakerThan.ofSubset Zermelo.axiom_of_equality

/-! ### Zermelo-Fraenkel set theory -/

inductive ZermeloFraenkel : Theory ℒₛₑₜ
  | axiom_of_equality : ∀ φ ∈ 𝗘𝗤, ZermeloFraenkel φ
  | axiom_of_empty_set : ZermeloFraenkel Axiom.empty
  | axiom_of_extentionality : ZermeloFraenkel Axiom.extentionality
  | axiom_of_pairing : ZermeloFraenkel Axiom.pairing
  | axiom_of_union : ZermeloFraenkel Axiom.union
  | axiom_of_power_set : ZermeloFraenkel Axiom.power
  | axiom_of_infinity : ZermeloFraenkel Axiom.infinity
  | axiom_of_foundation : ZermeloFraenkel Axiom.foundation
  | axiom_of_separation (φ : SyntacticSemiformula ℒₛₑₜ 1) : ZermeloFraenkel (Axiom.separationSchema φ)
  | axiom_of_replacement (φ : SyntacticSemiformula ℒₛₑₜ 2) : ZermeloFraenkel (Axiom.replacementSchema φ)

notation "𝗭𝗙" => ZermeloFraenkel

instance : 𝗘𝗤 ⪯ 𝗭𝗙 := Entailment.WeakerThan.ofSubset ZermeloFraenkel.axiom_of_equality

lemma Zermelo_subset_ZermeloFraenkel : 𝗭 ⊆ 𝗭𝗙 := by
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

instance : 𝗭 ⪯ 𝗭𝗙 := Entailment.WeakerThan.ofSubset Zermelo_subset_ZermeloFraenkel

/-! ### Zermelo set theory with axiom of choice -/

def ZermeloChoice : Theory ℒₛₑₜ := 𝗭 + {Axiom.choice}

notation "𝗭𝗖" => ZermeloChoice

instance : 𝗭 ⪯ 𝗭𝗖 := inferInstanceAs (𝗭 ⪯ 𝗭 + ({Axiom.choice} : Theory ℒₛₑₜ))

instance : 𝗘𝗤 ⪯ 𝗭𝗖 := Entailment.WeakerThan.trans (inferInstanceAs (𝗘𝗤 ⪯ 𝗭)) inferInstance

/-! ### ZFC -/

def ZermeloFraenkelChoice : Theory ℒₛₑₜ := 𝗭𝗙 + {Axiom.choice}

notation "𝗭𝗙𝗖" => ZermeloFraenkelChoice

instance : 𝗭𝗙 ⪯ 𝗭𝗙𝗖 := inferInstanceAs (𝗭𝗙 ⪯ 𝗭𝗙 + ({Axiom.choice} : Theory ℒₛₑₜ))

instance : 𝗘𝗤 ⪯ 𝗭𝗙𝗖 := Entailment.WeakerThan.trans (inferInstanceAs (𝗘𝗤 ⪯ 𝗭𝗙)) inferInstance

end LO.FirstOrder.SetTheory
