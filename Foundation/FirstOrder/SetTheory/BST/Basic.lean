module

public import Foundation.FirstOrder.SetTheory.Basic.Misc
public import Foundation.FirstOrder.SetTheory.Schemata

@[expose] public section
/-!
# Basic axioms of set theory

This is BST (basic set theory), which is Zermelo set theory minus replacement. TODO: Find a citation
for the name of this set theory.
-/

namespace FFL.FirstOrder.SetTheory

/-! ### Basic set theory -/

/-- Basic set theory (Zermelo minus separation). -/
inductive IsBasicSetTheoryAxiom : SetTheorySentence → Prop
  /-- Axiom of equality. -/
  | equality       : ∀ φ ∈ 𝗘𝗤 ℒₛₑₜ, IsBasicSetTheoryAxiom φ
  /-- Axiom of empty set. -/
  | empty_set      : IsBasicSetTheoryAxiom “∃ e, !isEmpty e”
  /-- Axiom of extensionality. -/
  | extensionality : IsBasicSetTheoryAxiom “∀ x y, x = y ↔ ∀ z, z ∈ x ↔ z ∈ y”
  /-- Axiom of pairing. -/
  | pairing        : IsBasicSetTheoryAxiom “∀ x y, ∃ z, ∀ w, w ∈ z ↔ w = x ∨ w = y”
  /-- Axiom of empty union. -/
  | union          : IsBasicSetTheoryAxiom
      “∀ x, ∃ y, ∀ z, z ∈ y ↔ ∃ w ∈ x, z ∈ w”
  /-- Axiom of power set. -/
  | power_set      : IsBasicSetTheoryAxiom “∀ x, ∃ y, ∀ z, z ∈ y ↔ z ⊆ x”
  /-- Axiom of infinity. -/
  | infinity       : IsBasicSetTheoryAxiom “∃ I, (∀ e, !isEmpty e → e ∈ I) ∧
    (∀ x ∈ I, ∀ x', !isSucc x' x → x' ∈ I)”
  /-- Axiom of foundation. -/
  | foundation     : IsBasicSetTheoryAxiom
      “∀ x, !isNonempty x → ∃ y ∈ x, ∀ z ∈ x, z ∉ y”

abbrev BasicSetTheory : SetTheory := Set.ofPred IsBasicSetTheoryAxiom

notation "𝗕𝗦𝗧" => BasicSetTheory

instance : 𝗘𝗤 _ ⪯ 𝗕𝗦𝗧 :=
  Entailment.WeakerThan.ofSubset IsBasicSetTheoryAxiom.equality

end FFL.FirstOrder.SetTheory
