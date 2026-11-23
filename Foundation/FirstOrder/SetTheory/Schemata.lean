module

public import Foundation.FirstOrder.SetTheory.Basic.Misc

@[expose] public section
/-!
# Axiom schemata in set theory
-/

namespace FFL.FirstOrder.SetTheory

namespace Axiom

/-- Axiom schema of separation (Aussonderungsaxiom). -/
def separationSchema (φ : SetTheorySemiproposition 1) : SetTheorySentence :=
  .univCl “∀ x, ∃ y, ∀ z, z ∈ y ↔ z ∈ x ∧ !φ z”

/-- Axiom schema of replacement. -/
def replacementSchema (φ : SetTheorySemiproposition 2) : SetTheorySentence :=
  .univCl “(∀ x, ∃! y, !φ x y) → ∀ X, ∃ Y, ∀ y, y ∈ Y ↔ ∃ x ∈ X, !φ x y”

end Axiom

/-! ### Axiom schema of separation -/

inductive IsSeparationAxiom : SetTheorySentence → Prop
  /-- Axiom schema of separation. -/
  | separation (φ : SetTheorySemiproposition 1) :
      IsSeparationAxiom (Axiom.separationSchema φ)

abbrev Separation : SetTheory := Set.ofPred IsSeparationAxiom

/-- The axiom schema of separation. (This is a theory containing all its instances.) -/
notation "𝗦𝗘𝗣" => Separation

/-! ### Axiom schema of replacement -/

inductive IsReplacementAxiom : SetTheorySentence → Prop
  /-- Axiom schema of separation. -/
  | replacement (φ : SetTheorySemiproposition 2) :
      IsReplacementAxiom (Axiom.replacementSchema φ)

abbrev Replacement : SetTheory := Set.ofPred IsReplacementAxiom

/-- The axiom schema of replacement. (This is a theory containing all its instances.) -/
notation "𝗥𝗘𝗣𝗟" => Replacement

end FFL.FirstOrder.SetTheory
