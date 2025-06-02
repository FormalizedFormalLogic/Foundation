import Foundation.Modal.Kripke.Completeness
import Foundation.Vorspiel.Relation.Supplemental


section

variable {α : Type u} (rel : α → α → Prop)

def SobocinskiCondition := ∀ x y z, x ≠ y → rel x y → rel x z → rel z y

class SatisfiesSobocinskiCondition (α) (rel : α → α → Prop) : Prop where
  sobCondition : SobocinskiCondition rel

instance [SatisfiesSobocinskiCondition _ rel] : IsConnected _ rel := ⟨by
  rintro x y z ⟨Rxy, Rxz⟩;
  by_cases hxy : x = y;
  . subst hxy;
    left;
    assumption;
  . right;
    apply SatisfiesSobocinskiCondition.sobCondition x y z hxy Rxy Rxz;
⟩

end


namespace LO.Modal

open Formula (atom)
open Formula.Kripke

namespace Kripke

section definability

variable {F : Kripke.Frame}

lemma validate_axiomPoint4_of_sobocinskiCondition : SobocinskiCondition F.Rel → F ⊧ (Axioms.Point4 (.atom 0)) := by
  dsimp [SobocinskiCondition];
  contrapose!;
  intro h;
  obtain ⟨V, x, h⟩ := ValidOnFrame.exists_valuation_world_of_not h;

  replace h := Satisfies.not_imp_def.mp h;
  have ⟨h₁, h₂⟩ := h;
  replace h₂ := Satisfies.not_imp_def.mp h₂;
  replace ⟨h₂, h₃⟩ := h₂;

  replace h₂ := Satisfies.dia_def.mp h₂;
  obtain ⟨z, Rxz, hz⟩ := h₂;

  replace h₃ := Satisfies.not_box_def.mp h₃;
  obtain ⟨y, Rxy, hy⟩ := h₃;

  use x, y, z;
  refine ⟨?_, Rxy, Rxz, ?_⟩;
  . by_contra hC; subst hC; contradiction;
  . by_contra hC; apply hy; apply hz; assumption;

lemma validate_axiomPoint4_of_satisfiesSobocinskiCondition [SatisfiesSobocinskiCondition _ F.Rel] : F ⊧ (Axioms.Point4 (.atom 0)) :=
  validate_axiomPoint4_of_sobocinskiCondition SatisfiesSobocinskiCondition.sobCondition

lemma sobocinskiCondition_of_validate_axiomPoint4 : F ⊧ (Axioms.Point4 (.atom 0)) → SobocinskiCondition F.Rel := by
  dsimp [SobocinskiCondition];
  contrapose!;
  rintro ⟨x, y, z, nexy, Rxy, Rxz, Rzy⟩;
  apply ValidOnFrame.not_of_exists_valuation_world;
  suffices ∃ V : Valuation F, ∃ x, V x 0 ∧ ∃ z, x ≺ z ∧ (∀ w, z ≺ w → V w 0) ∧ ∃ y, x ≺ y ∧ ¬V y 0 by
    simpa [Axioms.Point4, Satisfies];
  use (λ w _ => w = x ∨ z ≺ w), x;
  constructor;
  . tauto;
  . use z;
    constructor;
    . assumption
    . constructor;
      . tauto;
      . use y;
        constructor;
        . assumption;
        . tauto;

instance : SatisfiesSobocinskiCondition _ whitepoint := ⟨by tauto⟩

end definability


section canonicality

variable {S} [Entailment (Formula ℕ) S]
variable {𝓢 : S} [Entailment.Consistent 𝓢]

open Formula.Kripke
open LO.Entailment
     LO.Entailment.FiniteContext
     Modal.Entailment
open canonicalModel
open MaximalConsistentTableau

namespace Canonical

open Classical in
instance [Entailment.K 𝓢] [Entailment.HasAxiomPoint4 𝓢] : SatisfiesSobocinskiCondition _ (canonicalFrame 𝓢).Rel := ⟨by
  intro x y z nexy Rxy Rxz;

  replace Rxz := def_rel_dia_mem₁.mp Rxz;

  apply def_rel_box_mem₁.mpr;
  intro φ hφ;
  have : φ ➝ □φ ∈ x.1.1 := mdp_mem₁_provable (show 𝓢 ⊢! ◇□φ ➝ φ ➝ □φ by exact C!_swap $ axiomPoint4!) $ Rxz hφ;
  rcases iff_mem₁_imp.mp this with (this | this);
  . have := def_rel_box_mem₁.mp Rxy;
    sorry;
  . exact def_rel_box_mem₁.mp Rxy this;
⟩

end Canonical

end canonicality

end Kripke

end LO.Modal
