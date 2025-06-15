import Foundation.Modal.Kripke.Completeness



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

instance [IsEuclidean _ rel] : SatisfiesSobocinskiCondition _ rel := ⟨by
  intro x y z _ Rxy Rxz;
  apply IsEuclidean.euclidean Rxy Rxz;
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

  replace h₁ := Satisfies.dia_def.mp h₁;
  obtain ⟨z, Rxz, hz⟩ := h₁;

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
  suffices ∃ V : Valuation F, ∃ x z, x ≺ z ∧ (∀ w, z ≺ w → V w 0) ∧ V x 0 ∧ ∃ y, x ≺ y ∧ ¬V y 0 by
    simpa [Axioms.Point4, Satisfies];
  use (λ w _ => w = x ∨ z ≺ w), x, z;
  refine ⟨?_, ?_, ?_, ?_⟩;
  . assumption;
  . tauto;
  . tauto;
  . use y;
    tauto;

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

instance [Entailment.K 𝓢] [Entailment.HasAxiomPoint4 𝓢] : SatisfiesSobocinskiCondition _ (canonicalFrame 𝓢).Rel := ⟨by
  intro x y z nexy Rxy Rxz;
  obtain ⟨φ, hφ₁, hφ₂⟩ := exists₁₂_of_ne nexy;
  apply def_rel_box_mem₁.mpr;
  intro ψ hψ;
  have : (φ ⋎ ψ) ➝ □(φ ⋎ ψ) ∈ x.1.1 := mdp_mem₁_provable axiomPoint4! $ def_rel_dia_mem₁.mp Rxz $ mdp_mem₁_provable (by
    apply imply_box_distribute'!;
    simp;
  ) hψ;
  have : □(φ ⋎ ψ) ∈ x.1.1 := iff_mem₁_imp'.mp this $ by
    apply iff_mem₁_or.mpr;
    left;
    tauto;
  rcases iff_mem₁_or.mp $ (iff_mem₁_box.mp this) Rxy with (_ | _);
  . exfalso;
    apply y.neither (φ := φ);
    constructor <;> assumption;
  . assumption;
⟩

end Canonical

end canonicality

end Kripke

end LO.Modal
