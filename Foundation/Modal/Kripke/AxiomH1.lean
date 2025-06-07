import Foundation.Modal.Kripke.Completeness
import Foundation.Vorspiel.Relation.Supplemental
import Foundation.Modal.Kripke.AxiomGrz

section

variable {α : Type u} (rel : α → α → Prop)

/--
  There is no detour in `x < y`,
  i.e. there is no `u` such that `x < u < y` and `u ≠ x` and `u ≠ y`.
-/
def DetourFree := ∀ {x y z}, rel x y → rel y z → (x = y ∨ y = z)

class IsDetourFree (α) (rel : α → α → Prop) : Prop where
  detourFree : DetourFree rel

lemma DetourFree.not_exists_detour :
  DetourFree (α := α) rel ↔ ∀ {x y}, ¬∃ u, x ≠ u ∧ y ≠ u ∧ rel x u ∧ rel u y := by
  dsimp [DetourFree];
  push_neg;
  constructor
  . rintro h x z y nexz nezy Rxy Ryz;
    rcases h Rxy Ryz with (rfl | rfl) <;> contradiction;
  . rintro h x y z Rxy Ryz;
    by_contra! hC;
    apply @h x z y <;> tauto

end


namespace LO.Modal

open Formula (atom)
open Formula.Kripke

namespace Kripke

section definability

variable {F : Kripke.Frame}

lemma validate_axiomH1_of_detourFree : DetourFree F.Rel → F ⊧ (Axioms.H1 (.atom 0)) := by
  dsimp [DetourFree];
  contrapose!;
  intro h;
  obtain ⟨V, x, h⟩ := ValidOnFrame.exists_valuation_world_of_not h;
  replace h := Satisfies.not_imp_def.mp h;
  have ⟨h₁, h₂⟩ := h;
  replace h₂ := Satisfies.not_box_def.mp h₂;
  obtain ⟨y, Rxy, h₂⟩ := h₂;
  replace ⟨h₂, h₃⟩ := Satisfies.not_imp_def.mp h₂;
  obtain ⟨z, Ryz, h₂⟩ := Satisfies.dia_def.mp h₂;
  use x, y, z;
  refine ⟨Rxy, Ryz, ?_, ?_⟩ <;>
  . by_contra hC; subst hC; tauto;

lemma validate_axiomH1_of_isDetourFree [IsDetourFree _ F.Rel] : F ⊧ (Axioms.H1 (.atom 0)) :=
  validate_axiomH1_of_detourFree IsDetourFree.detourFree

lemma detourFree_of_validate_axiomH1 : F ⊧ (Axioms.H1 (.atom 0)) → DetourFree F.Rel := by
  dsimp [DetourFree];
  contrapose!;
  rintro ⟨x, y, z, Rxy, Ryz, nexy, neyz⟩;
  apply ValidOnFrame.not_of_exists_valuation_world;
  use λ w _ => w ≠ y, x;
  simp [Satisfies, Axioms.H1];
  tauto;

instance : IsDetourFree _ whitepoint := ⟨by tauto⟩

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

instance [Entailment.K 𝓢] [Entailment.HasAxiomH1 𝓢] : IsDetourFree _ (canonicalFrame 𝓢).Rel := ⟨by
  rintro x y z Rxy Ryz;
  by_contra! hC;
  obtain ⟨nexy, neyz⟩ := hC;

  obtain ⟨φ, hφx, hφy⟩ := exists₁₂_of_ne nexy;
  obtain ⟨ψ, hψy, hψz⟩ := exists₂₁_of_ne neyz;

  suffices φ ⋎ ψ ∈ y.1.1 by apply neither ⟨this, iff_mem₂_or.mpr $ ?_⟩; tauto;

  have : □(◇(φ ⋎ ψ) ➝ φ ⋎ ψ) ∈ x.1.1 := mdp_mem₁_provable axiomH1! $ by
    apply iff_mem₁_or.mpr;
    tauto;
  have : ◇(φ ⋎ ψ) ➝ φ ⋎ ψ ∈ y.1.1 := def_rel_box_mem₁.mp Rxy this;
  exact iff_mem₁_imp'.mp this $ by
    apply def_rel_dia_mem₁.mp Ryz;
    apply iff_mem₁_or.mpr;
    tauto;
⟩

end Canonical

end canonicality

end Kripke

end LO.Modal
