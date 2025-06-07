import Foundation.Modal.Kripke.Completeness
import Foundation.Vorspiel.Relation.Supplemental


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
