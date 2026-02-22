module

public import Foundation.Modal.Kripke.Root

@[expose] public section

namespace LO.Modal

open Formula (atom)
open Formula.Kripke

namespace Kripke

variable {F : Frame}

section

/--
  There is no detour in `x < y`,
  i.e. there is no `u` such that `x < u < y` and `u ≠ x` and `u ≠ y`.
-/
class Frame.IsDetourFree (F : Frame) : Prop where
  detour_free : ∀ {x u y : F}, x ≺ u → u ≺ y → (u = x ∨ u = y)

lemma Frame.detour_free [F.IsDetourFree] : ∀ {x u y : F}, x ≺ u → u ≺ y → (u = x ∨ u = y) := IsDetourFree.detour_free

lemma Frame.not_exists_detour [F.IsDetourFree] {x y : F} : ¬∃ u, u ≠ x ∧ u ≠ y ∧ x ≺ u ∧ u ≺ y := by
  by_contra! hC;
  obtain ⟨u, nexy, neuy, Rxy, Ruy⟩ := hC;
  rcases F.detour_free Rxy Ruy with (rfl | rfl) <;> contradiction;

lemma Frame.IsDetourFree.of_not_exists_detour (h : ∀ {x y : F}, ¬∃ u, u ≠ x ∧ u ≠ y ∧ x ≺ u ∧ u ≺ y) : Frame.IsDetourFree F := by
  constructor;
  rintro x y u Rxu Ruy;
  contrapose! h;
  use x, u, y;
  tauto;

instance [F.IsFinite] [F.IsDetourFree] : F.IsAntisymmetric := by
  constructor;
  intro x y Rxy Ryx;
  rcases F.detour_free Rxy Ryx with rfl | rfl <;> trivial;

instance {r : F.World} [F.IsDetourFree] : (F↾r).IsDetourFree := ⟨by
  rintro ⟨x, (rfl | Rrx)⟩ ⟨u, (rfl | Rru)⟩ ⟨y, (rfl | Rry)⟩ Rxu Ruy <;>
  rcases F.detour_free Rxu Ruy with h | h <;> simp_all;
⟩

end

section definability

instance : whitepoint.IsDetourFree := ⟨by tauto⟩

lemma validate_axiomH_of_isDetourFree [F.IsDetourFree] : F ⊧ (Axioms.H (.atom 0)) := by
  have := @F.detour_free _;
  contrapose! this;

  obtain ⟨V, x, h⟩ := ValidOnFrame.exists_valuation_world_of_not this;
  replace h := Satisfies.not_imp_def.mp h;
  have ⟨h₁, h₂⟩ := h;

  replace h₂ := Satisfies.not_box_def.mp h₂;
  obtain ⟨u, Rxu, h₂⟩ := h₂;
  replace ⟨h₂, h₃⟩ := Satisfies.not_imp_def.mp h₂;
  obtain ⟨y, Ruy, h₂⟩ := Satisfies.dia_def.mp h₂;

  use x, u, y;
  refine ⟨Rxu, Ruy, ?_, ?_⟩ <;>
  . by_contra hC;
    subst hC;
    tauto;

lemma isDetourFree_of_validate_axiomH (h : F ⊧ (Axioms.H (.atom 0))) : F.IsDetourFree := by
  constructor;
  contrapose! h;
  rcases h with ⟨x, u, y, Rxu, Ruy, neux, neuy⟩;
  apply ValidOnFrame.not_of_exists_valuation_world;
  use λ _ w => w ≠ u, x;
  simp [Satisfies];
  tauto;

end definability


section canonicality

variable {S} [Entailment S (Formula ℕ)]
variable {𝓢 : S} [Entailment.Consistent 𝓢] [Entailment.K 𝓢]

open Formula.Kripke
open LO.Entailment
     LO.Entailment.FiniteContext
     Modal.Entailment
open canonicalModel
open MaximalConsistentTableau

namespace Canonical

instance [Entailment.HasAxiomH 𝓢] : (canonicalFrame 𝓢).IsDetourFree := ⟨by
  rintro x u y Rxu Ruy;
  by_contra! hC;
  obtain ⟨neux, neuy⟩ := hC;

  obtain ⟨φ, hφu, hφx⟩ := exists₂₁_of_ne neux;
  obtain ⟨ψ, hψu, hψy⟩ := exists₂₁_of_ne neuy;

  suffices φ ⋎ ψ ∈ u.1.1 by
    apply neither ⟨this, iff_mem₂_or.mpr $ ?_⟩;
    tauto;

  have : □(◇(φ ⋎ ψ) ➝ φ ⋎ ψ) ∈ x.1.1 := mdp_mem₁_provable axiomH! $ by
    apply iff_mem₁_or.mpr;
    tauto;
  apply iff_mem₁_imp'.mp $ def_rel_box_mem₁.mp Rxu this;
  apply def_rel_dia_mem₁.mp Ruy;
  apply iff_mem₁_or.mpr;
  tauto;
⟩

end Canonical

end canonicality

end Kripke

end LO.Modal
end
