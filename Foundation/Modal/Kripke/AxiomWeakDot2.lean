import Foundation.Modal.Kripke.Completeness

namespace LO.Modal

namespace Kripke


section definability

open Formula.Kripke

variable {F : Kripke.Frame}

lemma weakConnected_of_validate_WeakDot2 (hCon : WeakConfluent F) : F ⊧ (Axioms.WeakDot2 (.atom 0) (.atom 1)) := by sorry

lemma validate_WeakDot2_of_weakConfluent : F ⊧ (Axioms.WeakDot2 (.atom 0) (.atom 1)) → WeakConfluent F := by sorry;

abbrev WeakConfluentFrameClass : FrameClass := { F | WeakConfluent F }

instance : WeakConfluentFrameClass.IsNonempty := by
  use ⟨Unit, λ _ _ => True⟩;
  simp [WeakConfluent];

instance WeakConfluentFrameClass.DefinedByWeakDot2 : WeakConfluentFrameClass.DefinedBy {Axioms.WeakDot2 (.atom 0) (.atom 1)} := ⟨by
  intro F;
  constructor;
  . simpa using weakConnected_of_validate_WeakDot2;
  . simpa using validate_WeakDot2_of_weakConfluent;
⟩

end definability


section canonicality

variable {S} [Entailment (Formula ℕ) S]
variable {𝓢 : S} [Entailment.Consistent 𝓢] [Entailment.K 𝓢]

open Formula.Kripke
open Entailment
open MaximalConsistentTableau
open canonicalModel

namespace Canonical

lemma weakConfluent [Entailment.HasAxiomWeakDot2 𝓢] : WeakConfluent (canonicalFrame 𝓢).Rel := by
  rintro x y z ⟨Rxy, Rxz, eyz⟩;
  have ⟨u, hu⟩ := lindenbaum (𝓢 := 𝓢) (t₀ := ⟨□''⁻¹y.1.1, ◇''⁻¹z.1.2⟩) $ by
    rintro Γ Δ hΓ hΔ;
    by_contra hC;
    replace hΓ : ∀ φ ∈ □'Γ, φ ∈ y.1.1 := by
      intro φ hφ;
      obtain ⟨ψ, hψ, rfl⟩ := List.exists_of_multibox hφ;
      exact hΓ _ hψ;
    have hγ : □(⋀Γ) ∈ y.1.1 := mdp_mem₁_provable collect_multibox_conj! $ iff_mem₁_conj.mpr hΓ
    generalize ⋀Γ = γ at hγ hC;

    replace hΔ : ∀ φ ∈ ◇'Δ, φ ∈ z.1.2 := by
      intro φ hφ;
      obtain ⟨ψ, hψ, rfl⟩ := List.exists_of_multidia hφ;
      exact hΔ _ hψ;
    have hδ : ◇(⋁Δ) ∈ z.1.2 := mdp_mem₂_provable distribute_dia_disj! $ iff_mem₂_disj.mpr hΔ;
    generalize ⋁Δ = δ at hδ hC;
    sorry;

  use u;
  constructor;
  . apply def_rel_box_mem₁.mpr;
    intro φ hφ;
    apply hu.1 hφ;
  . apply def_rel_dia_mem₂.mpr;
    intro φ hφ;
    apply hu.2 hφ;

end Canonical

end canonicality


end Kripke

end LO.Modal
