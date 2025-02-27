import Foundation.Modal.Kripke.Completeness2

namespace LO.Modal

namespace Kripke

variable {S} [Entailment (Formula ℕ) S]
variable {𝓢 : S} [Entailment.Consistent 𝓢] [Entailment.K 𝓢]

open Formula.Kripke
open Entailment
open MaximalConsistentTableau
open canonicalModel

lemma geachean_canonicalFrame_of_provable_geach_axiom
  (hG : ∀ {φ}, 𝓢 ⊢! ◇^[g.i](□^[g.m]φ) ➝ □^[g.j](◇^[g.n]φ))
  : Geachean g (canonicalFrame 𝓢).Rel := by
  rintro x y z ⟨Rxy, Rxz⟩;
  have ⟨u, hu⟩ := lindenbaum (𝓢 := 𝓢) (t₀ := ⟨□''⁻¹^[g.m]y.1.1, ◇''⁻¹^[g.n]z.1.2⟩) $ by
    rintro Γ Δ hΓ hΔ;
    by_contra hC;

    replace hΓ : ∀ φ ∈ □'^[g.m]Γ, φ ∈ y.1.1 := by
      intro φ hφ;
      obtain ⟨ψ, hψ, rfl⟩ := by simpa using hφ;
      exact hΓ _ hψ;
    have hγ : □^[g.m](⋀Γ) ∈ y.1.1 := mdp_mem₁_provable collect_multibox_conj! $ iff_mem₁_conj.mpr hΓ
    generalize ⋀Γ = γ at hγ hC;

    replace hΔ : ∀ φ ∈ ◇'^[g.n]Δ, φ ∈ z.1.2 := by
      intro φ hφ;
      obtain ⟨ψ, hψ, rfl⟩ := by simpa using hφ;
      exact hΔ _ hψ;
    have hδ : ◇^[g.n](⋁Δ) ∈ z.1.2 := mdp_mem₂_provable collect_multidia_disj! $ iff_mem₂_disj.mpr hΔ;
    generalize ⋁Δ = δ at hδ hC;

    have : 𝓢 ⊢! □^[g.m]γ ➝ □^[g.m]δ := imply_multibox_distribute'! hC;
    have : □^[g.m]δ ∈ y.1.1 := mdp_mem₁_provable this hγ;
    have : ◇^[g.i](□^[g.m]δ) ∈ x.1.1 := def_multirel_multidia_mem₁.mp Rxy this;
    have : □^[g.j](◇^[g.n]δ) ∈ x.1.1 := mdp_mem₁_provable hG this;
    have : ◇^[g.n]δ ∈ z.1.1 := def_multirel_multibox_mem₁.mp Rxz this;
    have : ◇^[g.n]δ ∉ z.1.2 := iff_not_mem₂_mem₁.mpr this;
    contradiction;
  use u;
  constructor;
  . apply def_multirel_multibox_mem₁.mpr;
    intro φ hφ;
    exact hu.1 hφ;
  . apply def_multirel_multidia_mem₂.mpr;
    intro φ hφ;
    exact hu.2 hφ;

end Kripke

end LO.Modal
