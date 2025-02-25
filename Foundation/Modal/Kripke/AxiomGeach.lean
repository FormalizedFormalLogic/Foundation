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
    replace hΓ : ∀ φ ∈ Γ, □^[g.m]φ ∈ y.1.1 := by simpa using hΓ;
    replace hΔ : ∀ φ ∈ Δ, ◇^[g.n]φ ∈ z.1.2 := by simpa using hΔ;
    have : ⋀□'^[g.m]Γ ∈ y.1.1 := by
      sorry;
    have : ⋁◇'^[g.n]Δ ∈ z.1.2 := by
      sorry;
    have : □^[g.m]⋀Γ ∈ y.1.1 := by sorry;
    have : ◇^[g.n]⋀Δ ∈ y.1.1 := by sorry;
    obtain ⟨γ, δ, hγ, hδ, hC⟩ : ∃ γ δ, □^[g.m]γ ∈ y.1.1 ∧ ◇^[g.n]δ ∈ z.1.2 ∧ 𝓢 ⊢! γ ➝ δ := by
      sorry;
    have : 𝓢 ⊢! □^[g.m]γ ➝ □^[g.m]δ := imply_multibox_distribute'! hC;
    have : □^[g.m]δ ∈ y.1.1 := mdp_mem₁Aux this hγ;
    have : ◇^[g.i](□^[g.m]δ) ∈ x.1.1 := def_multirel_multidia_mem₁.mp Rxy this;
    have : □^[g.j](◇^[g.n]δ) ∈ x.1.1 := mdp_mem₁Aux hG this;
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
