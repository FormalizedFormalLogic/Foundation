import Foundation.Modal.Kripke.Completeness

namespace LO.Modal

namespace Kripke


section definability

open Formula.Kripke

abbrev MultiGeacheanConfluentFrameClass (G : Set Geachean.Taple) : FrameClass := { F | (MultiGeachean G) F.Rel }

instance : (MultiGeacheanConfluentFrameClass G).IsNonempty := by
  use ⟨Unit, λ _ _ => True⟩;
  intros t ht x y z h;
  use x;
  constructor <;> { apply Rel.iterate.true_any; tauto; }

instance MultiGeacheanFrameClass.isDefinedByGeachAxioms (G) : (MultiGeacheanConfluentFrameClass G).DefinedBy (G.image (λ t => Axioms.Geach t (.atom 0))) := by
  unfold MultiGeacheanConfluentFrameClass MultiGeachean Axioms.Geach;
  constructor;
  intro F;
  constructor;
  . rintro hF φ ⟨g, ⟨hg, rfl⟩⟩ V x h;
    obtain ⟨y, Rxy, hbp⟩ := Satisfies.multidia_def.mp h;
    apply Satisfies.multibox_def.mpr;
    intro z Rxz;
    apply Satisfies.multidia_def.mpr;
    obtain ⟨u, Ryu, Rzu⟩ := hF g hg ⟨Rxy, Rxz⟩;
    use u;
    constructor;
    . assumption;
    . exact (Satisfies.multibox_def.mp hbp) Ryu;
  . rintro h g hg x y z ⟨Rxy, Rxz⟩;
    let V : Kripke.Valuation F := λ v _ => y ≺^[g.m] v;
    have : Satisfies ⟨F, V⟩ x (◇^[g.i](□^[g.m](.atom 0))) := by
      apply Satisfies.multidia_def.mpr;
      use y;
      constructor;
      . assumption;
      . apply Satisfies.multibox_def.mpr;
        aesop;
    have : Satisfies ⟨F, V⟩ x (□^[g.j](◇^[g.n]Formula.atom 0)) := h (Axioms.Geach g (.atom 0)) (by tauto) V x this;
    have : Satisfies ⟨F, V⟩ z (◇^[g.n]Formula.atom 0) := Satisfies.multibox_def.mp this Rxz;
    obtain ⟨u, Rzu, Ryu⟩ := Satisfies.multidia_def.mp this;
    exact ⟨u, Ryu, Rzu⟩;


section

variable {F : Frame}

lemma reflexive_of_validate_AxiomT (h : F ⊧ (Axioms.T (.atom 0))) : Reflexive F.Rel := by
  have : ValidOnFrame F (Axioms.T (.atom 0)) → Reflexive F.Rel := by
    simpa [Axioms.Geach, MultiGeachean, ←Geachean.reflexive_def] using
    MultiGeacheanFrameClass.isDefinedByGeachAxioms {⟨0, 0, 1, 0⟩} |>.defines F |>.mpr;
  exact this h;

lemma transitive_of_validate_AxiomFour (h : F ⊧ (Axioms.Four (.atom 0))) : Transitive F.Rel := by
  have : ValidOnFrame F (Axioms.Four (.atom 0)) → Transitive F.Rel := by
    simpa [Axioms.Geach, MultiGeachean, ←Geachean.transitive_def] using
    MultiGeacheanFrameClass.isDefinedByGeachAxioms {⟨0, 2, 1, 0⟩} |>.defines F |>.mpr;
  exact this h;

end

end definability


section canonicality

variable {S} [Entailment (Formula ℕ) S]
variable {𝓢 : S} [Entailment.Consistent 𝓢] [Entailment.K 𝓢]

open Formula.Kripke
open Entailment
open MaximalConsistentTableau
open canonicalModel

namespace Canonical

lemma geachean
  (hG : ∀ {φ}, 𝓢 ⊢! ◇^[g.i](□^[g.m]φ) ➝ □^[g.j](◇^[g.n]φ))
  : Geachean g (canonicalFrame 𝓢).Rel := by
  rintro x y z ⟨Rxy, Rxz⟩;
  have ⟨u, hu⟩ := lindenbaum (𝓢 := 𝓢) (t₀ := ⟨□''⁻¹^[g.m]y.1.1, ◇''⁻¹^[g.n]z.1.2⟩) $ by
    rintro Γ Δ hΓ hΔ;
    by_contra hC;

    replace hΓ : ∀ φ ∈ □'^[g.m]Γ, φ ∈ y.1.1 := by
      intro φ hφ;
      obtain ⟨ψ, hψ, rfl⟩ := List.exists_of_multibox hφ;
      exact hΓ _ hψ;
    have hγ : □^[g.m](⋀Γ) ∈ y.1.1 := mdp_mem₁_provable collect_multibox_conj! $ iff_mem₁_conj.mpr hΓ
    generalize ⋀Γ = γ at hγ hC;

    replace hΔ : ∀ φ ∈ ◇'^[g.n]Δ, φ ∈ z.1.2 := by
      intro φ hφ;
      obtain ⟨ψ, hψ, rfl⟩ := List.exists_of_multidia hφ;
      exact hΔ _ hψ;
    have hδ : ◇^[g.n](⋁Δ) ∈ z.1.2 := mdp_mem₂_provable distribute_multidia_disj! $ iff_mem₂_disj.mpr hΔ;
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

lemma reflexive [Entailment.HasAxiomT 𝓢] : Reflexive (canonicalFrame 𝓢).Rel := by
  rw [Geachean.reflexive_def]; apply geachean; simp [axiomT!];

lemma transitive [Entailment.HasAxiomFour 𝓢] : Transitive (canonicalFrame 𝓢).Rel := by
  rw [Geachean.transitive_def]; apply geachean; simp [axiomFour!];

lemma euclidean [Entailment.HasAxiomFive 𝓢] : Euclidean (canonicalFrame 𝓢).Rel := by
  rw [Geachean.euclidean_def]; apply geachean; simp [axiomFive!];

lemma serial [Entailment.HasAxiomD 𝓢] : Serial (canonicalFrame 𝓢).Rel := by
  rw [Geachean.serial_def]; apply geachean; simp [axiomD!];

lemma symmetric [Entailment.HasAxiomB 𝓢] : Symmetric (canonicalFrame 𝓢).Rel := by
  rw [Geachean.symmetric_def]; apply geachean; simp [axiomB!];

lemma coreflexive [Entailment.HasAxiomTc 𝓢] : Coreflexive (canonicalFrame 𝓢).Rel := by
  rw [Geachean.coreflexive_def]; apply geachean; simp [axiomTc!];

lemma confluent [Entailment.HasAxiomPoint2 𝓢] : Confluent (canonicalFrame 𝓢).Rel := by
  rw [Geachean.confluent_def]; apply geachean; simp [axiomPoint2!];

end Canonical

end canonicality


end Kripke

end LO.Modal
