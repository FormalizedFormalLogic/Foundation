import Foundation.Modal.Kripke.Completeness

namespace LO


section

variable {S F : Type*} [BasicModalLogicalConnective F] [Entailment F S]
variable {𝓢 : S}

/--
  Axiom for Geach confluency.
-/
protected abbrev Axioms.Geach (g : Geachean.Taple) (φ : F) := ◇^[g.i](□^[g.m]φ) ➝ □^[g.j](◇^[g.n]φ)

namespace Entailment

class HasAxiomGeach (g) (𝓢 : S) where Geach (φ : F) : 𝓢 ⊢ Axioms.Geach g φ

variable {g} [HasAxiomGeach g 𝓢]

def axiomGeach : 𝓢 ⊢ ◇^[g.i](□^[g.m]φ) ➝ □^[g.j](◇^[g.n]φ) := HasAxiomGeach.Geach _
@[simp] lemma axiomGeach! : 𝓢 ⊢! ◇^[g.i](□^[g.m]φ) ➝ □^[g.j](◇^[g.n]φ) := ⟨axiomGeach⟩

instance [Entailment.HasAxiomT 𝓢] : Entailment.HasAxiomGeach ⟨0, 0, 1, 0⟩ 𝓢 := ⟨fun _ => axiomT⟩
instance [Entailment.HasAxiomB 𝓢] : Entailment.HasAxiomGeach ⟨0, 1, 0, 1⟩ 𝓢 := ⟨fun _ => axiomB⟩
instance [Entailment.HasAxiomD 𝓢] : Entailment.HasAxiomGeach ⟨0, 0, 1, 1⟩ 𝓢 := ⟨fun _ => axiomD⟩
instance [Entailment.HasAxiomFour 𝓢] : Entailment.HasAxiomGeach ⟨0, 2, 1, 0⟩ 𝓢 := ⟨fun _ => axiomFour⟩
instance [Entailment.HasAxiomFive 𝓢] : Entailment.HasAxiomGeach ⟨1, 1, 0, 1⟩ 𝓢 := ⟨fun _ => axiomFive⟩
instance [Entailment.HasAxiomTc 𝓢] : Entailment.HasAxiomGeach ⟨0, 1, 0, 0⟩ 𝓢 := ⟨fun _ => axiomTc⟩
instance [Entailment.HasAxiomPoint2 𝓢] : Entailment.HasAxiomGeach ⟨1, 1, 1, 1⟩ 𝓢 := ⟨fun _ => axiomPoint2⟩

end Entailment

end


namespace Modal

namespace Kripke

instance whitepoint.instIsGeachean : IsGeachean g _ whitepoint.Rel := ⟨by
  rintro x y z ⟨Rxy, Rxz⟩;
  use ();
  constructor;
  . apply Rel.iterate.true_any; tauto;
  . apply Rel.iterate.true_any; tauto;
⟩

instance : IsRefl _ whitepoint.Rel := by
  have := whitepoint.instIsGeachean (g := ⟨0, 0, 1, 0⟩);
  infer_instance;

instance : IsTrans _ whitepoint.Rel := by
  have := whitepoint.instIsGeachean (g := ⟨0, 2, 1, 0⟩);
  infer_instance;

open Formula.Kripke

protected abbrev FrameClass.multiGeachean (G : Set Geachean.Taple) : FrameClass := { F | (MultiGeachean G) F.Rel }


section definability

variable {F : Kripke.Frame} {g : Geachean.Taple}

lemma validate_AxiomGeach_of_Geachean [IsGeachean g _ F.Rel] : F ⊧ (Axioms.Geach g (.atom 0)) := by
  rintro V x h;
  apply Satisfies.multibox_def.mpr;
  obtain ⟨y, Rxy, hbp⟩ := Satisfies.multidia_def.mp h;
  intro z Rxz;
  apply Satisfies.multidia_def.mpr;
  obtain ⟨u, Ryu, Rzu⟩ := IsGeachean.geachean ⟨Rxy, Rxz⟩;
  use u;
  constructor;
  . assumption;
  . exact (Satisfies.multibox_def.mp hbp) Ryu;

section

lemma validate_AxiomT_of_reflexive [refl : IsRefl _ F] : F ⊧ (Axioms.T (.atom 0)) := by
  exact validate_AxiomGeach_of_Geachean (g := ⟨0, 0, 1, 0⟩);

lemma validate_AxiomFour_of_transitive [trans : IsTrans _ F] : F ⊧ (Axioms.Four (.atom 0)) := by
  exact validate_AxiomGeach_of_Geachean (g := ⟨0, 2, 1, 0⟩);

/-
lemma validate_AxiomT_of_reflexive (h : Reflexive F.Rel) : F ⊧ (Axioms.T (.atom 0)) := by
  rw [Geachean.reflexive_def] at h;
  exact validate_AxiomGeach_of_Geachean h;

lemma validate_AxiomFour_of_transitive (h : Transitive F.Rel) : F ⊧ (Axioms.Four (.atom 0)) := by
  rw [Geachean.transitive_def] at h;
  exact validate_AxiomGeach_of_Geachean h;

lemma validate_AxiomD_of_serial (h : Serial F.Rel) : F ⊧ (Axioms.D (.atom 0)) := by
  rw [Geachean.serial_def] at h;
  exact validate_AxiomGeach_of_Geachean h;

lemma validate_AxiomFive_of_euclidean (h : Euclidean F.Rel) : F ⊧ (Axioms.Five (.atom 0)) := by
  rw [Geachean.euclidean_def] at h;
  exact validate_AxiomGeach_of_Geachean h;

lemma validate_AxiomB_of_symmetric (h : Symmetric F.Rel) : F ⊧ (Axioms.B (.atom 0)) := by
  rw [Geachean.symmetric_def] at h;
  exact validate_AxiomGeach_of_Geachean h;

lemma validate_AxiomPoint2_of_confluent (h : Confluent F.Rel) : F ⊧ (Axioms.Point2 (.atom 0)) := by
  rw [Geachean.confluent_def] at h;
  exact validate_AxiomGeach_of_Geachean h;

lemma validate_AxiomTc_of_coreflexive (h : Coreflexive F.Rel) : F ⊧ (Axioms.Tc (.atom 0)) := by
  rw [Geachean.coreflexive_def] at h;
  exact validate_AxiomGeach_of_Geachean h;
-/

end


lemma geachean_of_validate_AxiomGeach : F ⊧ (Axioms.Geach g (.atom 0)) → (Geachean g) F.Rel := by
  rintro h x y z ⟨Rxy, Rxz⟩;
  let V : Kripke.Valuation F := λ v _ => y ≺^[g.m] v;
  have : Satisfies ⟨F, V⟩ x (◇^[g.i](□^[g.m](.atom 0))) := by
    apply Satisfies.multidia_def.mpr;
    use y;
    constructor;
    . assumption;
    . apply Satisfies.multibox_def.mpr;
      aesop;
  have : Satisfies ⟨F, V⟩ x (□^[g.j](◇^[g.n]Formula.atom 0)) := h V x this;
  have : Satisfies ⟨F, V⟩ z (◇^[g.n]Formula.atom 0) := Satisfies.multibox_def.mp this Rxz;
  obtain ⟨u, Rzu, Ryu⟩ := Satisfies.multidia_def.mp this;
  exact ⟨u, Ryu, Rzu⟩;

namespace FrameClass.multiGeachean

@[simp]
lemma nonempty : (FrameClass.multiGeachean G).Nonempty := by
  use whitepoint;
  intros t ht x y z h;
  use x;
  constructor <;> { apply Rel.iterate.true_any; tauto; }

end FrameClass.multiGeachean

/-
instance FrameClass.multiGeachean.definability (G) : (FrameClass.multiGeachean G).DefinedBy (G.image (λ t => Axioms.Geach t (.atom 0))) := by
  unfold FrameClass.multiGeachean MultiGeachean Axioms.Geach;
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
-/

section

variable {F : Frame}

lemma reflexive_of_validate_AxiomT (h : F ⊧ (Axioms.T (.atom 0))) : Reflexive F.Rel := by
  rw [Geachean.reflexive_def];
  apply geachean_of_validate_AxiomGeach;
  exact h;

lemma transitive_of_validate_AxiomFour (h : F ⊧ (Axioms.Four (.atom 0))) : Transitive F.Rel := by
  rw [Geachean.transitive_def];
  apply geachean_of_validate_AxiomGeach;
  exact h;

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

protected lemma geachean [Entailment.HasAxiomGeach g 𝓢] : IsGeachean g _ (canonicalFrame 𝓢).Rel := ⟨by
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
    have : □^[g.j](◇^[g.n]δ) ∈ x.1.1 := mdp_mem₁_provable axiomGeach! this;
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
⟩

protected lemma transitive [Entailment.HasAxiomFour 𝓢] : IsTrans _ (canonicalFrame 𝓢).Rel := by
  have := Canonical.geachean (𝓢 := 𝓢) (g := ⟨0, 2, 1, 0⟩);
  infer_instance;

protected lemma reflexive [Entailment.HasAxiomT 𝓢] : IsRefl _ (canonicalFrame 𝓢).Rel := by
  have := Canonical.geachean (𝓢 := 𝓢) (g := ⟨0, 0, 1, 0⟩);
  infer_instance;


/-
protected lemma reflexive [Entailment.HasAxiomT 𝓢] : IsRefl _ (canonicalFrame 𝓢).Rel := ⟨by
  have := @Canonical.geachean (g := ⟨0, 0, 1, 0⟩);
  rw [←Geachean.reflexive_def] at this;
  apply Canonical.geachean;
  intro x;
  simp [axiomT!];
⟩
-/

/-
protected lemma transitive [Entailment.HasAxiomFour 𝓢] : Transitive (canonicalFrame 𝓢).Rel := by
  rw [Geachean.transitive_def]; apply Canonical.geachean; simp [axiomFour!];

protected lemma euclidean [Entailment.HasAxiomFive 𝓢] : Euclidean (canonicalFrame 𝓢).Rel := by
  rw [Geachean.euclidean_def]; apply Canonical.geachean; simp [axiomFive!];

protected lemma serial [Entailment.HasAxiomD 𝓢] : Serial (canonicalFrame 𝓢).Rel := by
  rw [Geachean.serial_def]; apply Canonical.geachean; simp [axiomD!];

protected lemma symmetric [Entailment.HasAxiomB 𝓢] : Symmetric (canonicalFrame 𝓢).Rel := by
  rw [Geachean.symmetric_def]; apply Canonical.geachean; simp [axiomB!];

protected lemma coreflexive [Entailment.HasAxiomTc 𝓢] : Coreflexive (canonicalFrame 𝓢).Rel := by
  rw [Geachean.coreflexive_def]; apply Canonical.geachean; simp [axiomTc!];

protected lemma confluent [Entailment.HasAxiomPoint2 𝓢] : Confluent (canonicalFrame 𝓢).Rel := by
  rw [Geachean.confluent_def]; apply Canonical.geachean; simp [axiomPoint2!];
-/

end Canonical

end canonicality


end Kripke

end LO.Modal
