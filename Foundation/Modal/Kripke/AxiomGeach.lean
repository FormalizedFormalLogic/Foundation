import Foundation.Modal.Kripke.Completeness
import Foundation.Vorspiel.Relation.Supplemental
import Foundation.Modal.Geachean

namespace LO.Modal

open LO.Modal.Entailment

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

instance [Entailment.HasAxiomT 𝓢]      : Entailment.HasAxiomGeach ⟨0, 0, 1, 0⟩ 𝓢 := ⟨fun _ => axiomT⟩
instance [Entailment.HasAxiomB 𝓢]      : Entailment.HasAxiomGeach ⟨0, 1, 0, 1⟩ 𝓢 := ⟨fun _ => axiomB⟩
instance [Entailment.HasAxiomD 𝓢]      : Entailment.HasAxiomGeach ⟨0, 0, 1, 1⟩ 𝓢 := ⟨fun _ => axiomD⟩
instance [Entailment.HasAxiomFour 𝓢]   : Entailment.HasAxiomGeach ⟨0, 2, 1, 0⟩ 𝓢 := ⟨fun _ => axiomFour⟩
instance [Entailment.HasAxiomFive 𝓢]   : Entailment.HasAxiomGeach ⟨1, 1, 0, 1⟩ 𝓢 := ⟨fun _ => axiomFive⟩
instance [Entailment.HasAxiomTc 𝓢]     : Entailment.HasAxiomGeach ⟨0, 1, 0, 0⟩ 𝓢 := ⟨fun _ => axiomTc⟩
instance [Entailment.HasAxiomPoint2 𝓢] : Entailment.HasAxiomGeach ⟨1, 1, 1, 1⟩ 𝓢 := ⟨fun _ => axiomPoint2⟩

end Entailment


namespace Kripke

instance whitepoint.instIsGeachean (g) : IsGeachean g _ whitepoint.Rel := ⟨by
  rintro x y z ⟨Rxy, Rxz⟩;
  use ();
  constructor;
  . apply Rel.iterate.true_any; tauto;
  . apply Rel.iterate.true_any; tauto;
⟩

open Formula.Kripke


protected abbrev FrameClass.multiGeachean (G : Set Geachean.Taple) : FrameClass := { F | (MultiGeachean G) F.Rel }


section definability

variable {F : Kripke.Frame} (g : Geachean.Taple)

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

lemma validate_AxiomT_of_reflexive [refl : IsRefl _ F] : F ⊧ (Axioms.T (.atom 0)) := validate_AxiomGeach_of_Geachean ⟨0, 0, 1, 0⟩
lemma validate_AxiomD_of_serial [ser : IsSerial _ F.Rel] : F ⊧ (Axioms.D (.atom 0)) := validate_AxiomGeach_of_Geachean ⟨0, 0, 1, 1⟩
lemma validate_AxiomB_of_symmetric [sym : IsSymm _ F.Rel] : F ⊧ (Axioms.B (.atom 0)) := validate_AxiomGeach_of_Geachean ⟨0, 1, 0, 1⟩
lemma validate_AxiomFour_of_transitive [trans : IsTrans _ F] : F ⊧ (Axioms.Four (.atom 0)) := validate_AxiomGeach_of_Geachean ⟨0, 2, 1, 0⟩
lemma validate_AxiomFive_of_euclidean [eucl : IsEuclidean _ F.Rel] : F ⊧ (Axioms.Five (.atom 0)) := validate_AxiomGeach_of_Geachean ⟨1, 1, 0, 1⟩
lemma validate_AxiomPoint2_of_confluent [conf : IsConfluent _ F.Rel] : F ⊧ (Axioms.Point2 (.atom 0)) := validate_AxiomGeach_of_Geachean ⟨1, 1, 1, 1⟩
lemma validate_AxiomTc_of_coreflexive [corefl : IsCoreflexive _ F.Rel] : F ⊧ (Axioms.Tc (.atom 0)) := validate_AxiomGeach_of_Geachean ⟨0, 1, 0, 0⟩

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

lemma euclidean_of_validate_AxiomFive (h : F ⊧ (Axioms.Five (.atom 0))) : Euclidean F.Rel := by
  rw [Geachean.euclidean_def];
  apply geachean_of_validate_AxiomGeach;
  exact h;

lemma symmetric_of_validate_AxiomB (h : F ⊧ (Axioms.B (.atom 0))) : Symmetric F.Rel := by
  rw [Geachean.symmetric_def];
  apply geachean_of_validate_AxiomGeach;
  exact h;

lemma serial_of_validate_AxiomD (h : F ⊧ (Axioms.D (.atom 0))) : Serial F.Rel := by
  rw [Geachean.serial_def];
  apply geachean_of_validate_AxiomGeach;
  exact h;

lemma coreflexive_of_validate_AxiomTc (h : F ⊧ (Axioms.Tc (.atom 0))) : Coreflexive F.Rel := by
  rw [Geachean.coreflexive_def];
  apply geachean_of_validate_AxiomGeach;
  exact h;

lemma confluent_of_validate_AxiomPoint2 (h : F ⊧ (Axioms.Point2 (.atom 0))) : Confluent F.Rel := by
  rw [Geachean.confluent_def];
  apply geachean_of_validate_AxiomGeach;
  exact h;

end

end definability


section canonicality

variable [Entailment (Formula ℕ) S]
variable {𝓢 : S} [Entailment.Consistent 𝓢] [Entailment.K 𝓢]

open Formula.Kripke
open Entailment
open MaximalConsistentTableau
open canonicalModel

namespace Canonical

instance [Entailment.HasAxiomGeach g 𝓢] : IsGeachean g _ (canonicalFrame 𝓢).Rel := ⟨by
  rintro x y z ⟨Rxy, Rxz⟩;
  have ⟨u, hu⟩ := lindenbaum (𝓢 := 𝓢) (t₀ := ⟨y.1.1.premultibox g.m, z.1.2.premultidia g.n⟩) $ by
    rintro Γ Δ hΓ hΔ;
    by_contra! hC;
    have hγ : □^[g.m](Γ.conj) ∈ y.1.1 := y.mdp_mem₁_provable collect_multibox_fconj! $ iff_mem₁_fconj.mpr (by simpa using hΓ);
    have hδ : ◇^[g.n](Δ.disj) ∈ z.1.2 := mdp_mem₂_provable distribute_multidia_fdisj! $ iff_mem₂_fdisj.mpr (by simpa using hΔ);
    generalize Γ.conj = γ at hγ hC;
    generalize Δ.disj = δ at hδ hC;
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

instance isTrans [Entailment.HasAxiomFour 𝓢] : IsTrans _ (canonicalFrame 𝓢).Rel := inferInstance
instance [Entailment.HasAxiomT 𝓢] : IsRefl _ (canonicalFrame 𝓢).Rel := inferInstance
instance [Entailment.HasAxiomFive 𝓢] : IsEuclidean _ (canonicalFrame 𝓢).Rel := inferInstance
instance [Entailment.HasAxiomD 𝓢] : IsSerial _ (canonicalFrame 𝓢).Rel := inferInstance
instance [Entailment.HasAxiomB 𝓢] : IsSymm _ (canonicalFrame 𝓢).Rel := inferInstance
instance [Entailment.HasAxiomTc 𝓢] : IsCoreflexive _ (canonicalFrame 𝓢).Rel := inferInstance
instance [Entailment.HasAxiomPoint2 𝓢] : IsConfluent _ (canonicalFrame 𝓢).Rel := inferInstance
instance [Entailment.HasAxiomT 𝓢] [Entailment.HasAxiomFour 𝓢] : IsPreorder _ (canonicalFrame 𝓢).Rel where
instance [Entailment.HasAxiomT 𝓢] [Entailment.HasAxiomFour 𝓢] [Entailment.HasAxiomB 𝓢] : IsEquiv _ (canonicalFrame 𝓢).Rel where

end Canonical

end canonicality


end Kripke

end LO.Modal
