import Foundation.Modal.Kripke.Completeness
import Foundation.Vorspiel.Relation.Supplemental
import Foundation.Vorspiel.Relation.Iterate

section

open LO.Modal

def GeachConfluent (t : Axioms.Geach.Taple) (R : Rel α α) := ∀ ⦃x y z : α⦄, (R.iterate t.i x y) ∧ (R.iterate t.j x z) → ∃ u, (R.iterate t.m y u) ∧ (R.iterate t.n z u)

namespace GeachConfluent

variable {rel : Rel α α}

lemma serial_def : Serial rel ↔ (GeachConfluent ⟨0, 0, 1, 1⟩ rel) := by simp [GeachConfluent, Serial];

lemma reflexive_def : Reflexive rel ↔ (GeachConfluent ⟨0, 0, 1, 0⟩ rel) := by simp [GeachConfluent, Reflexive];

lemma symmetric_def : Symmetric rel ↔ (GeachConfluent ⟨0, 1, 0, 1⟩ rel) := by
  simp [GeachConfluent, Symmetric];
  constructor;
  . rintro h x y z rfl Rxz; exact h Rxz;
  . intro h x y Rxy; exact h rfl Rxy;

lemma transitive_def : Transitive rel ↔ (GeachConfluent ⟨0, 2, 1, 0⟩ rel) := by
  simp [GeachConfluent, Transitive];
  constructor;
  . rintro h x y z rfl w Rxw Rwz; exact h Rxw Rwz;
  . intro h x y z Rxy Ryz; exact h rfl y Rxy Ryz

lemma euclidean_def : Euclidean rel ↔ (GeachConfluent ⟨1, 1, 0, 1⟩ rel) := by simp [GeachConfluent, Euclidean];

lemma confluent_def : Confluent rel ↔ (GeachConfluent ⟨1, 1, 1, 1⟩ rel) := by simp [GeachConfluent, Confluent];

lemma coreflexive_def : Coreflexive rel ↔ (GeachConfluent ⟨0, 1, 0, 0⟩ rel) := by
  simp [GeachConfluent, Coreflexive];
  constructor;
  . rintro h x y z rfl Rxz; have := h Rxz; tauto;
  . intro h x y Rxy; have := h rfl Rxy; tauto;

lemma functional_def : Functional rel ↔ (GeachConfluent ⟨1, 1, 0, 0⟩ rel) := by
  simp [GeachConfluent, Functional];
  constructor <;> tauto;

lemma dense_def : Dense rel ↔ (GeachConfluent ⟨0, 1, 2, 0⟩ rel) := by
  simp [GeachConfluent, Dense];
  constructor;
  . rintro h x y z rfl Rxz; exact h Rxz;
  . intro h x y Rxy; exact h rfl Rxy;

@[simp]
lemma satisfies_eq : GeachConfluent (α := α) t (· = ·) := by simp [GeachConfluent];

end GeachConfluent


class IsGeachConfluent (g) (α) (R : Rel α α) where
  geachean : GeachConfluent g R

section

variable {rel : Rel α α}

instance [IsGeachConfluent ⟨0, 2, 1, 0⟩ _ rel] : IsTrans _ rel := ⟨by
  intro a b c Rab Rac;
  apply @GeachConfluent.transitive_def α rel |>.mpr IsGeachConfluent.geachean Rab Rac;
⟩
instance [IsTrans _ rel] : IsGeachConfluent ⟨0, 2, 1, 0⟩ _ rel := ⟨by
  apply @GeachConfluent.transitive_def α rel |>.mp;
  exact IsTrans.trans;
⟩


instance [IsGeachConfluent ⟨0, 0, 1, 0⟩ _ rel] : IsRefl _ rel := ⟨by
  intro a;
  apply @GeachConfluent.reflexive_def α rel |>.mpr IsGeachConfluent.geachean;
⟩

instance [IsRefl _ rel] : IsGeachConfluent ⟨0, 0, 1, 0⟩ _ rel := ⟨by
  apply @GeachConfluent.reflexive_def α rel |>.mp;
  exact IsRefl.refl;
⟩


instance [IsGeachConfluent ⟨0, 1, 0, 1⟩ _ rel] : IsSymm _ rel := ⟨by
  intro a b Rab;
  apply @GeachConfluent.symmetric_def α rel |>.mpr IsGeachConfluent.geachean;
  exact Rab;
⟩

instance [IsSymm _ rel] : IsGeachConfluent ⟨0, 1, 0, 1⟩ _ rel := ⟨by
  apply @GeachConfluent.symmetric_def α rel |>.mp;
  exact IsSymm.symm;
⟩


instance [IsGeachConfluent ⟨0, 0, 1, 1⟩ _ rel] : IsSerial _ rel := ⟨by
  intro a;
  apply @GeachConfluent.serial_def α rel |>.mpr IsGeachConfluent.geachean;
⟩

instance [IsSerial _ rel] : IsGeachConfluent ⟨0, 0, 1, 1⟩ _ rel := ⟨by
  apply @GeachConfluent.serial_def α rel |>.mp;
  exact IsSerial.serial;
⟩


instance [IsGeachConfluent ⟨1, 1, 0, 1⟩ _ rel] : IsEuclidean _ rel := ⟨by
  intro a b c Rab Rac;
  apply @GeachConfluent.euclidean_def α rel |>.mpr IsGeachConfluent.geachean Rab Rac;
⟩

instance [IsEuclidean _ rel] : IsGeachConfluent ⟨1, 1, 0, 1⟩ _ rel := ⟨by
  apply @GeachConfluent.euclidean_def α rel |>.mp;
  exact IsEuclidean.euclidean;
⟩


instance [IsGeachConfluent ⟨1, 1, 1, 1⟩ _ rel] : IsConfluent _ rel := ⟨by
  rintro a b c ⟨Rab, Rba⟩;
  apply @GeachConfluent.confluent_def α rel |>.mpr IsGeachConfluent.geachean;
  exact ⟨Rab, Rba⟩;
⟩

instance [IsConfluent _ rel] : IsGeachConfluent ⟨1, 1, 1, 1⟩ _ rel := ⟨by
  apply @GeachConfluent.confluent_def α rel |>.mp;
  exact IsConfluent.confluent;
⟩


instance [IsGeachConfluent ⟨0, 1, 0, 0⟩ _ rel] : IsCoreflexive _ rel := ⟨by
  intro a b Rab;
  apply @GeachConfluent.coreflexive_def α rel |>.mpr IsGeachConfluent.geachean;
  exact Rab;
⟩

instance [IsCoreflexive _ rel] : IsGeachConfluent ⟨0, 1, 0, 0⟩ _ rel := ⟨by
  apply @GeachConfluent.coreflexive_def α rel |>.mp;
  exact IsCoreflexive.coreflexive;
⟩

end

end



namespace LO.Modal

open LO.Modal.Entailment


namespace Kripke

instance whitepoint.instIsGeachConfluent : IsGeachConfluent g _ whitepoint.Rel := ⟨by
  rintro x y z ⟨Rxy, Rxz⟩;
  use ();
  constructor;
  . apply Rel.iterate.true_any; tauto;
  . apply Rel.iterate.true_any; tauto;
⟩

open Formula.Kripke



section definability

variable {F : Kripke.Frame} (g)

lemma validate_AxiomGeach_of_GeachConfluent [IsGeachConfluent g _ F.Rel] : F ⊧ (Axioms.Geach g (.atom 0)) := by
  rintro V x h;
  apply Satisfies.multibox_def.mpr;
  obtain ⟨y, Rxy, hbp⟩ := Satisfies.multidia_def.mp h;
  intro z Rxz;
  apply Satisfies.multidia_def.mpr;
  obtain ⟨u, Ryu, Rzu⟩ := IsGeachConfluent.geachean ⟨Rxy, Rxz⟩;
  use u;
  constructor;
  . assumption;
  . exact (Satisfies.multibox_def.mp hbp) Ryu;

section

lemma validate_AxiomT_of_reflexive [refl : IsRefl _ F] : F ⊧ (Axioms.T (.atom 0)) := validate_AxiomGeach_of_GeachConfluent ⟨0, 0, 1, 0⟩
lemma validate_AxiomD_of_serial [ser : IsSerial _ F.Rel] : F ⊧ (Axioms.D (.atom 0)) := validate_AxiomGeach_of_GeachConfluent ⟨0, 0, 1, 1⟩
lemma validate_AxiomB_of_symmetric [sym : IsSymm _ F.Rel] : F ⊧ (Axioms.B (.atom 0)) := validate_AxiomGeach_of_GeachConfluent ⟨0, 1, 0, 1⟩
lemma validate_AxiomFour_of_transitive [trans : IsTrans _ F] : F ⊧ (Axioms.Four (.atom 0)) := validate_AxiomGeach_of_GeachConfluent ⟨0, 2, 1, 0⟩
lemma validate_AxiomFive_of_euclidean [eucl : IsEuclidean _ F.Rel] : F ⊧ (Axioms.Five (.atom 0)) := validate_AxiomGeach_of_GeachConfluent ⟨1, 1, 0, 1⟩
lemma validate_AxiomPoint2_of_confluent [conf : IsConfluent _ F.Rel] : F ⊧ (Axioms.Point2 (.atom 0)) := validate_AxiomGeach_of_GeachConfluent ⟨1, 1, 1, 1⟩
lemma validate_AxiomTc_of_coreflexive [corefl : IsCoreflexive _ F.Rel] : F ⊧ (Axioms.Tc (.atom 0)) := validate_AxiomGeach_of_GeachConfluent ⟨0, 1, 0, 0⟩

end


lemma geachean_of_validate_AxiomGeach : F ⊧ (Axioms.Geach g (.atom 0)) → (GeachConfluent g) F.Rel := by
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

/-
instance FrameClass.multiGeachConfluent.definability (G) : (FrameClass.multiGeachConfluent G).DefinedBy (G.image (λ t => Axioms.Geach t (.atom 0))) := by
  unfold FrameClass.multiGeachConfluent MultiGeachConfluent Axioms.Geach;
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
  rw [GeachConfluent.reflexive_def];
  apply geachean_of_validate_AxiomGeach;
  exact h;

lemma transitive_of_validate_AxiomFour (h : F ⊧ (Axioms.Four (.atom 0))) : Transitive F.Rel := by
  rw [GeachConfluent.transitive_def];
  apply geachean_of_validate_AxiomGeach;
  exact h;

lemma euclidean_of_validate_AxiomFive (h : F ⊧ (Axioms.Five (.atom 0))) : Euclidean F.Rel := by
  rw [GeachConfluent.euclidean_def];
  apply geachean_of_validate_AxiomGeach;
  exact h;

lemma symmetric_of_validate_AxiomB (h : F ⊧ (Axioms.B (.atom 0))) : Symmetric F.Rel := by
  rw [GeachConfluent.symmetric_def];
  apply geachean_of_validate_AxiomGeach;
  exact h;

lemma serial_of_validate_AxiomD (h : F ⊧ (Axioms.D (.atom 0))) : Serial F.Rel := by
  rw [GeachConfluent.serial_def];
  apply geachean_of_validate_AxiomGeach;
  exact h;

lemma coreflexive_of_validate_AxiomTc (h : F ⊧ (Axioms.Tc (.atom 0))) : Coreflexive F.Rel := by
  rw [GeachConfluent.coreflexive_def];
  apply geachean_of_validate_AxiomGeach;
  exact h;

lemma confluent_of_validate_AxiomPoint2 (h : F ⊧ (Axioms.Point2 (.atom 0))) : Confluent F.Rel := by
  rw [GeachConfluent.confluent_def];
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

instance isGeachConfluent [Entailment.HasAxiomGeach g 𝓢] : IsGeachConfluent g _ (canonicalFrame 𝓢).Rel := ⟨by
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
