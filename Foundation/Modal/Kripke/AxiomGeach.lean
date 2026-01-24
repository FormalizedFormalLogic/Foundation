import Foundation.Modal.Kripke.Completeness
import Foundation.Vorspiel.Rel.Euclidean
import Foundation.Vorspiel.Rel.Coreflexive
import Foundation.Vorspiel.Rel.Convergent

namespace LO.Modal

namespace Kripke

variable {F : Frame}

namespace Frame

class IsGeachConvergent (F : Frame) (g : Axioms.Geach.Taple) where
  gconv : ∀ ⦃x y z : F⦄, x ≺^[g.i] y → x ≺^[g.j] z → ∃ u, y ≺^[g.m] u ∧ z ≺^[g.n] u


protected abbrev IsReflexive (F : Frame) := _root_.Std.Refl F

@[simp] lemma refl [F.IsReflexive] : ∀ {x : F.World}, x ≺ x := by apply Std.Refl.refl

@[simp]
instance [F.IsGeachConvergent ⟨0, 0, 1, 0⟩] : F.IsReflexive where
  refl := by simpa using IsGeachConvergent.gconv (F := F) (g := ⟨0, 0, 1, 0⟩);
instance [F.IsReflexive] : F.IsGeachConvergent ⟨0, 0, 1, 0⟩ where
  gconv x y z Rxy Rxz := by simp_all;

protected abbrev IsSerial (F : Frame) := _root_.IsSerial F.Rel

lemma serial [F.IsSerial] : ∀ x : F, ∃ y, x ≺ y := IsSerial.serial

@[simp]
instance [F.IsGeachConvergent ⟨0, 0, 1, 1⟩] : F.IsSerial where
  serial := by simpa using IsGeachConvergent.gconv (F := F) (g := ⟨0, 0, 1, 1⟩);
instance [F.IsSerial] : F.IsGeachConvergent ⟨0, 0, 1, 1⟩ where
  gconv x y z Rxy Rxz := by
    simp_all only [Rel.Iterate.iff_zero, Rel.Iterate.iff_succ, exists_eq_right, and_self];
    subst Rxz;
    apply _root_.IsSerial.serial


protected abbrev IsTransitive (F : Frame) := _root_.IsTrans _ F.Rel

lemma trans [F.IsTransitive] : ∀ {x y z : F.World}, x ≺ y → y ≺ z → x ≺ z := by apply IsTrans.trans

@[simp]
instance [F.IsGeachConvergent ⟨0, 2, 1, 0⟩] : F.IsTransitive where
  trans := by
    rintro x y z;
    have : ∀ x y z : F, x = y → ∀ (u : F.World), x ≺ u → u ≺ z → y ≺ z := by
      simpa using IsGeachConvergent.gconv (F := F) (g := ⟨0, 2, 1, 0⟩);
    apply this x x z rfl y;
instance [F.IsTransitive] : F.IsGeachConvergent ⟨0, 2, 1, 0⟩ where
  gconv x y z Rxy Rxz := by
    simp_all only [Rel.Iterate.iff_zero, Rel.Iterate.iff_succ, exists_eq_right, exists_eq_right'];
    subst Rxy;
    obtain ⟨y, Rxy, Ryz⟩ := Rxz;
    exact IsTrans.trans _ _ _ Rxy Ryz


protected abbrev IsSymmetric (F : Frame) := _root_.Std.Symm F.Rel

lemma symm [F.IsSymmetric] : ∀ {x y : F.World}, x ≺ y → y ≺ x := by apply Std.Symm.symm

@[simp]
instance [F.IsGeachConvergent ⟨0, 1, 0, 1⟩] : F.IsSymmetric where
  symm x y := by
    have : ∀ x y z : F, x = y → x ≺ z → z ≺ y := by
      simpa using IsGeachConvergent.gconv (g := ⟨0, 1, 0, 1⟩) (F := F);
    apply @this x x y rfl;
instance [F.IsSymmetric] : F.IsGeachConvergent ⟨0, 1, 0, 1⟩ where
  gconv x y z Rxy Rxz := by
    simp_all only [Rel.Iterate.iff_zero, Rel.Iterate.iff_succ, exists_eq_right, exists_eq_left'];
    subst Rxy;
    exact _root_.Std.Symm.symm _ _ Rxz;


protected abbrev IsEuclidean (F : Frame) := _root_.IsRightEuclidean F.Rel

lemma eucl [F.IsEuclidean] : ∀ {x y z : F.World}, x ≺ y → x ≺ z → y ≺ z := by apply IsRightEuclidean.reucl

@[simp]
instance [F.IsGeachConvergent ⟨1, 1, 0, 1⟩] : F.IsEuclidean where
  reucl x y z Rxy Rxz := by
    have : ∀ x y z : F, x ≺ y → x ≺ z → z ≺ y := by
      simpa using IsGeachConvergent.gconv (F := F) (g := ⟨1, 1, 0, 1⟩);
    apply this x z y Rxz Rxy;
instance [F.IsEuclidean] : F.IsGeachConvergent ⟨1, 1, 0, 1⟩ where
  gconv x y z Rxy Rxz := by
    simp_all only [Rel.Iterate.iff_succ, Rel.Iterate.iff_zero, exists_eq_right, exists_eq_left'];
    exact IsRightEuclidean.reucl Rxz Rxy


protected abbrev IsPiecewiseStronglyConvergent (F : Frame) := _root_.IsPiecewiseStronglyConvergent F.Rel

lemma ps_convergent [F.IsPiecewiseStronglyConvergent] : ∀ {x y z : F.World}, x ≺ y → x ≺ z → ∃ u, y ≺ u ∧ z ≺ u := by
  apply IsPiecewiseStronglyConvergent.ps_convergent

@[simp]
instance [F.IsGeachConvergent ⟨1, 1, 1, 1⟩] : F.IsPiecewiseStronglyConvergent where
  ps_convergent := by simpa using IsGeachConvergent.gconv (g := ⟨1, 1, 1, 1⟩) (F := F);
instance [F.IsPiecewiseStronglyConvergent] : F.IsGeachConvergent ⟨1, 1, 1, 1⟩ where
  gconv x y z Rxy Rxz := by
    simp_all only [Rel.Iterate.iff_succ, Rel.Iterate.iff_zero, exists_eq_right];
    obtain ⟨u, Ryu, Rzu⟩ := IsPiecewiseStronglyConvergent.ps_convergent Rxy Rxz;
    use u;


protected abbrev IsCoreflexive (F : Frame) := _root_.IsCoreflexive F.Rel

lemma corefl [F.IsCoreflexive] : ∀ {x y : F.World}, x ≺ y → x = y := by apply IsCoreflexive.corefl

@[simp]
instance [F.IsGeachConvergent ⟨0, 1, 0, 0⟩] : F.IsCoreflexive where
  corefl x y Rxy := by
    have : ∀ x y z : F, x = y → x ≺ z → z = y := by
      simpa using IsGeachConvergent.gconv (F := F) (g := ⟨0, 1, 0, 0⟩);
    apply this x x y rfl Rxy |>.symm;
instance [F.IsCoreflexive] : F.IsGeachConvergent ⟨0, 1, 0, 0⟩ where
  gconv x y z Rxy Rxz := by
    simp_all only [Rel.Iterate.iff_zero, Rel.Iterate.iff_succ, exists_eq_right, exists_eq_left'];
    subst Rxy;
    exact F.corefl Rxz |>.symm;


protected class IsFunctional (F : Frame) where
  functional : ∀ ⦃x y z : F.World⦄, x ≺ y → x ≺ z → y = z

lemma functional [F.IsFunctional] : ∀ {x y z : F.World}, x ≺ y → x ≺ z → y = z := by apply IsFunctional.functional

instance [F.IsGeachConvergent ⟨1, 1, 0, 0⟩] : F.IsFunctional where
  functional x y z Rxy Rxz := by
    have : ∀ x y z : F, x ≺ y → x ≺ z → z = y := by
      simpa using IsGeachConvergent.gconv (F := F) (g := ⟨1, 1, 0, 0⟩);
    exact this x y z Rxy Rxz |>.symm;
instance [F.IsFunctional] : F.IsGeachConvergent ⟨1, 1, 0, 0⟩ where
  gconv x y z Rxy Rxz := by
    simp_all only [Rel.Iterate.iff_succ, Rel.Iterate.iff_zero, exists_eq_right, exists_eq_left'];
    apply IsFunctional.functional Rxy Rxz |>.symm;


protected class IsDense (F : Frame) where
  dense : ∀ ⦃x y : F.World⦄, x ≺ y → ∃ u, x ≺ u ∧ u ≺ y

lemma dense [F.IsDense] : ∀ {x y : F.World}, x ≺ y → ∃ u, x ≺ u ∧ u ≺ y := by apply IsDense.dense

instance [F.IsGeachConvergent ⟨0, 1, 2, 0⟩] : F.IsDense where
  dense x y Rxy := by
    have : ∀ x y z : F, x = y → x ≺ z → ∃ u, y ≺ u ∧ u ≺ z := by
      simpa using IsGeachConvergent.gconv (F := F) (g := ⟨0, 1, 2, 0⟩);
    apply this x x y rfl Rxy;
instance [F.IsDense] : F.IsGeachConvergent ⟨0, 1, 2, 0⟩ where
  gconv x y z Rxy Rxz := by
    simp_all only [Rel.Iterate.iff_zero, Rel.Iterate.iff_succ, exists_eq_right, exists_eq_right'];
    subst Rxy;
    obtain ⟨u, Ryu, Rzu⟩ := IsDense.dense Rxz;
    use u;


protected class IsPreorder (F : Frame) extends F.IsReflexive, F.IsTransitive

protected class IsEquivalence (F : Frame) extends F.IsReflexive, F.IsTransitive, F.IsSymmetric
instance [F.IsEquivalence] : F.IsPreorder where

end Frame


instance : whitepoint.IsGeachConvergent g := ⟨by
  rintro x y z Rxy Rxz;
  use ();
  constructor <;> . apply Rel.Iterate.true_any; tauto;
⟩
instance : whitepoint.IsPreorder where


section definability

open Formula (atom)
open Formula.Kripke

lemma validate_axiomGeach_of_isGeachConvergent (g) [F.IsGeachConvergent g] : F ⊧ (Axioms.Geach g (.atom 0)) := by
  rintro V x h;
  apply Satisfies.boxItr_def.mpr;
  obtain ⟨y, Rxy, hbp⟩ := Satisfies.diaItr_def.mp h;
  intro z Rxz;
  apply Satisfies.diaItr_def.mpr;
  obtain ⟨u, Ryu, Rzu⟩ := Frame.IsGeachConvergent.gconv Rxy Rxz;
  use u;
  constructor;
  . assumption;
  . exact (Satisfies.boxItr_def.mp hbp) Ryu;

lemma validate_AxiomT_of_reflexive [refl : F.IsReflexive] : F ⊧ (Axioms.T (.atom 0)) := validate_axiomGeach_of_isGeachConvergent ⟨0, 0, 1, 0⟩
lemma validate_AxiomD_of_serial [ser : F.IsSerial] : F ⊧ (Axioms.D (.atom 0)) := validate_axiomGeach_of_isGeachConvergent ⟨0, 0, 1, 1⟩
lemma validate_AxiomB_of_symmetric [sym : F.IsSymmetric] : F ⊧ (Axioms.B (.atom 0)) := validate_axiomGeach_of_isGeachConvergent ⟨0, 1, 0, 1⟩
lemma validate_AxiomFour_of_transitive [trans : F.IsTransitive] : F ⊧ (Axioms.Four (.atom 0)) := validate_axiomGeach_of_isGeachConvergent ⟨0, 2, 1, 0⟩
lemma validate_AxiomFive_of_euclidean [eucl : F.IsEuclidean] : F ⊧ (Axioms.Five (.atom 0)) := validate_axiomGeach_of_isGeachConvergent ⟨1, 1, 0, 1⟩
lemma validate_AxiomPoint2_of_confluent [conf : F.IsPiecewiseStronglyConvergent] : F ⊧ (Axioms.Point2 (.atom 0)) := validate_axiomGeach_of_isGeachConvergent ⟨1, 1, 1, 1⟩
lemma validate_AxiomTc_of_coreflexive [corefl : F.IsCoreflexive] : F ⊧ (Axioms.Tc (.atom 0)) := validate_axiomGeach_of_isGeachConvergent ⟨0, 1, 0, 0⟩


lemma isGeachConvergent_of_validate_axiomGeach {g} (h : F ⊧ (Axioms.Geach g (.atom 0))) : F.IsGeachConvergent g := ⟨by
  rintro x y z Rxy Rxz;
  let V : Kripke.Valuation F := λ v _ => y ≺^[g.m] v;
  have : Satisfies ⟨F, V⟩ x (□^[g.j](◇^[g.n](.atom 0)))  := h V x $ by
    apply Satisfies.diaItr_def.mpr;
    use y;
    constructor;
    . assumption;
    . apply Satisfies.boxItr_def.mpr;
      aesop;
  replace : Satisfies ⟨F, V⟩ z (◇^[g.n]Formula.atom 0) := Satisfies.boxItr_def.mp this Rxz;
  obtain ⟨u, Rzu, Ryu⟩ := Satisfies.diaItr_def.mp this;
  exact ⟨u, Ryu, Rzu⟩;
⟩

lemma reflexive_of_validate_AxiomT (h : F ⊧ (Axioms.T (.atom 0))) : F.IsReflexive := by
  suffices F.IsGeachConvergent ⟨0, 0, 1, 0⟩ by infer_instance;
  apply isGeachConvergent_of_validate_axiomGeach;
  simpa;

lemma transitive_of_validate_AxiomFour (h : F ⊧ (Axioms.Four (.atom 0))) : F.IsTransitive := by
  suffices F.IsGeachConvergent ⟨0, 2, 1, 0⟩ by infer_instance;
  apply isGeachConvergent_of_validate_axiomGeach;
  simpa;

lemma euclidean_of_validate_AxiomFive (h : F ⊧ (Axioms.Five (.atom 0))) : F.IsEuclidean := by
  suffices F.IsGeachConvergent ⟨1, 1, 0, 1⟩ by infer_instance;
  apply isGeachConvergent_of_validate_axiomGeach;
  simpa;

lemma symmetric_of_validate_AxiomB (h : F ⊧ (Axioms.B (.atom 0))) : F.IsSymmetric := by
  suffices F.IsGeachConvergent ⟨0, 1, 0, 1⟩ by infer_instance;
  apply isGeachConvergent_of_validate_axiomGeach;
  simpa;

lemma serial_of_validate_AxiomD (h : F ⊧ (Axioms.D (.atom 0))) : F.IsSerial := by
  suffices F.IsGeachConvergent ⟨0, 0, 1, 1⟩ by infer_instance;
  apply isGeachConvergent_of_validate_axiomGeach;
  simpa;

lemma coreflexive_of_validate_AxiomTc (h : F ⊧ (Axioms.Tc (.atom 0))) : F.IsCoreflexive := by
  suffices F.IsGeachConvergent ⟨0, 1, 0, 0⟩ by infer_instance;
  apply isGeachConvergent_of_validate_axiomGeach;
  simpa;

lemma confluent_of_validate_AxiomPoint2 (h : F ⊧ (Axioms.Point2 (.atom 0))) : F.IsPiecewiseStronglyConvergent := by
  suffices F.IsGeachConvergent ⟨1, 1, 1, 1⟩ by infer_instance;
  apply isGeachConvergent_of_validate_axiomGeach;
  simpa;

end definability


section canonicality

variable [Entailment S (Formula ℕ)]
variable {𝓢 : S} [Entailment.Consistent 𝓢] [Entailment.K 𝓢]

open Formula.Kripke
open Entailment
open MaximalConsistentTableau
open canonicalModel

instance [Entailment.HasAxiomGeach g 𝓢] : (canonicalFrame 𝓢).IsGeachConvergent g := ⟨by
  rintro x y z Rxy Rxz;
  have ⟨u, hu⟩ := lindenbaum (𝓢 := 𝓢) (t₀ := ⟨□⁻¹^[g.m]'y.1.1, ◇⁻¹^[g.n]'z.1.2⟩) $ by
    rintro Γ Δ hΓ hΔ;
    by_contra! hC;
    have hγ : □^[g.m](Γ.conj) ∈ y.1.1 := y.mdp_mem₁_provable collect_boxItr_fconj! $ iff_mem₁_fconj.mpr $ by
      intro χ hχ;
      obtain ⟨ξ, hξ, rfl⟩ := Finset.LO.exists_of_mem_boxItr hχ;
      apply hΓ;
      assumption;
    have hδ : ◇^[g.n](Δ.disj) ∈ z.1.2 := mdp_mem₂_provable distribute_diaItr_fdisj! $ iff_mem₂_fdisj.mpr $ by
      intro χ hχ;
      obtain ⟨ξ, hξ, rfl⟩ := Finset.LO.exists_of_mem_diaItr hχ;
      apply hΔ;
      assumption;
    generalize Γ.conj = γ at hγ hC;
    generalize Δ.disj = δ at hδ hC;
    have : 𝓢 ⊢ □^[g.m]γ ➝ □^[g.m]δ := imply_boxItr_distribute'! hC;
    have : □^[g.m]δ ∈ y.1.1 := mdp_mem₁_provable this hγ;
    have : ◇^[g.i](□^[g.m]δ) ∈ x.1.1 := def_multirel_diaItr_mem₁.mp Rxy this;
    have : □^[g.j](◇^[g.n]δ) ∈ x.1.1 := mdp_mem₁_provable axiomGeach! this;
    have : ◇^[g.n]δ ∈ z.1.1 := def_multirel_boxItr_mem₁.mp Rxz this;
    have : ◇^[g.n]δ ∉ z.1.2 := iff_not_mem₂_mem₁.mpr this;
    contradiction;
  use u;
  constructor;
  . apply def_multirel_boxItr_mem₁.mpr;
    apply hu.1;
  . apply def_multirel_diaItr_mem₂.mpr;
    apply hu.2;
⟩

instance [Entailment.HasAxiomT 𝓢] : (canonicalFrame 𝓢).IsReflexive := by simp
instance [Entailment.HasAxiomD 𝓢] : (canonicalFrame 𝓢).IsSerial := by simp
instance [Entailment.HasAxiomB 𝓢] : (canonicalFrame 𝓢).IsSymmetric := by simp
instance [Entailment.HasAxiomFour 𝓢] : (canonicalFrame 𝓢).IsTransitive := by simp
instance [Entailment.HasAxiomFive 𝓢] :(canonicalFrame 𝓢).IsEuclidean := by simp
instance [Entailment.HasAxiomTc 𝓢] : (canonicalFrame 𝓢).IsCoreflexive := by simp
instance [Entailment.HasAxiomPoint2 𝓢] : (canonicalFrame 𝓢).IsPiecewiseStronglyConvergent := by simp

end canonicality

end Kripke

end LO.Modal
