module

public import Foundation.Modal.Kripke2.Completeness
public import Foundation.Vorspiel.Rel.Coreflexive

@[expose] public section

namespace Rel

variable {R : Rel α α} {x y z : α}

protected structure IsGeachConvergent.Taple where
  i : ℕ
  j : ℕ
  m : ℕ
  n : ℕ

class IsGeachConvergent (R : Rel α α) (i j m n : ℕ) : Prop where
  gconv : ∀ ⦃x y z : α⦄, R.Iterate i x y → R.Iterate j x z → ∃ u, R.Iterate m y u ∧ R.Iterate n z u

instance [R.IsGeachConvergent 0 0 1 0] : Std.Refl R := by
  constructor;
  simpa using IsGeachConvergent.gconv (i := 0) (j := 0) (m := 1) (n := 0);

instance [Std.Refl R] : R.IsGeachConvergent 0 0 1 0 := by
  constructor;
  rintro x y z Rxy Rxz;
  simp_all [Std.Refl.refl];


instance [R.IsGeachConvergent 0 0 1 1] : IsSerial R := by
  constructor;
  have := IsGeachConvergent.gconv (R := R) (i := 0) (j := 0) (m := 1) (n := 1);
  simp only [Iterate.iff_zero, Iterate.iff_succ, exists_eq_right, forall_apply_eq_imp_iff, forall_eq', and_self] at this;
  apply this;

instance [IsSerial R] : R.IsGeachConvergent 0 0 1 1 := by
  constructor;
  rintro x y z Rxy rfl;
  simp_all only [Rel.Iterate.iff_zero, Rel.Iterate.iff_succ, exists_eq_right, and_self];
  apply _root_.IsSerial.serial


instance [R.IsGeachConvergent 0 2 1 0] : IsTrans _ R := by
  constructor;
  rintro x y z Rxy Ryz;
  have := IsGeachConvergent.gconv (R := R) (i := 0) (j := 2) (m := 1) (n := 0) (x := x) (y := x) (z := z) rfl;
  simp only [Iterate.iff_succ, Iterate.iff_zero, exists_eq_right, exists_eq_right', forall_exists_index, and_imp] at this;
  apply this y Rxy Ryz;
instance [IsTrans _ R] : R.IsGeachConvergent 0 2 1 0 := by
  constructor;
  rintro x _ z rfl ⟨y, Rxy, Ryz⟩;
  use z;
  have := IsTrans.trans _ _ z Rxy (by simpa using Ryz);
  tauto;


end Rel



namespace LO.Modal

namespace KripkeModel

variable {κ α} [Nonempty κ] {φ ψ χ : Formula α} {K : Rel κ κ}

lemma models_axiomGeach_of_isGeachConvergent
  (i j m n : ℕ) [K.IsGeachConvergent i j m n]
  : ∀ V, (⟨K, V⟩ : KripkeModel κ α) ⊧ ((◇^[i](□^[m]φ)) ➝ (□^[j](◇^[n]φ))) := by
  intro V x him;
  apply KripkeModel.forces_boxItr.mpr;
  intro y Rxy;
  apply forces_diaItr.mpr;
  obtain ⟨z, Rxz, hm⟩ := forces_diaItr.mp him;
  obtain ⟨u, Rzu, hnu⟩ := Rel.IsGeachConvergent.gconv (i := i) (j := j) (m := m) (n := n) Rxz Rxy;
  use u;
  constructor;
  . assumption;
  . exact (KripkeModel.forces_boxItr.mp hm) _ Rzu;

lemma models_axiomT_of_reflexive [Std.Refl K] : ∀ V, (⟨K, V⟩ : KripkeModel κ α) ⊧ (Axioms.T φ) := models_axiomGeach_of_isGeachConvergent 0 0 1 0
lemma models_axiomD_of_serial [IsSerial K] : ∀ V, (⟨K, V⟩ : KripkeModel κ α) ⊧ (Axioms.D φ) := models_axiomGeach_of_isGeachConvergent 0 0 1 1
lemma models_axiomFour_of_transitive [IsTrans _ K] : ∀ V, (⟨K, V⟩ : KripkeModel κ α) ⊧ (Axioms.Four φ) := models_axiomGeach_of_isGeachConvergent 0 2 1 0
attribute [grind .]
  models_axiomT_of_reflexive
  models_axiomD_of_serial
  models_axiomFour_of_transitive


variable {a : α}

lemma isGeachConvergent_of_models_axiomGeach
  (i j m n : ℕ) (h : ∀ V, (⟨K, V⟩ : KripkeModel κ α) ⊧ ((◇^[i](□^[m](.atom a))) ➝ (□^[j](◇^[n](.atom a)))))
  : K.IsGeachConvergent i j m n := by
  constructor;
  rintro x y z Rxy Rxz;
  let M : KripkeModel κ α := ⟨K, (λ _ v => K.Iterate m y v)⟩;
  have : M.Forces x (□^[j](◇^[n](.atom a))) := h M.val x $ forces_diaItr.mpr ⟨y, ⟨Rxy, forces_boxItr.mpr (by tauto)⟩⟩;
  replace : M.Forces z (◇^[n](.atom a)) := forces_boxItr.mp this z Rxz;
  obtain ⟨u, Rzu, Ryu⟩ := forces_diaItr.mp this;
  use u;
  constructor;
  . exact Ryu;
  . assumption;

lemma reflexive_of_models_axiomT (h : ∀ V, (⟨K, V⟩ : KripkeModel κ α) ⊧ (Axioms.T (.atom a))) : Std.Refl K := by
  suffices K.IsGeachConvergent 0 0 1 0 by infer_instance;
  exact isGeachConvergent_of_models_axiomGeach _ _ _ _ h;

lemma serial_of_models_axiomD (h : ∀ V, (⟨K, V⟩ : KripkeModel κ α) ⊧ (Axioms.D (.atom a))) : IsSerial K := by
  suffices K.IsGeachConvergent 0 0 1 1 by infer_instance;
  exact isGeachConvergent_of_models_axiomGeach _ _ _ _ h;

lemma transitive_of_models_axiomFour (h : ∀ V, (⟨K, V⟩ : KripkeModel κ α) ⊧ (Axioms.Four (.atom a))) : IsTrans _ K := by
  suffices K.IsGeachConvergent 0 2 1 0 by infer_instance;
  apply isGeachConvergent_of_models_axiomGeach _ _ _ _ h;

end KripkeModel


namespace canonicalKripkeModel

open Entailment
open MaximalConsistentTableau
open canonicalKripkeModel

variable {α} [DecidableEq α] [Encodable α]
         {S} [Entailment S (Formula α)]
         {𝓢 : S} [Entailment.Consistent 𝓢] [Entailment.K 𝓢]

instance instGeachConvergent (i j m n : ℕ) [Entailment.HasAxiomGeach ⟨i, j, m, n⟩ 𝓢]
  : (canonicalKripkeModel 𝓢).frame.IsGeachConvergent i j m n := by
  constructor;
  rintro x y z Rxy Rxz;
  have ⟨u, hu⟩ := MaximalConsistentTableau.lindenbaum (𝓢 := 𝓢) (t₀ := ⟨□⁻¹^[m]'y.1.1, ◇⁻¹^[n]'z.1.2⟩) $ by
    rintro Γ Δ hΓ hΔ;
    by_contra! hC;
    have hγ : □^[m](Γ.conj) ∈ y.1.1 := y.mdp_mem₁_provable collect_boxItr_fconj! $ iff_mem₁_fconj.mpr $ by
      intro χ hχ;
      obtain ⟨ξ, hξ, rfl⟩ := Finset.LO.exists_of_mem_boxItr hχ;
      apply hΓ;
      assumption;
    have hδ : ◇^[n](Δ.disj) ∈ z.1.2 := mdp_mem₂_provable distribute_diaItr_fdisj! $ iff_mem₂_fdisj.mpr $ by
      intro χ hχ;
      obtain ⟨ξ, hξ, rfl⟩ := Finset.LO.exists_of_mem_diaItr hχ;
      apply hΔ;
      assumption;
    generalize Γ.conj = γ at hγ hC;
    generalize Δ.disj = δ at hδ hC;
    have : 𝓢 ⊢ □^[m]γ ➝ □^[m]δ := imply_boxItr_distribute'! hC;
    have : □^[m]δ ∈ y.1.1 := mdp_mem₁_provable this hγ;
    have : ◇^[i](□^[m]δ) ∈ x.1.1 := iff_relItr_diaItr_subset₁.mp Rxy this;
    have : □^[j](◇^[n]δ) ∈ x.1.1 := mdp_mem₁_provable (axiomGeach! (g := ⟨i, j, m, n⟩)) this;
    have : ◇^[n]δ ∈ z.1.1 := iff_relItr_boxItr_subset₁.mp Rxz this;
    have : ◇^[n]δ ∉ z.1.2 := iff_not_mem₂_mem₁.mpr this;
    contradiction;
  use u;
  constructor;
  . apply iff_relItr_boxItr_subset₁.mpr;
    apply hu.1;
  . apply iff_relItr_diaItr_subset₂.mpr;
    apply hu.2;

instance instReflexive [Entailment.HasAxiomT 𝓢] : Std.Refl (canonicalKripkeModel 𝓢).frame := by
  suffices (canonicalKripkeModel 𝓢).frame.IsGeachConvergent 0 0 1 0 by infer_instance;
  infer_instance;

instance instTransitive [Entailment.HasAxiomFour 𝓢] : IsTrans _ (canonicalKripkeModel 𝓢).frame := by
  suffices (canonicalKripkeModel 𝓢).frame.IsGeachConvergent 0 2 1 0 by infer_instance;
  infer_instance;

end canonicalKripkeModel

end LO.Modal

end
