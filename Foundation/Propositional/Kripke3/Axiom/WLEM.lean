module

public import Foundation.Propositional.Kripke3.Basic
public import Foundation.Propositional.Kripke3.Logic.Int.Completeness
public import Foundation.Vorspiel.Rel.Convergent

@[expose] public section

namespace LO.Propositional

variable {κ α : Type*} [Nonempty κ]

namespace KripkeModel

variable {M : KripkeModel κ α} [M.Intuitionistic] {φ ψ χ : Formula α}

lemma validates_axiomWLEM [IsPiecewiseStronglyConvergent M.rel] : M ⊧ (Axioms.WLEM φ) := by
  have : PiecewiseStronglyConvergent M.rel := IsPiecewiseStronglyConvergent.ps_convergent;
  contrapose! this;
  obtain ⟨x, h⟩ := exists_world_notForces_of_notValidates this;

  replace h := forces_or.not.mp h;
  push_neg at h;
  rcases h with ⟨h₁, h₂⟩;

  replace h₁ := forces_neg.not.mp h₁;
  push_neg at h₁;
  obtain ⟨y, Rxy, hy⟩ := h₁;

  replace h₂ := forces_neg.not.mp h₂;
  push_neg at h₂;
  obtain ⟨z, Rxz, hz⟩ := h₂;

  dsimp [PiecewiseStronglyConvergent]
  push_neg;
  use x, y, z;
  refine ⟨Rxy, Rxz, ?_⟩;
  . intro u Ryu;
    by_contra Rzu;
    exact hz u Rzu $ M.formula_persistency hy Ryu;

lemma isPiecewiseStronglyConvergent_of_validates_axiomWLEM [Std.Refl K]
  (h : ∀ V, letI M : KripkeModel κ α := ⟨K, V⟩; M ⊧ (Axioms.WLEM #a))
  : IsPiecewiseStronglyConvergent K := by
  constructor;
  rintro x y z Rxy Rxz;
  have := (h $ (λ {p v} => K y v)) x;
  rw [forces_or] at this;
  rcases this with (hi | hi);
  . exfalso;
    simp only [forces_neg, ForcingRelation.NotForces, forces_atom] at hi;
    apply hi y Rxy $ Std.Refl.refl y;
  . simp only [forces_neg, ForcingRelation.NotForces, forces_atom] at hi;
    push_neg at hi;
    obtain ⟨w, Rzw, Ryw⟩ := hi z Rxz;
    use w;

end KripkeModel

section


variable {S} [Entailment S (Formula ℕ)]
variable {𝓢 : S} [Entailment.Consistent 𝓢] [Entailment.Int 𝓢]

open Formula.Kripke
open LO.Entailment
     LO.Entailment.FiniteContext
open canonicalKripkeModel
open SaturatedConsistentTableau
open Classical

instance [Entailment.HasAxiomWLEM 𝓢] : IsPiecewiseStronglyConvergent (canonicalKripkeModel 𝓢).rel := by
  constructor;
  rintro x y z Rxy Rxz;
  obtain ⟨w, hw⟩ := lindenbaum (𝓢 := 𝓢) $ by
    show Tableau.Consistent 𝓢 (y.1.1 ∪ z.1.1, ∅);
    rintro Γ Δ hΓ hΔ h;
    replace hΓ : (SetLike.coe Γ) ⊆ (↑y.1.1 ∪ ↑z.1.1) := by grind;
    replace hΔ : Δ = ∅ := by simpa using hΔ;
    subst hΔ;

    let Θx := { φ ∈ Γ | (φ ∈ y.1.1 ∧ φ ∈ x.1.1) ∨ (φ ∈ z.1.1 ∧ φ ∈ x.1.1) };
    let Θy := { φ ∈ Γ | φ ∈ y.1.1 ∧ φ ∉ x.1.1 };
    let Θz := { φ ∈ Γ | φ ∈ z.1.1 ∧ φ ∉ x.1.1 };

    simp only [Finset.disj_empty] at h;
    replace : [Θx.conj] ⊢[𝓢] ∼∼Θz.conj ➝ ∼Θy.conj := contra! $ FiniteContext.deductInv'! $ by
      apply FConj_DT.mpr;
      apply FConj_DT'.mpr;
      apply FConj_DT'.mpr;
      apply mdp! $ Context.of! h;
      apply FConj_DT.mp;
      apply CFConj_FConj!_of_subset;
      intro φ hφ;
      rcases hΓ hφ with h | h <;>
      . dsimp [Θx, Θy, Θz];
        grind;

    have h_Θx_x   :   Θx.conj ∈ x.1.1 := iff_mem₁_fconj.mpr $ by intro; grind only [Finset.mem_coe, Finset.mem_filter];
    have h_Θz_z   :   Θz.conj ∈ z.1.1 := iff_mem₁_fconj.mpr $ by intro; grind only [Finset.mem_coe, Finset.mem_filter];
    have nh_nΘz_z :  ∼Θz.conj ∉ z.1.1 := not_mem₁_neg_of_mem₁ h_Θz_z;
    have nh_nΘz_x :  ∼Θz.conj ∉ x.1.1 := Set.notMem_subset Rxz nh_nΘz_z;
    have h_nnΘz_x : ∼∼Θz.conj ∈ x.1.1 := or_iff_not_imp_left.mp (iff_mem₁_or.mp $ mem₁_of_provable $ wlem!) nh_nΘz_x;
    have h_nΘy_y  :  ∼Θy.conj ∈ y.1.1 := Rxy $ mdp₁_mem h_nnΘz_x $ mdp_mem₁_provable this h_Θx_x;
    have nh_nΘy_y :  ∼Θy.conj ∉ y.1.1 := not_mem₁_neg_of_mem₁ $ iff_mem₁_fconj.mpr $ by intro; grind only [Finset.mem_coe, Finset.mem_filter];
    contradiction;
  use w;
  simpa using hw;

end

end LO.Propositional

end
