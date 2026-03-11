module

public import Foundation.Propositional.Kripke3.Basic
public import Foundation.Vorspiel.Rel.Connected
public import Foundation.Propositional.Kripke3.Logic.Int.Completeness

@[expose] public section

namespace LO.Propositional

variable {κ α : Type*} [Nonempty κ]

namespace KripkeModel

variable {M : KripkeModel κ α} [M.Intuitionistic] {φ ψ χ : Formula α}

lemma validates_axiomDummett [IsPiecewiseStronglyConnected M.rel] : M ⊧ (Axioms.Dummett φ ψ) := by
  have : PiecewiseStronglyConnected M.rel := IsPiecewiseStronglyConnected.ps_connected;
  contrapose! this;
  obtain ⟨x, h⟩ := exists_world_notForces_of_notValidates this;
  replace h := forces_or.not.mp h;
  push_neg at h;
  rcases h with ⟨h₁, h₂⟩;

  replace h₁ := forces_imp.not.mp h₁;
  push_neg at h₁;
  obtain ⟨y, Rxy, hyφ, hyψ⟩ := h₁;

  replace h₂ := forces_imp.not.mp h₂;
  push_neg at h₂;
  obtain ⟨z, Rxz, hzψ, hzφ⟩ := h₂;

  dsimp [PiecewiseStronglyConnected]
  push_neg;
  use x, y, z;
  refine ⟨Rxy, Rxz, ?_⟩;
  . set_option push_neg.use_distrib true in by_contra! hC;
    rcases hC with (Ryz | Rzy);
    . apply hzφ $ M.formula_persistency hyφ Ryz;
    . apply hyψ $ M.formula_persistency hzψ Rzy;

variable [DecidableEq α]
lemma isPiecewiseStronglyConvergent_of_validates_axiomDummett
  (a b : α) (hab : a ≠ b := by trivial)
  [Std.Refl K]
  (h : ∀ V, letI M : KripkeModel κ α := ⟨K, V⟩; M ⊧ (Axioms.Dummett #a #b))
  : IsPiecewiseStronglyConvergent K := by
  constructor;
  rintro x y z Rxy Rxz;
  have := (h $ (λ {p v} => if p = a then K y v else if p = b then K z v else True)) x;
  rw [forces_or] at this;
  rcases this with (hi | hi);
  . simp only [forces_imp, forces_atom, ↓reduceIte, hab.symm] at hi;
    use y;
    constructor;
    . apply Std.Refl.refl;
    . apply hi;
      . assumption;
      . apply Std.Refl.refl;
  . use z;
    simp only [forces_imp, forces_atom, hab.symm, ↓reduceIte] at hi;
    constructor;
    . apply hi z Rxz;
      exact Std.Refl.refl z;
    . apply Std.Refl.refl;

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

instance [Entailment.HasAxiomDummett 𝓢] : IsPiecewiseStronglyConnected (canonicalKripkeModel 𝓢).rel := by
  constructor;
  rintro x y z Rxy Rxz;
  by_contra!;
  obtain ⟨φ, hφy, hφz⟩ := Set.not_subset.mp this.1;
  obtain ⟨ψ, hψz, hψy⟩ := Set.not_subset.mp this.2;
  rcases (show φ ➝ ψ ∈ x.1.1 ∨ ψ ➝ φ ∈ x.1.1 by exact iff_mem₁_or.mp $ mem₁_of_provable dummett!) with (hφψx | hψφx);
  . exact hψy $ mdp₁_mem hφy (Rxy hφψx);
  . exact hφz $ mdp₁_mem hψz (Rxz hψφx);

end

end LO.Propositional
end
