import Foundation.Propositional.Kripke.Completeness
import Foundation.Propositional.Entailment.Cl

namespace LO.Propositional

open Kripke
open Formula.Kripke

namespace Kripke


section definability

variable {F : Kripke.Frame}

lemma validate_LEM_of_symmetric' : Symmetric F → F ⊧ (Axioms.LEM (.atom 0)) := by
  unfold Symmetric Axioms.LEM;
  contrapose;
  push_neg;
  intro h;

  obtain ⟨V, x, h⟩ := ValidOnFrame.exists_valuation_world_of_not h;
  unfold Satisfies at h;
  push_neg at h;
  rcases h with ⟨h₁, h₂⟩;

  replace h₂ := Satisfies.neg_def.not.mp h₂;
  push_neg at h₂;
  obtain ⟨y, Rxy, hy⟩ := h₂;

  use x, y;
  constructor;
  . assumption;
  . by_contra Ryx;
    exact h₁ $ Satisfies.formula_hereditary Ryx hy;

lemma validate_LEM_of_symmetric [IsSymm _ F] : F ⊧ (Axioms.LEM (.atom 0)) := by
  apply validate_LEM_of_symmetric';
  exact IsSymm.symm;

lemma validate_LEM_of_euclidean [IsEuclidean _ F] : F ⊧ (Axioms.LEM (.atom 0)) := validate_LEM_of_symmetric

lemma euclidean_of_validate_LEM : F ⊧ (Axioms.LEM (.atom 0)) → Euclidean F := by
  rintro h x y z Rxy Rxz;
  let V : Kripke.Valuation F := ⟨λ {v a} => z ≺ v, by
    intro w v Rwv a Rzw;
    exact F.trans Rzw Rwv;
  ⟩;
  suffices Satisfies ⟨F, V⟩ y (.atom 0) by simpa [Satisfies] using this;
  apply V.hereditary Rxy;
  simp at h;
  have := @h V x;
  simp [Semantics.Realize, Satisfies, V, or_iff_not_imp_right] at this;
  apply this z;
  . exact Rxz;
  . apply F.refl;

end definability


section canonicality

variable {S} [Entailment (Formula ℕ) S]
variable {𝓢 : S} [Entailment.Consistent 𝓢] [Entailment.Intuitionistic 𝓢]

open Formula.Kripke
open Entailment
     Entailment.FiniteContext
open canonicalModel
open SaturatedConsistentTableau
open Classical

namespace Canonical

instance [Entailment.HasAxiomLEM 𝓢] : IsEuclidean _ (canonicalFrame 𝓢).Rel := ⟨by
  rintro x y z;
  simp [canonicalFrame];
  intro Rxy;
  contrapose;
  intro nRzy;
  obtain ⟨φ, hzφ, nhyφ⟩ := Set.not_subset.mp nRzy;
  apply Set.not_subset.mpr;
  use ∼φ;
  constructor;
  . by_contra hnφ;
    have : φ ∈ y.1.1:= Rxy $ (or_iff_not_imp_right.mp $ iff_mem₁_or.mp $ mem₁_of_provable (by simp)) hnφ;
    contradiction;
  . exact not_mem₁_neg_of_mem₁ hzφ;
⟩

end Canonical

end canonicality


end Kripke

end LO.Propositional
