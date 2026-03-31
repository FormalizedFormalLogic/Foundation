module

public import Foundation.Propositional.Kripke.Completeness

@[expose] public section

namespace LO.Propositional

open Kripke
open Formula.Kripke

namespace Kripke

protected abbrev Frame.IsSymmetric (F : Frame) := _root_.Std.Symm F.Rel
lemma Frame.symm {F : Frame} [F.IsSymmetric] : ∀ ⦃x y : F⦄, x ≺ y → y ≺ x := by apply Std.Symm.symm

protected abbrev Frame.IsEuclidean (F : Frame) := _root_.IsRightEuclidean F.Rel
lemma Frame.eucl {F : Frame} [F.IsEuclidean] : ∀ ⦃x y z : F⦄, x ≺ y → x ≺ z → y ≺ z := by apply IsRightEuclidean.reucl

section definability

variable {F : Kripke.Frame}

lemma validate_axiomLEM_of_isSymmetric [F.IsSymmetric] : F ⊧ (Axioms.LEM φ) := by
  have := F.symm;
  revert this;
  contrapose!;
  intro h;

  obtain ⟨V, x, h⟩ := ValidOnFrame.exists_valuation_world_of_not h;
  unfold Satisfies at h;
  push Not at h;
  rcases h with ⟨h₁, h₂⟩;

  replace h₂ := Satisfies.neg_def.not.mp h₂;
  push Not at h₂;
  obtain ⟨y, Rxy, hy⟩ := h₂;

  use x, y;
  constructor;
  . assumption;
  . by_contra Ryx;
    exact h₁ $ Satisfies.formula_hereditary Ryx hy;

lemma validate_axiomLEM_of_isEuclidean [F.IsEuclidean] : F ⊧ (Axioms.LEM φ) := validate_axiomLEM_of_isSymmetric

lemma isEuclidean_of_validate_axiomLEM (h : F ⊧ (Axioms.LEM (.atom 0))) : F.IsEuclidean := ⟨by
  rintro x y z Rxy Rxz;
  let V : Kripke.Valuation F := ⟨λ {a v} => y ≺ v, by
    intro w v Rwv a Rzw;
    exact F.trans Rzw Rwv;
  ⟩;
  suffices Satisfies ⟨F, V⟩ z (.atom 0) by simpa [Satisfies] using this;
  apply V.hereditary Rxz;
  have : ∀ (w : F.World), x ≺ w → y ≺ w → y ≺ x := by simpa [Semantics.Models, Satisfies, V, or_iff_not_imp_right] using h V x;
  apply this y;
  . exact Rxy;
  . apply F.refl;
⟩

end definability

section canonicality

variable {S} [Entailment S (Formula ℕ)]
variable {𝓢 : S} [Entailment.Consistent 𝓢] [Entailment.Int 𝓢]

open Formula.Kripke
open Entailment
     Entailment.FiniteContext
open canonicalModel
open SaturatedConsistentTableau
open Classical

instance [Entailment.HasAxiomLEM 𝓢] : (canonicalFrame 𝓢).IsEuclidean := ⟨by
  suffices ∀ x y z : (canonicalFrame 𝓢), x ≺ y → x ≺ z → z ≺ y by
    intro x y z Rxy Rxz;
    exact this x z y Rxz Rxy;

  rintro x y z;
  intro Rxy;
  contrapose!;
  intro nRzy;
  obtain ⟨φ, hzφ, nhyφ⟩ := Set.not_subset.mp nRzy;
  apply Set.not_subset.mpr;
  use ∼φ;
  constructor;
  . by_contra hnφ;
    have : φ ∈ y.1.1 := Rxy $ (or_iff_not_imp_right.mp $ iff_mem₁_or.mp $ mem₁_of_provable (by simp)) hnφ;
    contradiction;
  . exact not_mem₁_neg_of_mem₁ hzφ;
⟩

end canonicality

end Kripke

end LO.Propositional
end
