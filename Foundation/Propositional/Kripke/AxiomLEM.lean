import Foundation.Propositional.Kripke.Completeness

namespace LO.Propositional

open Kripke
open Formula.Kripke

namespace Kripke


section definability

variable {F : Kripke.Frame}

lemma validate_LEM_of_symmetric : Symmetric F → F ⊧ (Axioms.LEM (.atom 0)) := by
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

lemma validate_LEM_of_euclidean (hEuc : Euclidean F) : F ⊧ (Axioms.LEM (.atom 0)) :=
  validate_LEM_of_symmetric (symm_of_refl_eucl F.rel_refl hEuc)

lemma euclidean_of_validate_LEM : F ⊧ (Axioms.LEM (.atom 0)) → Euclidean F := by
  rintro h x y z Rxy Rxz;
  let V : Kripke.Valuation F := ⟨λ {v a} => z ≺ v, by
    intro w v Rwv a Rzw;
    exact F.rel_trans' Rzw Rwv;
  ⟩;
  suffices Satisfies ⟨F, V⟩ y (.atom 0) by simpa [Satisfies] using this;
  apply V.hereditary Rxy;
  simp at h;
  have := @h V x;
  simp [Semantics.Realize, Satisfies, V, or_iff_not_imp_right] at this;
  apply this z;
  . exact Rxz;
  . apply F.rel_refl;

protected abbrev FrameClass.euclidean : FrameClass := { F | Euclidean F }

instance FrameClass.euclidean.definability : FrameClass.euclidean.DefinedByFormula (Axioms.LEM (.atom 0)) := ⟨by
  intro F;
  constructor;
  . simpa using validate_LEM_of_euclidean;
  . simpa using euclidean_of_validate_LEM;
⟩

@[simp]
lemma FrameClass.euclidean.nonempty : FrameClass.euclidean.Nonempty := by
  use pointFrame;
  simp [Euclidean];

end definability

end Kripke

end LO.Propositional
