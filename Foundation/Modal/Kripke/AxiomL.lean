module

public import Foundation.Modal.Kripke.Irreflexive

@[expose] public section

namespace LO.Modal

namespace Kripke

open Formula.Kripke

variable {F : Kripke.Frame}

protected abbrev Frame.IsConverseWellFounded (F : Frame) := _root_.IsConverseWellFounded _ F.Rel

lemma Frame.cwf [F.IsConverseWellFounded] : ConverseWellFounded F.Rel := IsConverseWellFounded.cwf

instance [F.IsFinite] [F.IsTransitive] [F.IsIrreflexive] : F.IsConverseWellFounded := ⟨IsConverseWellFounded.cwf⟩

lemma validate_AxiomL_of_trans_cwf [F.IsTransitive] [F.IsConverseWellFounded] : F ⊧ (Axioms.L φ) := by
  rintro V w;
  apply Satisfies.imp_def.mpr;
  contrapose;
  intro h;
  obtain ⟨x, Rwx, h⟩ := by simpa using Satisfies.box_def.not.mp h;
  obtain ⟨m, ⟨⟨Rwm, hm⟩, hm₂⟩⟩ := F.cwf.has_min ({ x | w ≺ x ∧ ¬(Satisfies ⟨F, V⟩ x φ) }) $ by
    use x;
    tauto;
  replace hm₂ : ∀ x, w ≺ x → ¬Satisfies ⟨F, V⟩ x φ → ¬m ≺ x := by simpa using hm₂;
  apply Satisfies.not_box_def.mpr;
  use m;
  constructor;
  . assumption;
  . apply Satisfies.not_imp_def.mpr;
    constructor;
    . intro n rmn;
      apply not_imp_not.mp $ hm₂ n (IsTrans.trans _ _ _ Rwm rmn);
      exact rmn;
    . assumption;

lemma validate_AxiomL_of_finite_trans_irrefl [F.IsFinite] [F.IsTransitive] [F.IsIrreflexive] : F ⊧ (Axioms.L φ) := validate_AxiomL_of_trans_cwf

lemma isTransitive_of_validate_axiomL (h : F ⊧ (Axioms.L (.atom 0))) : F.IsTransitive where
  trans := by
    revert h;
    contrapose!;
    intro hT;
    obtain ⟨w, v, Rwv, u, Rvu, nRwu⟩ := by simpa [Transitive] using hT;
    apply ValidOnFrame.not_of_exists_valuation_world;
    use (λ w _ => w ≠ v ∧ w ≠ u), w;
    apply Satisfies.imp_def.not.mpr;
    push_neg;
    constructor;
    . intro x Rwx hx;
      by_cases exv : x = v;
      . subst x;
        simpa using Satisfies.atom_def.mp $ @hx u Rvu;
      . apply Satisfies.atom_def.mpr;
        constructor;
        . assumption;
        . by_contra hC;
          subst x;
          contradiction;
    . apply Satisfies.box_def.not.mpr;
      push_neg;
      use v;
      constructor;
      . assumption;
      . simp [Semantics.Models, Satisfies];

lemma isConverseWellFounded_of_validate_axiomL (h : F ⊧ (Axioms.L (.atom 0))) : F.IsConverseWellFounded where
  cwf := by
    revert h;
    contrapose;
    intro hCF;
    obtain ⟨X, ⟨x, _⟩, hX₂⟩ := by simpa using ConverseWellFounded.iff_has_max.not.mp hCF;
    apply ValidOnFrame.not_of_exists_valuation_world;
    use (λ w _ => w ∉ X), x;
    apply Satisfies.imp_def.not.mpr;
    push_neg;
    constructor;
    . intro y Rxy;
      by_cases hys : y ∈ X
      . obtain ⟨z, _, Rxz⟩ := hX₂ y hys;
        intro hy;
        have : z ∉ X := by simpa using Satisfies.atom_def.mp $ hy z Rxz;
        contradiction;
      . intro _;
        apply Satisfies.atom_def.mpr;
        simpa;
    . obtain ⟨y, _, _⟩ := hX₂ x (by assumption);
      apply Satisfies.box_def.not.mpr;
      push_neg;
      use y;
      constructor;
      . assumption;
      . simpa [Semantics.Models, Satisfies];

/-
protected instance FrameClass.transitive_cwf.definability : FrameClass.trans_cwf.DefinedByFormula (Axioms.L (.atom 0)) := ⟨by
  intro F;
  constructor;
  . simpa using validate_L_of_trans_and_cwf;
  . intro h;
    constructor;
    . apply trans_of_validate_L; simp_all;
    . apply cwf_of_validate_L; simp_all;
⟩

protected instance FrameClass.finite_trans_irrefl.definability : FrameClass.finite_trans_irrefl.DefinedByFormula (Axioms.L (.atom 0)) := ⟨by
  intro F;
  constructor;
  . rintro ⟨hTrans, hIrrefl⟩ φ ⟨_, rfl⟩;
    apply validate_L_of_trans_and_cwf;
    . assumption;
    . apply Finite.converseWellFounded_of_trans_irrefl';
      . exact F.world_finite;
      . assumption;
      . assumption;
  . intro h;
    refine ⟨?_, ?_⟩;
    . apply trans_of_validate_L; simpa using h;
    . intro w;
      simpa using ConverseWellFounded.iff_has_max.mp (cwf_of_validate_L (by simpa using h)) {w} (by simp);
⟩
-/

end Kripke

end LO.Modal
end
