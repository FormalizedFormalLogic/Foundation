import Foundation.Modal.Kripke.Hilbert.GL.Completeness
import Foundation.Modal.Kripke.Tree

namespace LO.Modal

open Kripke
open Entailment
open Formula.Kripke


namespace Kripke

variable (F : Kripke.Frame) {φ : Formula _}

lemma valid_on_FiniteTransitiveTreeClass_of_valid_on_TransitiveIrreflexiveFrameClass (h : FrameClass.finite_trans_irrefl ⊧ φ)
  : ∀ F : Kripke.Frame, ∀ r, [F.IsFiniteTree r] → F ⊧ φ := by
  intro F r hT;
  apply h;
  refine ⟨inferInstance, hT.rel_transitive, hT.rel_irreflexive⟩;

lemma satisfies_at_root_on_FiniteTransitiveTree (h : ∀ F : Kripke.Frame, ∀ r, [F.IsFiniteTree r] → F ⊧ φ)
  : ∀ M : Model, ∀ r, [M.IsFiniteTree r] → Satisfies M r φ := fun M r _ => h M.toFrame r M.Val r

open Model Classical in
lemma valid_on_TransitiveIrreflexiveFrameClass_of_satisfies_at_root_on_FiniteTransitiveTree
  : (∀ M : Model, ∀ r : M.World, (Frame.IsFiniteTree M.toFrame r) → Satisfies M r φ) → FrameClass.finite_trans_irrefl ⊧ φ := by
  rintro H F ⟨_, F_trans, F_irrefl⟩ V r;
  let M : Kripke.Model := ⟨F, V⟩;
  have : Satisfies ((M↾r).mkTransTreeUnravelling pointGenerate.root) mkTransTreeUnravelling.root φ := H _ _ ?_;
  have : Satisfies (M↾r) pointGenerate.root φ := mkTransTreeUnravelling.pMorphism (M↾r) (Frame.pointGenerate.rel_trans F_trans) _
    |>.modal_equivalence _
    |>.mp this;
  exact pointGenerate.pMorphism.modal_equivalence _ |>.mp this;
  . exact @Frame.mkTransTreeUnravelling.instIsTree (F := (M↾r).toFrame) _
      (by
        apply @Frame.isFinite_iff (M↾r).toFrame |>.mpr;
        apply Subtype.finite;
      )
      pointGenerate.root
      (Frame.pointGenerate.rel_trans F_trans)
      (Frame.pointGenerate.rel_irrefl F_irrefl)

end Kripke


namespace Hilbert.GL.Kripke

theorem iff_provable_satisfies_FiniteTransitiveTree : Hilbert.GL ⊢! φ ↔ (∀ M : Model, ∀ r, M.IsFiniteTree r → Satisfies M r φ) := by
  constructor;
  . intro h M;
    have : FrameClass.finite_trans_irrefl ⊧ φ := Kripke.finite_sound.sound h;
    have := valid_on_FiniteTransitiveTreeClass_of_valid_on_TransitiveIrreflexiveFrameClass this;
    exact satisfies_at_root_on_FiniteTransitiveTree this M;
  . intro h;
    apply Hilbert.GL.Kripke.finiteComplete.complete;
    intro F hF V;
    apply valid_on_TransitiveIrreflexiveFrameClass_of_satisfies_at_root_on_FiniteTransitiveTree h hF;

lemma iff_unprovable_exists_unsatisfies_FiniteTransitiveTree
  : Hilbert.GL ⊬ φ ↔ ∃ M : Model, ∃ r, M.IsFiniteTree r ∧ ¬Satisfies M r φ := by
  apply Iff.not_left;
  push_neg;
  exact iff_provable_satisfies_FiniteTransitiveTree;

end Hilbert.GL.Kripke

end LO.Modal
