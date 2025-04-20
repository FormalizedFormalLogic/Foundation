import Foundation.Modal.Kripke.Hilbert.GL.Completeness
import Foundation.Modal.Kripke.Tree

namespace LO.Modal

open Kripke
open Entailment
open Formula.Kripke


namespace Kripke

variable (F : Kripke.Frame) {φ : Formula _}

lemma valid_on_FinitE_transitiveTreeClass_of_valid_on_TransitiveIrreflexiveFrameClass (h : FrameClass.finite_trans_irrefl ⊧ φ)
  : ∀ F : Kripke.Frame, ∀ r, [F.IsFiniteTree r] → F ⊧ φ := by
  intro F r h_tree;
  apply h;
  refine ⟨inferInstance, inferInstance, inferInstance⟩;

lemma satisfies_at_root_on_FinitE_transitiveTree (h : ∀ F : Kripke.Frame, ∀ r, [Finite F.World] → [F.IsTree r] → F ⊧ φ)
  : ∀ M : Model, ∀ r, [M.IsFiniteTree r] → Satisfies M r φ := fun M r _ => h M.toFrame r M.Val r

open Model Classical in
lemma valid_on_TransitiveIrreflexiveFrameClass_of_satisfies_at_root_on_FinitE_transitiveTree
  : (∀ M : Model, ∀ r : M.World, [M.IsFiniteTree r] → Satisfies M r φ) → FrameClass.finite_trans_irrefl ⊧ φ := by
  rintro H F ⟨_, F_trans, F_irrefl⟩ V r;
  let M : Kripke.Model := ⟨F, V⟩;
  have : IsTrans (M↾r).World (M↾r).Rel := Frame.pointGenerate.isTrans (trans := F_trans);
  have : Satisfies ((M↾r).mkTransTreeUnravelling pointGenerate.root) mkTransTreeUnravelling.root φ := @H _ _ ?_;
  have : Satisfies (M↾r) pointGenerate.root φ := mkTransTreeUnravelling.pMorphism (M↾r) _
    |>.modal_equivalence _
    |>.mp this;
  exact pointGenerate.pMorphism.modal_equivalence _ |>.mp this;
  . exact @Frame.mkTransTreeUnravelling.instIsFiniteTree (F := (M↾r).toFrame) (r := pointGenerate.root) _
      (Subtype.finite)
      (Frame.pointGenerate.isTrans)
      (Frame.pointGenerate.isIrrefl);

end Kripke


namespace Hilbert.GL.Kripke

theorem iff_provable_satisfies_FinitE_transitiveTree : Hilbert.GL ⊢! φ ↔ (∀ M : Model, ∀ r, [M.IsFiniteTree r] → Satisfies M r φ) := by
  constructor;
  . intro h M r M_tree;
    have : FrameClass.finite_trans_irrefl ⊧ φ := Kripke.finite_sound.sound h;
    apply valid_on_FinitE_transitiveTreeClass_of_valid_on_TransitiveIrreflexiveFrameClass this M.toFrame r;
  . intro h;
    apply Hilbert.GL.Kripke.finiteComplete.complete;
    intro F hF V;
    apply valid_on_TransitiveIrreflexiveFrameClass_of_satisfies_at_root_on_FinitE_transitiveTree h hF;

lemma iff_unprovable_exists_unsatisfies_FinitE_transitiveTree
  : Hilbert.GL ⊬ φ ↔ ∃ M : Model, ∃ r, M.IsFiniteTree r ∧ ¬Satisfies M r φ := by
  apply Iff.not_left;
  push_neg;
  exact iff_provable_satisfies_FinitE_transitiveTree;

end Hilbert.GL.Kripke

end LO.Modal
