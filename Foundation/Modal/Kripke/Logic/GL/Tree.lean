import Foundation.Modal.Kripke.Logic.GL.Completeness
import Foundation.Modal.Kripke.Tree

namespace LO.Modal

open Formula
open Formula.Kripke
open Entailment
open Formula
open Kripke
open Hilbert.Kripke

namespace Kripke

instance {F : Frame} {r : outParam F} [F.IsFiniteTree r] : F.IsFiniteGL where

variable (F : Kripke.Frame) {φ : Formula _}

lemma valid_on_FiniteTransitiveTreeClass_of_valid_on_TransitiveIrreflexiveFrameClass (h : FrameClass.finite_GL ⊧ φ)
  : ∀ F : Kripke.Frame, ∀ r, [F.IsFiniteTree r] → F ⊧ φ := by
  intro F r h_tree;
  apply h;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

lemma satisfies_at_root_on_FiniteTransitiveTree (h : ∀ F : Kripke.Frame, ∀ r, [Finite F.World] → [F.IsTree r] → F ⊧ φ)
  : ∀ M : Model, ∀ r, [M.IsFiniteTree r] → Satisfies M r φ := fun M r _ => h M.toFrame r M.Val r

open Model Classical in
lemma valid_on_TransitiveIrreflexiveFrameClass_of_satisfies_at_root_on_FiniteTransitiveTree
  : (∀ M : Model, ∀ r : M.World, [M.IsFiniteTree r] → Satisfies M r φ) → FrameClass.finite_GL ⊧ φ := by
  rintro H F ⟨_, F_trans, F_irrefl⟩ V r;
  let M : Kripke.Model := ⟨F, V⟩;
  have : (M↾r).IsTransitive := Frame.pointGenerate.isTransitive;
  have : Satisfies ((M↾r).mkTransTreeUnravelling pointGenerate.root) mkTransTreeUnravelling.root φ := @H _ _ $
    @Frame.mkTransTreeUnravelling.instIsFiniteTree (F := (M↾r).toFrame) (r := pointGenerate.root) _
      (Subtype.finite)
      (Frame.pointGenerate.isTransitive)
      (Frame.pointGenerate.isIrreflexive);
  have : Satisfies (M↾r) pointGenerate.root φ := mkTransTreeUnravelling.pMorphism (M↾r) _
    |>.modal_equivalence _
    |>.mp this;
  exact pointGenerate.pMorphism.modal_equivalence _ |>.mp this;


end Kripke


namespace Logic.GL.Kripke

theorem iff_provable_satisfies_FiniteTransitiveTree : Hilbert.GL ⊢! φ ↔ (∀ M : Kripke.Model, ∀ r, [M.IsFiniteTree r] → Satisfies M r φ) := by
  constructor;
  . intro h M r M_tree;
    have : FrameClass.finite_GL ⊧ φ := Sound.sound (𝓜 := FrameClass.finite_GL) h;
    apply valid_on_FiniteTransitiveTreeClass_of_valid_on_TransitiveIrreflexiveFrameClass this M.toFrame r;
  . intro h;
    apply Complete.complete (𝓜 := FrameClass.finite_GL);
    intro F hF V;
    apply valid_on_TransitiveIrreflexiveFrameClass_of_satisfies_at_root_on_FiniteTransitiveTree h hF;

lemma iff_unprovable_exists_unsatisfies_FiniteTransitiveTree
  : Hilbert.GL ⊬ φ ↔ ∃ M : Model, ∃ r, M.IsFiniteTree r ∧ ¬Satisfies M r φ := by
  apply Iff.not_left;
  push_neg;
  exact iff_provable_satisfies_FiniteTransitiveTree;

end Logic.GL.Kripke

end LO.Modal
