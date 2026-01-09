module
import Foundation.Modal.Kripke.Logic.GL.Completeness
import Foundation.Modal.Kripke.Tree
import Mathlib.Tactic.TFAE

namespace LO.Modal

open Formula
open Formula.Kripke
open Entailment
open Formula
open Kripke
open Modal.Kripke

namespace Kripke

instance {F : Frame} {r : outParam F} [F.IsFiniteTree r] : F.IsFiniteGL where

end Kripke


namespace GL.Kripke

open Classical
open Kripke Kripke.Model

theorem tree_completeness_TFAE : [
  Modal.GL ⊢ φ,
  FrameClass.finite_GL ⊧ φ,
  ∀ F : Kripke.Frame, ∀ r, [F.IsFiniteTree r] → F ⊧ φ,
  ∀ M : Kripke.Model, ∀ r, [M.IsFiniteTree r] → r ⊧ φ
].TFAE := by
  tfae_have 1 → 2 := by apply Sound.sound;
  tfae_have 2 → 1 := by apply Complete.complete;
  tfae_have 2 → 3 := by
    intro h F r h_tree;
    apply h;
    apply Set.mem_setOf_eq.mpr;
    infer_instance;
  tfae_have 3 → 4 := by
    intro h M r _;
    apply h;
  tfae_have 4 → 2 := by
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
  tfae_finish;

lemma iff_provable_satisfies_FiniteTransitiveTree : Modal.GL ⊢ φ ↔ (∀ M : Kripke.Model, ∀ r, [M.IsFiniteTree r] → r ⊧ φ) := tree_completeness_TFAE (φ := φ) |>.out 0 3

lemma iff_unprovable_exists_unsatisfies_FiniteTransitiveTree : Modal.GL ⊬ φ ↔ ∃ M : Model, ∃ r, M.IsFiniteTree r ∧ ¬r ⊧ φ := by
  apply Iff.not_left;
  push_neg;
  exact iff_provable_satisfies_FiniteTransitiveTree;

end GL.Kripke

end LO.Modal
