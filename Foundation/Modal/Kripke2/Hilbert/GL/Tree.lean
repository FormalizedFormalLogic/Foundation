import Foundation.Modal.Kripke2.Hilbert.GL.Completeness
import Foundation.Modal.Kripke2.Tree

namespace LO.Modal

open Kripke
open System
open Formula.Kripke


namespace Kripke

variable (T : Kripke.FiniteTransitiveTree)

lemma valid_on_FiniteTransitiveTreeClass_of_valid_on_TransitiveIrreflexiveFrameClass (h : Kripke.TransitiveIrreflexiveFiniteFrameClass ⊧ φ)
  : ∀ T : Kripke.FiniteTransitiveTree, T.toFrame ⊧ φ := by
  intro T;
  apply @h T.toFrame;
  use T.toFiniteFrame;
  refine ⟨⟨?_, ?_⟩, rfl⟩;
  . exact T.rel_transitive;
  . exact T.rel_irreflexive;

lemma satisfies_at_root_on_FiniteTransitiveTree (h : ∀ T : FiniteTransitiveTree, T.toFrame ⊧ φ) : ∀ M : FiniteTransitiveTreeModel, Satisfies M.toModel M.root φ := by
  intro M;
  exact h M.toFiniteTransitiveTree M.Val M.root;

open Classical in
lemma valid_on_TransitiveIrreflexiveFrameClass_of_satisfies_at_root_on_FiniteTransitiveTree
  : (∀ M : FiniteTransitiveTreeModel, Satisfies M.toModel M.root φ) → TransitiveIrreflexiveFiniteFrameClass ⊧ φ := by
  rintro H _ ⟨F, ⟨F_trans, F_irrefl⟩, rfl⟩ V r;
  let M : Kripke.Model := ⟨F.toFrame, V⟩;
  apply Model.PointGenerated.modal_equivalent_at_root F_trans r |>.mp;
  apply Model.TransitiveTreeUnravelling.modal_equivalence_at_root (M := (M↾r).toModel) (Frame.PointGenerated.rel_transitive F_trans) ⟨r, by tauto⟩ |>.mp;
  exact H ⟨(F.FiniteTransitiveTreeUnravelling F_trans F_irrefl r), (M.FiniteTransitiveTreeUnravelling r).Val⟩;

end Kripke


namespace Hilbert.GL.Kripke

theorem iff_provable_satisfies_FiniteTransitiveTree : Hilbert.GL ⊢! φ ↔ (∀ M : FiniteTransitiveTreeModel, Satisfies M.toModel M.root φ) := by
  constructor;
  . intro h M;
    have : TransitiveIrreflexiveFiniteFrameClass ⊧ φ := Hilbert.GL.Kripke.finiteSound.sound h;
    have := valid_on_FiniteTransitiveTreeClass_of_valid_on_TransitiveIrreflexiveFrameClass this;
    exact satisfies_at_root_on_FiniteTransitiveTree this M;
  . intro h;
    apply Hilbert.GL.Kripke.finiteComplete.complete;
    intro F hF V;
    apply valid_on_TransitiveIrreflexiveFrameClass_of_satisfies_at_root_on_FiniteTransitiveTree h hF;

lemma iff_unprovable_exists_unsatisfies_FiniteTransitiveTree
  : Hilbert.GL ⊬ φ ↔ ∃ M : FiniteTransitiveTreeModel, ¬Satisfies M.toModel M.root φ := by
  apply Iff.not_left;
  push_neg;
  exact iff_provable_satisfies_FiniteTransitiveTree;

end Hilbert.GL.Kripke

end LO.Modal
