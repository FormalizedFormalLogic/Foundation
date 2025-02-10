import Foundation.Modal.Hilbert.K
import Foundation.Modal.Kripke.Hilbert.K


namespace LO.Modal

abbrev Logic := Set (Modal.Formula ℕ)

abbrev Hilbert.logic (H : Hilbert ℕ) : Logic := { φ | H ⊢! φ }

protected abbrev Logic.K : Logic := Hilbert.K.logic


namespace Logic

protected class Unnecessitation (L : Logic) where
  unnec_closed {φ} : □φ ∈ L → φ ∈ L

protected class ModalDisjunctive (L : Logic) where
  modal_disjunctive_closed {φ ψ} : □φ ⋎ □ψ ∈ L → φ ∈ L ∨ ψ ∈ L

class QuasiNormal (L : Logic) where
  subset_K : Logic.K ⊆ L
  mdp_closed {φ ψ} : φ ➝ ψ ∈ L → φ ∈ L → ψ ∈ L
  subst_closed {φ} : φ ∈ L → ∀ s, φ⟦s⟧ ∈ L

class Normal (L : Logic) extends L.QuasiNormal where
  nec_closed {φ} : φ ∈ L → □φ ∈ L

class Consistent (L : Logic) : Prop where
  consis : L ≠ Set.univ
attribute [simp] Consistent.consis


section

variable {L : Logic} {φ ψ : Formula ℕ}
variable [L.QuasiNormal]

protected lemma mdp (hφψ : φ ➝ ψ ∈ L) (hφ : φ ∈ L) : ψ ∈ L := QuasiNormal.mdp_closed hφψ hφ

protected lemma efq (h : ⊥ ∈ L) : ∀ {φ}, φ ∈ L := by
  intro φ;
  have : ⊥ ➝ φ ∈ L := by apply QuasiNormal.subset_K; simp;
  exact Logic.mdp this h;

@[simp]
protected lemma no_bot [L.Consistent] : ¬(⊥ ∈ L) := by
  intro h;
  exact Consistent.consis $ Set.eq_univ_of_univ_subset $ by
    intro φ _;
    apply Logic.efq h;

lemma no_either_not [L.Consistent] : (φ ∉ L) ∨ (∼φ ∉ L) := by
  apply or_iff_not_imp_left.mpr;
  intro hφ hnφ;
  push_neg at hφ;
  exact Logic.no_bot $ Logic.mdp hnφ hφ;

end


end Logic




namespace Hilbert

open System

variable {H : Hilbert ℕ}

instance normal [H.HasK] : (H.logic).Normal where
  subset_K := by
    intro φ hφ;
    induction hφ using Hilbert.Deduction.rec! with
    | maxm h =>
      rcases (by simpa using h) with ⟨s, rfl⟩; simp;
    | mdp ihφψ ihφ => exact mdp! ihφψ ihφ;
    | nec ih => exact nec! ih;
    | _ => simp;
  mdp_closed := by
    intro φ ψ hφψ hφ;
    exact hφψ ⨀ hφ;
  subst_closed := by
    intro φ hφ s;
    exact Hilbert.Deduction.subst! s hφ;
  nec_closed := by
    intro φ hφ;
    exact System.nec! hφ;

instance [System.Unnecessitation H] : H.logic.Unnecessitation := ⟨fun {_} h => unnec! h⟩

instance [System.ModalDisjunctive H] : H.logic.ModalDisjunctive := ⟨fun {_ _} h => modal_disjunctive h⟩

end Hilbert

instance : (Logic.K).Normal := Hilbert.normal



section

open Kripke

abbrev Kripke.FrameClass.logic (C : FrameClass) : Logic := { φ | C ⊧ φ }

abbrev Kripke.FiniteFrameClass.logic (C : FiniteFrameClass) : Logic := { φ | C ⊧ φ }

lemma Logic.eq_Hilbert_Logic_KripkeFrameClass_Logic
  {H : Hilbert ℕ} {C : FrameClass}
  [sound : Sound H C] [complete : Complete H C]
  : H.logic = C.logic := by
  ext φ;
  constructor;
  . exact sound.sound;
  . exact complete.complete;

lemma Logic.eq_Hilbert_Logic_KripkeFiniteFrameClass_Logic
  {H : Hilbert ℕ} {C : FiniteFrameClass}
  [sound : Sound H C] [complete : Complete H C]
  : H.logic = C.logic := by
  ext φ;
  constructor;
  . exact sound.sound;
  . exact complete.complete;

lemma Logic.K.eq_AllKripkeFrameClass_Logic : Logic.K = AllFrameClass.logic := eq_Hilbert_Logic_KripkeFrameClass_Logic

lemma Logic.K.eq_AllKripkeFiniteFrameClass_Logic : Logic.K = AllFiniteFrameClass.logic := eq_Hilbert_Logic_KripkeFiniteFrameClass_Logic

end


end LO.Modal
