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

protected class QuasiNormal (L : Logic) where
  subset_K : Logic.K ⊆ L
  mdp_closed {φ ψ} : φ ➝ ψ ∈ L → φ ∈ L → ψ ∈ L
  subst_closed {φ} : φ ∈ L → ∀ s, φ⟦s⟧ ∈ L

protected class Normal (L : Logic) extends L.QuasiNormal where
  nec_closed {φ} : φ ∈ L → □φ ∈ L

class Sublogic (L₁ L₂ : Logic) where
  subset : L₁ ⊆ L₂

class ProperSublogic (L₁ L₂ : Logic) : Prop where
  ssubset : L₁ ⊂ L₂


variable {L : Logic} {φ ψ : Formula ℕ}


section

variable [L.QuasiNormal]

protected lemma subset_K : Logic.K ⊆ L := QuasiNormal.subset_K

protected lemma of_mem_K : φ ∈ Logic.K → φ ∈ L := fun h => Logic.subset_K h

protected lemma mdp (hφψ : φ ➝ ψ ∈ L) (hφ : φ ∈ L) : ψ ∈ L := QuasiNormal.mdp_closed hφψ hφ

protected lemma subst (hφ : φ ∈ L) : φ⟦s⟧ ∈ L := QuasiNormal.subst_closed hφ s

protected lemma efq (h : ⊥ ∈ L) : ∀ {φ}, φ ∈ L := by
  intro φ;
  have : ⊥ ➝ φ ∈ L := by apply QuasiNormal.subset_K; simp;
  exact Logic.mdp this h;

end


section

variable [L.Normal]

protected lemma nec (hφ : φ ∈ L) : □φ ∈ L := Normal.nec_closed hφ

end


end Logic


namespace Hilbert

open Entailment

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
    exact Entailment.nec! hφ;

instance [Entailment.Unnecessitation H] : H.logic.Unnecessitation := ⟨fun {_} h => unnec! h⟩

instance [Entailment.ModalDisjunctive H] : H.logic.ModalDisjunctive := ⟨fun {_ _} h => modal_disjunctive h⟩

instance : (Logic.K).Normal := Hilbert.normal

end Hilbert


section

open Kripke

abbrev Kripke.FrameClass.logic (C : FrameClass) : Logic := { φ | C ⊧ φ }

abbrev Kripke.FiniteFrameClass.logic (C : FiniteFrameClass) : Logic := { φ | C ⊧ φ }

@[simp]
lemma Logic.eq_kripkeFiniteFrameClass_toFrameClas_logic {C : Kripke.FiniteFrameClass} : (C.toFrameClass.logic) = C.logic := by
  simp [Kripke.FiniteFrameClass.logic, Kripke.FrameClass.logic, FiniteFrameClass.toFrameClass, Semantics.Realize]

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

lemma Logic.K.eq_AllKripkeFrameClass_Logic : Logic.K = FrameClass.all.logic := eq_Hilbert_Logic_KripkeFrameClass_Logic

lemma Logic.K.eq_AllKripkeFiniteFrameClass_Logic : Logic.K = FiniteFrameClass.all.logic := eq_Hilbert_Logic_KripkeFiniteFrameClass_Logic

end


end LO.Modal
