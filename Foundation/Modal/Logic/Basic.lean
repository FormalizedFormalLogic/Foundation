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

class Consistent (L : Logic) : Prop where
  consis : L ≠ Set.univ
attribute [simp] Consistent.consis



variable {L : Logic}

section

open Entailment

variable [L.QuasiNormal]
variable {φ ψ χ : Formula ℕ}

protected lemma subset_K : Logic.K ⊆ L := QuasiNormal.subset_K

protected lemma of_mem_K : φ ∈ Logic.K → φ ∈ L := fun h => Logic.subset_K h

protected lemma mdp (hφψ : φ ➝ ψ ∈ L) (hφ : φ ∈ L) : ψ ∈ L := QuasiNormal.mdp_closed hφψ hφ

protected lemma subst (hφ : φ ∈ L) : φ⟦s⟧ ∈ L := QuasiNormal.subst_closed hφ s

protected lemma efq (h : ⊥ ∈ L) : ∀ {φ}, φ ∈ L := by
  intro φ;
  have : ⊥ ➝ φ ∈ L := by apply QuasiNormal.subset_K; simp;
  exact Logic.mdp this h;

lemma p_q_Apq (hφ : φ ∈ L) (hψ : ψ ∈ L) : φ ⋏ ψ ∈ L := by
  apply Logic.mdp (φ := ψ);
  . apply Logic.mdp (φ := φ) (ψ := ψ ➝ φ ⋏ ψ);
    . apply Logic.of_mem_K;
      exact and₃!;
    . assumption;
  . assumption;

lemma conj_iffAux {Γ : List (Formula ℕ)} : Γ.conj₂ ∈ L ↔ ∀ φ ∈ Γ, φ ∈ L := by
  constructor;
  . intro h φ hφ;
    refine Logic.mdp ?_ h;
    apply Logic.of_mem_K;
    apply left_Conj₂!_intro hφ;
  . intro h;
    induction Γ using List.induction_with_singleton with
    | hnil =>
      simp only [List.conj₂_nil];
      apply Logic.of_mem_K;
      exact verum!;
    | hsingle φ =>
      apply h;
      simp;
    | @hcons φ Γ hΓ ih =>
      simp only [List.conj₂_cons_nonempty hΓ];
      apply p_q_Apq;
      . apply h; tauto;
      . apply ih; tauto;

lemma conj_iff {Γ : FormulaFinset ℕ} : Γ.conj ∈ L ↔ ∀ φ ∈ Γ, φ ∈ L := by
  constructor;
  . intro h φ hφ;
    apply Logic.conj_iffAux (Γ := Γ.toList) |>.mp $ h;
    simpa;
  . intro h;
    apply Logic.conj_iffAux (Γ := Γ.toList) |>.mpr;
    intro φ hφ;
    apply h;
    simpa using hφ;


section

variable [L.Consistent]

@[simp]
lemma no_bot : ⊥ ∉ L := by
  by_contra hC;
  obtain ⟨φ, hφ⟩ := Set.ne_univ_iff_exists_not_mem L |>.mp $ Consistent.consis;
  have : φ ∈ L := Logic.efq hC;
  contradiction;

lemma no_either_no : ¬(φ ∈ L ∧ ∼φ ∈ L) := by
  rintro ⟨h₁, h₂⟩;
  exact no_bot $ Logic.mdp h₂ h₁;

lemma not_neg_mem_of_mem : φ ∈ L → ∼φ ∉ L := by
  have := no_either_no (φ := φ) (L := L);
  tauto;

lemma not_mem_of_neg_mem : ∼φ ∈ L → φ ∉ L := by
  have := no_either_no (φ := φ) (L := L);
  tauto;

end


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

abbrev Kripke.FrameClass.finite_logic (C: FrameClass) : Logic := { φ | C ⊧ φ }

lemma Logic.eq_Hilbert_Logic_KripkeFrameClass_Logic
  {H : Hilbert ℕ} {C : FrameClass}
  [sound : Sound H C] [complete : Complete H C]
  : H.logic = C.logic := by
  ext φ;
  constructor;
  . exact sound.sound;
  . exact complete.complete;

instance Logic.consistent_of_consistent_hilbert {H : Hilbert ℕ} [Entailment.Consistent H] : Consistent (H.logic) := ⟨by
  apply Set.eq_univ_iff_forall.not.mpr;
  push_neg;
  obtain ⟨φ, hφ⟩ : ∃ φ, H ⊬ φ := Entailment.Consistent.exists_unprovable inferInstance;
  use φ;
  simpa;
⟩

lemma Logic.K.eq_AllKripkeFrameClass_Logic : Logic.K = FrameClass.all.logic := eq_Hilbert_Logic_KripkeFrameClass_Logic

-- lemma Logic.K.eq_AllKripkeFiniteFrameClass_Logic : Logic.K = FrameClass.finite_all.logic := eq_Hilbert_Logic_KripkeFrameClass_Logic

end


end LO.Modal
