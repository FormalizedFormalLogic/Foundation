import Logic.Modal.Normal.ModalCube

namespace LO.Modal.Normal

open Hilbert

variable {α : Type} [DecidableEq α]

def Formula.BoxdotTranslation : Formula α → Formula α
  | atom p => .atom p
  | ⊥ => ⊥
  | p ⟶ q => (BoxdotTranslation p) ⟶ (BoxdotTranslation q)
  | p ⋏ q => (BoxdotTranslation p) ⋏ (BoxdotTranslation q)
  | p ⋎ q => (BoxdotTranslation p) ⋎ (BoxdotTranslation q)
  | box p => ⊡(BoxdotTranslation p)

postfix:75 "ᵇ" => Formula.BoxdotTranslation

namespace Formula.BoxdotTranslation

variable {p q : Formula α}

@[simp] lemma atom_def : (atom a)ᵇ = (atom a) := by rfl
@[simp] lemma falsum_def : (⊥ : Formula α)ᵇ = ⊥ := by rfl
@[simp] lemma imp_def : (p ⟶ q)ᵇ = pᵇ ⟶ qᵇ := by rfl
@[simp] lemma conj_def : (p ⋏ q)ᵇ = pᵇ ⋏ qᵇ := by rfl
@[simp] lemma disj_def : (p ⋎ q)ᵇ = pᵇ ⋎ qᵇ := by rfl
@[simp] lemma neg_def : (~p)ᵇ = (pᵇ ⟶ ⊥) := by rfl
@[simp] lemma top_def : (⊤ : Formula α)ᵇ = ⊤ := by rfl
@[simp] lemma box_def : ⊡pᵇ = (□p)ᵇ := by rfl

end Formula.BoxdotTranslation

open Formula

def BoxdotAxiomset (Λ : AxiomSet α) : AxiomSet α  := { p | ∅ ⊢ᴹ[Λ]! pᵇ }
postfix:75 "⁻ᵇ" => BoxdotAxiomset

variable {Λ : AxiomSet α} (hK : 𝐊 ⊆ Λ)

lemma boxdot_maxm (h : ∅ ⊢ᴹ[Λ] pᵇ) : (Γ ⊢ᴹ[Λ⁻ᵇ] p) := by
  apply Deduction.maxm;
  simp [BoxdotAxiomset];
  exact ⟨h⟩

lemma boxdot_maxm! (h : ∅ ⊢ᴹ[Λ]! pᵇ) : (Γ ⊢ᴹ[Λ⁻ᵇ]! p) := ⟨boxdot_maxm h.some⟩

-- TODO: move
section

variable {F : Type u} [ModalLogicSymbol F] [NegDefinition F] [ModalDuality F] [DecidableEq F] (Bew : Set F → F → Type u)

class _root_.LO.Hilbert.KT extends Hilbert.K Bew, HasAxiomT Bew

end

lemma KT_boxdotAxiomset : Hilbert.KT (Deduction (Λ⁻ᵇ)) where
  K Γ p q := by
    have := Deduction.ofKSubset hK;
    apply boxdot_maxm;
    simp only [AxiomK, BoxdotTranslation.imp_def, ←BoxdotTranslation.box_def];
    apply boxdotAxiomK;
  T Γ p := by
    have := Deduction.ofKSubset hK;
    apply boxdot_maxm;
    simp only [AxiomT, BoxdotTranslation.imp_def, ←BoxdotTranslation.box_def]
    apply boxdotAxiomT;

open Deduction

end LO.Modal.Normal
