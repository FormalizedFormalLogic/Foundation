import Foundation.Modal.Logic.Basic
import Foundation.Modal.Hilbert.K

namespace LO.Modal

open LO.Entailment LO.Modal.Entailment

variable {L L₀ L₁ L₂ L₃ : Logic}

namespace Logic

protected class IsQuasiNormal (L : Logic) where
  subset_K : Logic.K ⊆ L
  mdp_closed {φ ψ} : φ ➝ ψ ∈ L → φ ∈ L → ψ ∈ L
  subst_closed {φ} : φ ∈ L → ∀ s, φ⟦s⟧ ∈ L

protected class IsNormal (L : Logic) extends L.IsQuasiNormal where
  nec_closed {φ} : φ ∈ L → □φ ∈ L


section

open Entailment
open Entailment.FiniteContext

variable [L.IsQuasiNormal]
variable {φ ψ χ : Formula ℕ}

protected lemma subset_K : Logic.K ⊆ L := IsQuasiNormal.subset_K

lemma of_mem_K : φ ∈ Logic.K → φ ∈ L := fun h => Logic.subset_K h

protected lemma mdp (hφψ : φ ➝ ψ ∈ L) (hφ : φ ∈ L) : ψ ∈ L := IsQuasiNormal.mdp_closed hφψ hφ

protected lemma subst (hφ : φ ∈ L) : φ⟦s⟧ ∈ L := IsQuasiNormal.subst_closed hφ s

protected lemma efq (h : ⊥ ∈ L) : ∀ {φ}, φ ∈ L := by
  intro φ;
  apply Logic.mdp ?_ h;
  apply L.of_mem_K;
  simp;

lemma p_q_Apq (hφ : φ ∈ L) (hψ : ψ ∈ L) : φ ⋏ ψ ∈ L := by
  apply Logic.mdp ?_ hψ;
  apply Logic.mdp ?_ hφ;
  apply L.of_mem_K;
  simp;

@[simp]
lemma C_id : φ ➝ φ ∈ L := by
  apply L.of_mem_K;
  simp;

@[simp]
lemma E_id : φ ⭤ φ ∈ L := by
  apply L.of_mem_K;
  simp;

lemma E_symm (h : φ ⭤ ψ ∈ L) : ψ ⭤ φ ∈ L := by
  apply Logic.mdp ?_ h;
  apply L.of_mem_K;
  -- TODO: extract this as `inside_E!_symm`
  apply deduct'!;
  apply E!_symm;
  simp;

lemma C_of_E_mp (h : φ ⭤ ψ ∈ L) : φ ➝ ψ ∈ L := by
  apply Logic.mdp ?_ h;
  apply L.of_mem_K;
  -- TODO: extract this as `CEC!`
  apply deduct'!;
  apply C_of_E_mp!;
  simp;

lemma C_of_E_mpr (h : φ ⭤ ψ ∈ L) : ψ ➝ φ ∈ L := C_of_E_mp $ L.E_symm h

lemma E_of_C_of_C (h : φ ➝ ψ ∈ L) (h : ψ ➝ φ ∈ L) : φ ⭤ ψ ∈ L := by
  apply p_q_Apq <;> tauto;

lemma C_trans (h₁ : φ ➝ ψ ∈ L) (h₂ : ψ ➝ χ ∈ L) : φ ➝ χ ∈ L := by
  apply Logic.mdp ?_ h₂;
  apply Logic.mdp ?_ h₁;
  apply L.of_mem_K;
  -- TODO: extract this as `inside_C!_trans`
  apply deduct'!;
  apply deduct!;
  have H₁ : [ψ ➝ χ, φ ➝ ψ] ⊢[Hilbert.K]! φ ➝ ψ := by_axm!;
  have H₂ : [ψ ➝ χ, φ ➝ ψ] ⊢[Hilbert.K]! ψ ➝ χ := by_axm!;
  exact C!_trans H₁ H₂;

lemma C_replace (h : φ ➝ ψ ∈ L) (hφ : φ' ➝ φ ∈ L) (hψ : ψ ➝ ψ' ∈ L) : φ' ➝ ψ' ∈ L :=
  C_trans hφ $ C_trans h hψ

lemma conj_iffAux {Γ : List (Formula ℕ)} : Γ.conj₂ ∈ L ↔ ∀ φ ∈ Γ, φ ∈ L := by
  constructor;
  . intro h φ hφ;
    refine Logic.mdp ?_ h;
    apply L.of_mem_K;
    apply left_Conj₂!_intro hφ;
  . intro h;
    induction Γ using List.induction_with_singleton with
    | hnil =>
      simp only [List.conj₂_nil];
      apply L.of_mem_K;
      exact verum!;
    | hsingle φ =>
      apply h;
      simp;
    | @hcons φ Γ hΓ ih =>
      simp [List.conj₂_cons_nonempty hΓ];
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

variable [L.IsNormal]

variable {φ ψ : Formula ℕ}

protected lemma nec (hφ : φ ∈ L) : □φ ∈ L := IsNormal.nec_closed hφ

lemma neg_congruence (h : φ ⭤ ψ ∈ L) : ∼φ ⭤ ∼ψ ∈ L := by
  apply E_of_C_of_C;
  . apply Logic.mdp ?_ (C_of_E_mpr h);
    apply L.of_mem_K;
    simp;
  . apply Logic.mdp ?_ (C_of_E_mp h);
    apply L.of_mem_K;
    simp;

lemma box_regularity (h : φ ➝ ψ ∈ L) : □φ ➝ □ψ ∈ L := by
  apply Logic.mdp ?_ $ Logic.nec h;
  apply L.of_mem_K;
  simp;

lemma box_congruence (h : φ ⭤ ψ ∈ L) : □φ ⭤ □ψ ∈ L := by
  apply E_of_C_of_C;
  . apply box_regularity;
    apply C_of_E_mp h;
  . apply box_regularity;
    apply C_of_E_mpr h;

lemma dia_regularity (h : φ ⭤ ψ ∈ L) : ◇φ ⭤ ◇ψ ∈ L := by
  apply neg_congruence;
  apply box_congruence;
  apply neg_congruence;
  exact h;

end


inductive sumQuasiNormal (L₁ L₂ : Logic) : Logic
  | mem₁ {φ}    : φ ∈ L₁ → sumQuasiNormal L₁ L₂ φ
  | mem₂ {φ}    : φ ∈ L₂ → sumQuasiNormal L₁ L₂ φ
  | mdp  {φ ψ}  : sumQuasiNormal L₁ L₂ (φ ➝ ψ) → sumQuasiNormal L₁ L₂ φ → sumQuasiNormal L₁ L₂ ψ
  | subst {φ s} : sumQuasiNormal L₁ L₂ φ → sumQuasiNormal L₁ L₂ (φ⟦s⟧)

abbrev addQuasiNormal (L : Logic) (φ : Formula ℕ) : Logic := sumQuasiNormal L {φ}

inductive sumNormal (L₁ L₂ : Logic) : Logic
  | mem₁ {φ}    : φ ∈ L₁ → sumNormal L₁ L₂ φ
  | mem₂ {φ}    : φ ∈ L₂ → sumNormal L₁ L₂ φ
  | mdp  {φ ψ}  : sumNormal L₁ L₂ (φ ➝ ψ) → sumNormal L₁ L₂ φ → sumNormal L₁ L₂ ψ
  | subst {φ s} : sumNormal L₁ L₂ φ → sumNormal L₁ L₂ (φ⟦s⟧)
  | nec {φ}     : sumNormal L₁ L₂ φ → sumNormal L₁ L₂ (□φ)

abbrev addNormal (L : Logic) (φ : Formula ℕ) : Logic := sumNormal L {φ}

end Logic



namespace Hilbert

open Entailment

instance {H : Hilbert ℕ} [H.HasK] : (H.logic).IsNormal where
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

end Hilbert



def QuasiNormalExtension (L : Logic) := { L' : Logic // L ⊆ L' ∧ L'.IsQuasiNormal }

namespace QuasiNormalExtension

variable {L₀ : Logic} {L : QuasiNormalExtension L₀}

instance : Membership (Formula ℕ) (QuasiNormalExtension L₀) := ⟨λ L φ => φ ∈ L.1⟩

lemma mem_of_mem_base (h : φ ∈ L₀) : φ ∈ L := L.property.1 h

lemma mem_of_mem_LogicK (h : φ ∈ Logic.K) : φ ∈ L := L.property.2.subset_K h

lemma mdp (hφψ : φ ➝ ψ ∈ L) (hφ : φ ∈ L) : ψ ∈ L := L.property.2.mdp_closed hφψ hφ

lemma subst (hφ : φ ∈ L) : φ⟦s⟧ ∈ L := L.property.2.subst_closed hφ s

def add (L₁ L₂ : QuasiNormalExtension L₀) : QuasiNormalExtension L₀ where
  val := Logic.sumQuasiNormal L₁.1 L₂.1
  property := by
    constructor;
    . intro φ hφ;
      apply Logic.sumQuasiNormal.mem₁;
      apply mem_of_mem_base hφ;
    . refine ⟨?_, ?_, ?_⟩;
      . intro φ hφ;
        apply Logic.sumQuasiNormal.mem₁;
        apply mem_of_mem_LogicK hφ;
      . intro φ ψ hφ hφψ;
        apply Logic.sumQuasiNormal.mdp hφ hφψ;
      . intro φ hφ s;
        apply Logic.sumQuasiNormal.subst hφ;

instance : Add (QuasiNormalExtension L₀) := ⟨add⟩

/-
instance : Std.IdempotentOp (α := QuasiNormalExtension L₀) (· + ·) where
  idempotent := by
    intro L;
    sorry;

instance : Std.Commutative (α := QuasiNormalExtension L₀) (· + ·) where
  comm := by
    intro L₁ L₂;
    sorry;

instance : Std.Associative (α := QuasiNormalExtension L₀) (· + ·) where
  assoc := by
    intro L₁ L₂ L₃;
    sorry;
-/

def inter (L₁ L₂ : QuasiNormalExtension L₀) : QuasiNormalExtension L₀ where
  val := L₁.1 ∩ L₂.1
  property := by
    constructor;
    . intro φ hφ;
      apply Set.mem_inter <;> exact mem_of_mem_base hφ;
    . refine ⟨?_, ?_, ?_⟩;
      . intro φ hφ;
        apply Set.mem_inter <;> exact mem_of_mem_LogicK hφ;
      . rintro φ ψ ⟨hφψ₁, hφψ₂⟩ ⟨hφ₁, hφ₂⟩;
        apply Set.mem_inter;
        . exact mdp hφψ₁ hφ₁;
        . exact mdp hφψ₂ hφ₂;
      . rintro φ ⟨hφ₁, hφ₂⟩ s;
        apply Set.mem_inter;
        . exact subst hφ₁;
        . exact subst hφ₂;

instance : Inter (QuasiNormalExtension L₀) := ⟨inter⟩

end QuasiNormalExtension


def ExtensionNormal (L : Logic) := { L' : Logic // L'.IsNormal ∧ L ⊆ L' }

namespace ExtensionNormal

end ExtensionNormal

end LO.Modal
