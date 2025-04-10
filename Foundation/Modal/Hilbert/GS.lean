import Foundation.Modal.Logic.WellKnown
import Foundation.Modal.Hilbert.WellKnown
import Foundation.Modal.Entailment.GL
import Mathlib.Tactic.TFAE
import Foundation.Modal.Boxdot.GL_Grz

namespace LO.Entailment

open FiniteContext

variable {S F : Type*} [BasicModalLogicalConnective F] [Entailment F S]
variable {𝓢 : S} {φ ψ : F}

class NecCongr [LogicalConnective F] (𝓢 : S) where
  nec_congr {φ ψ : F} : 𝓢 ⊢ φ ⭤ ψ → 𝓢 ⊢ □φ ⭤ □ψ

section

variable [NecCongr 𝓢]

alias nec_congr := NecCongr.nec_congr
lemma nec_congr! {φ ψ : F} : 𝓢 ⊢! φ ⭤ ψ → 𝓢 ⊢! □φ ⭤ □ψ := by rintro ⟨hp⟩; exact ⟨nec_congr hp⟩

end


class RosserRule [LogicalConnective F] (𝓢 : S) where
  rosser {φ : F} : 𝓢 ⊢ φ → 𝓢 ⊢ ∼□φ

section

variable [RosserRule 𝓢]

alias rosser := RosserRule.rosser
lemma rosser! : 𝓢 ⊢! φ → 𝓢 ⊢! ∼□φ := by rintro ⟨hp⟩; exact ⟨rosser hp⟩

end


protected class Modal.GS (𝓢 : S) extends Entailment.Cl 𝓢, HasDiaDuality 𝓢, HasAxiomT 𝓢, RosserRule 𝓢, NecCongr 𝓢 where
  Ax2 (φ ψ : F) : 𝓢 ⊢ (φ ⋏ □φ) ➝ □φ ⋎ □(φ ➝ ψ)
  Ax3 (φ : F) : 𝓢 ⊢ φ ➝ ◇□φ
  Ax4 (φ : F) : 𝓢 ⊢ □(∼□φ) ➝ □(φ ⋎ □(∼□φ))

section

variable [Modal.GS 𝓢]

namespace Modal.GS

protected def axiomK : 𝓢 ⊢ Axioms.K φ ψ := by
  sorry;
instance : HasAxiomK 𝓢 := ⟨fun _ _ ↦ Modal.GS.axiomK⟩

protected def axiomFour : 𝓢 ⊢ Axioms.Four φ := by
  sorry;
instance : HasAxiomFour 𝓢 := ⟨fun _ ↦ Modal.GS.axiomFour⟩

end Modal.GS

end


end LO.Entailment


namespace LO.Modal

namespace Hilbert

open Entailment

variable {α : Type*}

protected structure GS_System (α : Type*) where
  axioms : Set (Formula α)

namespace GS_System

abbrev axiomInstances (H : Hilbert.GS_System α) : Set (Formula α) := { φ⟦s⟧ | (φ ∈ H.axioms) (s : Substitution α) }

inductive Deduction (H : Hilbert.GS_System α) : (Formula α) → Type _
  | imply₁ φ ψ   : Deduction H $ Axioms.Imply₁ φ ψ
  | imply₂ φ ψ χ : Deduction H $ Axioms.Imply₂ φ ψ χ
  | ec φ ψ       : Deduction H $ Axioms.ElimContra φ ψ
  | mdp {φ ψ}    : Deduction H (φ ➝ ψ) → Deduction H φ → Deduction H ψ
  | maxm {φ}      : φ ∈ H.axiomInstances → Deduction H φ
  | nec_congr {φ ψ}       : Deduction H (φ ⭤ ψ) → Deduction H (□φ ⭤ □ψ)
  | rosser {φ}         : Deduction H φ → Deduction H (∼□φ)

namespace Deduction

variable {H H₁ H₂ : Hilbert.GS_System α}

instance : Entailment (Formula α) (Hilbert.GS_System α) := ⟨Deduction⟩

instance : Entailment.Lukasiewicz H where
  mdp := mdp
  imply₁ := imply₁
  imply₂ := imply₂
  elim_contra := ec

instance : Entailment.Cl H where

instance : Entailment.HasDiaDuality H := inferInstance
instance : Entailment.RosserRule H := ⟨rosser⟩
instance : Entailment.NecCongr H := ⟨nec_congr⟩

lemma maxm! {φ} (h : φ ∈ H.axiomInstances) : H ⊢! φ := ⟨maxm h⟩

noncomputable def rec!
  {motive      : (φ : Formula α) → H ⊢! φ → Sort*}
  (maxm       : ∀ {φ}, (h : φ ∈ H.axiomInstances) → motive φ (maxm! h))
  (mdp        : ∀ {φ ψ}, {hpq : H ⊢! φ ➝ ψ} → {hp : H ⊢! φ} → motive (φ ➝ ψ) hpq → motive φ hp → motive ψ (mdp! hpq hp))
  (nec_congr  : ∀ {φ ψ}, {hp : H ⊢! φ ⭤ ψ} → (ihp : motive (φ ⭤ ψ) hp) → motive (□φ ⭤ □ψ) (nec_congr! hp))
  (rosser     : ∀ {φ}, {hp : H ⊢! φ} → (ihp : motive φ hp) → motive (∼□φ) (rosser! hp))
  (imply₁     : ∀ {φ ψ}, motive (Axioms.Imply₁ φ ψ) $ ⟨imply₁ φ ψ⟩)
  (imply₂     : ∀ {φ ψ χ}, motive (Axioms.Imply₂ φ ψ χ) $ ⟨imply₂ φ ψ χ⟩)
  (ec : ∀ {φ ψ}, motive (Axioms.ElimContra φ ψ) $ ⟨ec φ ψ⟩)
  : ∀ {φ}, (d : H ⊢! φ) → motive φ d := by
  intro φ d;
  induction d.some with
  | maxm h => exact maxm h
  | mdp hpq hp ihpq ihp => exact mdp (ihpq ⟨hpq⟩) (ihp ⟨hp⟩)
  | rosser hp ihp => exact rosser (ihp ⟨hp⟩)
  | nec_congr hp ihp => exact nec_congr (ihp ⟨hp⟩)
  | _ => aesop;

def subst! {φ} (s) (h : H ⊢! φ) : H ⊢! φ⟦s⟧ := by
  induction h using Deduction.rec! with
  | imply₁ => simp;
  | imply₂ => simp;
  | ec => simp;
  | mdp ihφψ ihφ => exact ihφψ ⨀ ihφ;
  | nec_congr ihφ => exact nec_congr! ihφ;
  | rosser ihφ => exact rosser! ihφ;
  | maxm h =>
    obtain ⟨ψ, h, ⟨s', rfl⟩⟩ := h;
    apply maxm!;
    use ψ;
    constructor;
    . assumption;
    . use s' ∘ s;
      simp;

end Deduction

end GS_System

protected abbrev GS : Hilbert.GS_System ℕ := ⟨{
  □(.atom 0) ➝ (.atom 0),
  ((.atom 0) ⋏ □(.atom 0)) ➝ □(.atom 0) ⋎ □((.atom 0) ➝ (.atom 1)),
  (.atom 0) ➝ ◇□(.atom 0),
  □(∼□(.atom 0)) ➝ □((.atom 0) ⋎ □(∼□(.atom 0)))
}⟩
instance : Entailment.Modal.GS (Hilbert.GS) where
  T φ := by
    apply GS_System.Deduction.maxm;
    use Axioms.T (.atom 0);
    constructor;
    . tauto;
    . use λ _ => φ; tauto;
  Ax2 φ ψ := by
    apply GS_System.Deduction.maxm;
    use ((.atom 0) ⋏ □(.atom 0)) ➝ □(.atom 0) ⋎ □((.atom 0) ➝ (.atom 1));
    constructor;
    . tauto;
    . use λ b => if b = 0 then φ else ψ; tauto;
  Ax3 φ := by
    apply GS_System.Deduction.maxm;
    use (.atom 0) ➝ ◇□(.atom 0);
    constructor;
    . tauto;
    . use λ _ => φ; tauto;
  Ax4 φ := by
    apply GS_System.Deduction.maxm;
    use □(∼□(.atom 0)) ➝ □((.atom 0) ⋎ □(∼□(.atom 0)));
    constructor;
    . tauto;
    . use λ _ => φ; tauto;

end Hilbert



def Formula.gsTranslate : Formula ℕ → Formula ℕ
  | .atom a => .atom a
  | ⊥ => ⊥
  | φ ➝ ψ => φ.gsTranslate ➝ ψ.gsTranslate
  | □φ => φ.gsTranslate ⋏ ∼□(φ.gsTranslate)
postfix:max "ᴾ" => Formula.gsTranslate

variable {φ : Formula ℕ}

lemma provable_Grz_gsTranslated_of_provable_GS (h : Hilbert.GS ⊢! φ) : Hilbert.Grz ⊢! φᴾ := by sorry

lemma provable_GS_translated_of_provable_Grz (h : Hilbert.Grz ⊢! φ) : Hilbert.GS ⊢! φᴾ := by sorry

lemma iff_provable_Grz_provable_gsTranslated_GS : Hilbert.Grz ⊢! φ ↔ Hilbert.GS ⊢! φᴾ := by
  constructor;
  . exact provable_GS_translated_of_provable_Grz;
  . sorry;

lemma iff_provable_GS_gsTranslated_Grz : Hilbert.GS ⊢! φ ↔ Hilbert.Grz ⊢! φᴾ := by
  constructor;
  . exact provable_Grz_gsTranslated_of_provable_GS;
  . sorry;

lemma iff_provable_gsTranslate_boxdotTranslate_provable_gsTranslate_inside : Hilbert.GL ⊢! φᴾᵇ ⭤ φᴾ := by
  induction φ using Formula.rec' with
  | hatom φ => simp [Formula.gsTranslate, Formula.BoxdotTranslation];
  | hfalsum => simp [Formula.gsTranslate, Formula.BoxdotTranslation];
  | himp φ ψ ihφ ihψ =>
    simp [Formula.gsTranslate, Formula.BoxdotTranslation];
    sorry;
  | hbox φ ihφ =>
    simp [Formula.gsTranslate, Formula.BoxdotTranslation];
    sorry;

lemma iff_provable_gsTranslate_boxdotTranslate_provable_gsTranslate : Hilbert.GL ⊢! φᴾᵇ ↔ Hilbert.GL ⊢! φᴾ := ⟨
  λ h => (Entailment.and₁'! iff_provable_gsTranslate_boxdotTranslate_provable_gsTranslate_inside) ⨀ h,
  λ h => (Entailment.and₂'! iff_provable_gsTranslate_boxdotTranslate_provable_gsTranslate_inside) ⨀ h
⟩

lemma iff_provable_GS_provable_boxdot_GL : Hilbert.GS ⊢! φ ↔ Hilbert.GL ⊢! φᴾ := by
  apply Iff.trans iff_provable_GS_gsTranslated_Grz;
  apply Iff.trans Hilbert.iff_boxdotTranslatedGL_Grz.symm;
  exact iff_provable_gsTranslate_boxdotTranslate_provable_gsTranslate;

def Logic.GS : Modal.Logic := { φ | Hilbert.GS ⊢! φ }

end LO.Modal
