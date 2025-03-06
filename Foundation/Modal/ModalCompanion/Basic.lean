import Foundation.Propositional.Logic.Basic
import Foundation.Modal.Logic.WellKnown
import Foundation.Modal.Logic.Extension

namespace LO

open Entailment FiniteContext
open Necessitation
open Propositional

def Propositional.Formula.goedelTranslate : Propositional.Formula α → Modal.Formula α
  | .atom a  => □(.atom a)
  | ⊥ => ⊥
  | φ ⋏ ψ => (goedelTranslate φ) ⋏ (goedelTranslate ψ)
  | φ ⋎ ψ => (goedelTranslate φ) ⋎ (goedelTranslate ψ)
  | φ ➝ ψ => □((goedelTranslate φ) ➝ (goedelTranslate ψ))
postfix:90 "ᵍ" => Propositional.Formula.goedelTranslate

class Modal.ModalCompanion (IL : Propositional.Logic) (ML : Modal.Logic) where
  companion : ∀ {φ}, φ ∈ IL ↔ φᵍ ∈ ML

lemma Modal.instModalCompanion (h₁ : ∀ {φ}, φ ∈ IL → φᵍ ∈ ML) (h₂ : ∀ {φ}, φᵍ ∈ ML → φ ∈ IL) : Modal.ModalCompanion IL ML := ⟨λ {_} => ⟨h₁, h₂⟩⟩


namespace Propositional.Logic

def minimamMC (IL : Propositional.Logic) : Modal.Logic := Modal.Logic.sumNormal Modal.Logic.S4 { φᵍ | φ ∈ IL }

def maximalMC (IL : Propositional.Logic) : Modal.Logic := Modal.Logic.addNormal IL.minimamMC (Axioms.Grz (.atom 0))

/-
lemma minimanMC_Hilbert (H : Hilbert ℕ) : H.logic.minimamMC = Modal.Logic.sumNormal Modal.Logic.S4 { φᵍ | φ ∈ H.axiomInstances } := by
  ext φ;
  constructor;
  . rintro h;
    unfold Hilbert.logic minimamMC at h;
    induction h with
    | mem₁ h => exact Modal.Logic.sumNormal.mem₁ h;
    | mdp hφ hψ ihφ ihψ => apply Modal.Logic.sumNormal.mdp ihφ ihψ;
    | subst h ih => apply Modal.Logic.sumNormal.subst ih;
    | nec h ih => apply Modal.Logic.sumNormal.nec ih;
    | mem₂ h =>
      apply Modal.Logic.sumNormal.mem₂;
      obtain ⟨φ, hφ, rfl⟩ := h;
      use φ;
      simp at hφ;
  . sorry;
-/

end Propositional.Logic


section

open Propositional.Formula (goedelTranslate)

lemma Modal.instModalCompanion_of_minimamMC_via_KripkeSemantics
  {IL : Propositional.Logic}
  (IC : Propositional.Kripke.FrameClass) (hIL_complete : ∀ {φ}, φ ∈ IL ↔ φ ∈ IC.logic)
  (MC : Modal.Kripke.FrameClass) (hML_complete : ∀ {φ}, φ ∈ IL.minimamMC ↔ φ ∈ MC.logic)
  (hIC_MC : ∀ F ∈ IC, ⟨F.World, F.Rel⟩ ∈ MC)
  : ModalCompanion IL (IL.minimamMC) := Modal.instModalCompanion
  (by
    intro φ hφ;
    apply Modal.Logic.sumNormal.mem₂;
    use φ;
  )
  (by
    intro φ;
    contrapose;
    intro h;
    have := hIL_complete.not.mp h;
    obtain ⟨F, hF, hF₂⟩ := by simpa using this;
    obtain ⟨V, x, hφ⟩ := Propositional.Formula.Kripke.ValidOnFrame.exists_valuation_world_of_not hF₂;
    have h₁ : ∀ ψ x, Propositional.Formula.Kripke.Satisfies ⟨F, V⟩ x ψ ↔ (Modal.Formula.Kripke.Satisfies ⟨⟨F.World, F.Rel⟩, V⟩ x (ψᵍ)) := by
      intro ψ x;
      induction ψ using Propositional.Formula.rec' generalizing x with
      | hatom a =>
        unfold goedelTranslate;
        constructor;
        . intro _ _ h;
          exact V.hereditary h $ by assumption;
        . intro h;
          exact h x (F.rel_refl x);
      | hfalsum =>  rfl;
      | hor φ ψ ihp ihq =>
        unfold goedelTranslate;
        constructor;
        . rintro (hp | hq);
          . apply Modal.Formula.Kripke.Satisfies.or_def.mpr; left;
            exact ihp x |>.mp hp;
          . apply Modal.Formula.Kripke.Satisfies.or_def.mpr; right;
            exact ihq x |>.mp hq;
        . intro h;
          rcases Modal.Formula.Kripke.Satisfies.or_def.mp h with (hp | hq)
          . left; exact ihp x |>.mpr hp;
          . right; exact ihq x |>.mpr hq;
      | _ => simp_all [goedelTranslate, Propositional.Formula.Kripke.Satisfies, Modal.Formula.Kripke.Satisfies];
    apply hML_complete.not.mpr;
    apply Modal.Formula.Kripke.ValidOnFrameClass.not_of_exists_frame;
    use { World := F.World, Rel := F.Rel };
    constructor;
    . apply hIC_MC;
      exact hF;
    . apply Modal.Formula.Kripke.ValidOnFrame.not_of_exists_valuation_world;
      use V, x;
      exact (h₁ φ x).not.mp hφ;
  )

lemma Modal.instModalCompanion_of_maximalMC_via_KripkeSemantics
  {IL : Propositional.Logic}
  (IC : Propositional.Kripke.FrameClass) (hIL_complete : ∀ {φ}, φ ∈ IL ↔ φ ∈ IC.logic)
  (MC : Modal.Kripke.FrameClass) (hML_complete : ∀ {φ}, φ ∈ IL.maximalMC ↔ φ ∈ MC.logic)
  (hIC_MC : ∀ F ∈ IC, ⟨F.World, F.Rel⟩ ∈ MC)
  : ModalCompanion IL (IL.maximalMC) := Modal.instModalCompanion
  (by
    intro φ hφ;
    apply Modal.Logic.sumNormal.mem₁;
    apply Modal.Logic.sumNormal.mem₂;
    use φ;
  )
  (by
    intro φ;
    contrapose;
    intro h;
    have := hIL_complete.not.mp h;
    obtain ⟨F, hF, hF₂⟩ := by simpa using this;
    obtain ⟨V, x, hφ⟩ := Propositional.Formula.Kripke.ValidOnFrame.exists_valuation_world_of_not hF₂;
    have h₁ : ∀ ψ x, Propositional.Formula.Kripke.Satisfies ⟨F, V⟩ x ψ ↔ (Modal.Formula.Kripke.Satisfies ⟨⟨F.World, F.Rel⟩, V⟩ x (ψᵍ)) := by
      intro ψ x;
      induction ψ using Propositional.Formula.rec' generalizing x with
      | hatom a =>
        unfold goedelTranslate;
        constructor;
        . intro _ _ h;
          exact V.hereditary h $ by assumption;
        . intro h;
          exact h x (F.rel_refl x);
      | hfalsum =>  rfl;
      | hor φ ψ ihp ihq =>
        unfold goedelTranslate;
        constructor;
        . rintro (hp | hq);
          . apply Modal.Formula.Kripke.Satisfies.or_def.mpr; left;
            exact ihp x |>.mp hp;
          . apply Modal.Formula.Kripke.Satisfies.or_def.mpr; right;
            exact ihq x |>.mp hq;
        . intro h;
          rcases Modal.Formula.Kripke.Satisfies.or_def.mp h with (hp | hq)
          . left; exact ihp x |>.mpr hp;
          . right; exact ihq x |>.mpr hq;
      | _ => simp_all [goedelTranslate, Propositional.Formula.Kripke.Satisfies, Modal.Formula.Kripke.Satisfies];
    apply hML_complete.not.mpr;
    apply Modal.Formula.Kripke.ValidOnFrameClass.not_of_exists_frame;
    use { World := F.World, Rel := F.Rel };
    constructor;
    . apply hIC_MC;
      exact hF;
    . apply Modal.Formula.Kripke.ValidOnFrame.not_of_exists_valuation_world;
      use V, x;
      exact (h₁ φ x).not.mp hφ;
  )

end

/-
lemma dp_of_mdp [ModalDisjunctive mH] [ModalCompanion iH mH] [Entailment.S4 mH] : iH ⊢! φ ⋎ ψ → iH ⊢! φ ∨ iH ⊢! ψ := by
    intro hpq;
    have : mH ⊢! □φᵍ ⋎ □ψᵍ := or₃'''! (imply_left_or'! axiomTc_GTranslate!) (imply_right_or'! axiomTc_GTranslate!) (by simpa using ModalCompanion.companion.mp hpq);
    cases ModalDisjunctive.modal_disjunctive this with
    | inl h => left; exact ModalCompanion.companion.mpr h;
    | inr h => right; exact ModalCompanion.companion.mpr h;

theorem disjunctive_of_modalDisjunctive [ModalDisjunctive mH] [ModalCompanion iH mH] [Entailment.S4 mH] : Disjunctive iH := ⟨dp_of_mdp (iH := iH) (mH := mH)⟩
-/

end LO
