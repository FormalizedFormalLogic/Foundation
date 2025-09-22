import Foundation.Modal.Kripke.Logic.S4
import Foundation.Modal.Logic.SumNormal
import Foundation.Propositional.Kripke.Basic

namespace LO

open LO.Entailment LO.Entailment.FiniteContext LO.Modal.Entailment
open Propositional

@[match_pattern]
def Propositional.Formula.goedelTranslate : Propositional.Formula α → Modal.Formula α
  | .atom a  => □(.atom a)
  | ⊥ => ⊥
  | φ ⋏ ψ => (goedelTranslate φ) ⋏ (goedelTranslate ψ)
  | φ ⋎ ψ => (goedelTranslate φ) ⋎ (goedelTranslate ψ)
  | φ ➝ ψ => □((goedelTranslate φ) ➝ (goedelTranslate ψ))
postfix:90 "ᵍ" => Propositional.Formula.goedelTranslate

class Modal.ModalCompanion (IL : Propositional.Logic ℕ) (ML : Modal.Logic ℕ) where
  companion : ∀ {φ}, IL ⊢ φ ↔ ML ⊢ φᵍ

lemma Modal.instModalCompanion (h₁ : ∀ {φ}, IL ⊢ φ → ML ⊢ φᵍ) (h₂ : ∀ {φ}, ML ⊢ φᵍ → IL ⊢ φ) : Modal.ModalCompanion IL ML := ⟨λ {_} => ⟨h₁, h₂⟩⟩


namespace Propositional.Logic

variable {IL : Propositional.Logic ℕ}

variable (IL : Propositional.Logic ℕ)

abbrev smallestMC (IL : Propositional.Logic ℕ) : Modal.Logic ℕ := Modal.Logic.sumNormal Modal.S4 ((Entailment.theory IL).image (·ᵍ))

instance : Modal.Entailment.S4 IL.smallestMC where
  T φ := by
    constructor;
    apply Modal.Logic.iff_provable.mp;
    apply Modal.Logic.sumNormal.mem₁!;
    simp [Modal.Logic.iff_provable, Entailment.theory];
  Four φ := by
    constructor;
    apply Modal.Logic.iff_provable.mp;
    apply Modal.Logic.sumNormal.mem₁!;
    simp [Modal.Logic.iff_provable, Entailment.theory];

lemma smallestMC.mdp_S4 (hφψ : Modal.S4 ⊢ φ ➝ ψ) (hφ : IL.smallestMC ⊢ φ) : IL.smallestMC ⊢ ψ := by
  exact (Modal.Logic.sumNormal.mem₁! hφψ) ⨀ hφ;

abbrev largestMC (IL : Propositional.Logic ℕ) : Modal.Logic ℕ := Modal.Logic.sumNormal IL.smallestMC ({ Modal.Axioms.Grz (.atom 0) })

instance : Modal.Entailment.Grz IL.largestMC where
  Grz φ := by
    constructor;
    apply Modal.Logic.iff_provable.mp;
    apply Modal.Logic.subst! (φ := Modal.Axioms.Grz (.atom 0)) (s := λ _ => φ);
    apply Modal.Logic.sumNormal.mem₂!;
    apply Modal.Logic.iff_provable.mpr;
    simp;

instance : IL.smallestMC ⪯ IL.smallestMC := inferInstance

end Propositional.Logic


section

open Propositional.Formula (goedelTranslate)

lemma Modal.instModalCompanion_of_smallestMC_via_KripkeSemantics
  {IL : Propositional.Logic ℕ} (IC : Propositional.Kripke.FrameClass) (MC : Modal.Kripke.FrameClass)
  (hIC_MC : ∀ F ∈ IC, ⟨F.World, F.Rel⟩ ∈ MC)
  [Complete IL IC] [Sound IL.smallestMC MC]
  : ModalCompanion IL (IL.smallestMC) := Modal.instModalCompanion
  (by
    intro φ hφ;
    apply Modal.Logic.sumNormal.mem₂!;
    use φ;
    simpa;
  )
  (by
    intro φ;
    contrapose!;
    intro h;
    obtain ⟨F, hF, hF₂⟩ : ∃ F ∈ IC, ¬F ⊧ φ := Propositional.Kripke.exists_frame_of_not_validOnFrameClass $ (not_imp_not.mpr $ Complete.complete) h;
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
          exact h x F.refl;
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
      | _ => simp_all [Propositional.Formula.Kripke.Satisfies, Modal.Formula.Kripke.Satisfies];
    apply Sound.not_provable_of_countermodel (𝓜 := MC);
    apply Modal.Kripke.not_validOnFrameClass_of_exists_frame;
    use { World := F.World, Rel := F.Rel };
    constructor;
    . apply hIC_MC;
      exact hF;
    . apply Modal.Formula.Kripke.ValidOnFrame.not_of_exists_valuation_world;
      use V, x;
      exact (h₁ φ x).not.mp hφ;
  )

lemma Modal.instModalCompanion_of_largestMC_via_KripkeSemantics
  {IL : Propositional.Logic ℕ} (IC : Propositional.Kripke.FrameClass) (MC : Modal.Kripke.FrameClass)
  (hIC_MC : ∀ F ∈ IC, ⟨F.World, F.Rel⟩ ∈ MC)
  [Complete IL IC] [Sound IL.largestMC MC]
  : ModalCompanion IL (IL.largestMC) := Modal.instModalCompanion
  (by
    intro φ hφ;
    apply Modal.Logic.sumNormal.mem₁!;
    apply Modal.Logic.sumNormal.mem₂!;
    use φ;
    simpa;
  )
  (by
    intro φ;
    contrapose;
    intro h;
    obtain ⟨F, hF, hF₂⟩ : ∃ F ∈ IC, ¬F ⊧ φ := Propositional.Kripke.exists_frame_of_not_validOnFrameClass $ (not_imp_not.mpr $ Complete.complete) h;
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
          exact h x F.refl;
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
      | _ => simp_all [Propositional.Formula.Kripke.Satisfies, Modal.Formula.Kripke.Satisfies];
    apply Sound.not_provable_of_countermodel (𝓜 := MC);
    apply Modal.Kripke.not_validOnFrameClass_of_exists_frame;
    use { World := F.World, Rel := F.Rel };
    constructor;
    . apply hIC_MC;
      exact hF;
    . apply Modal.Formula.Kripke.ValidOnFrame.not_of_exists_valuation_world;
      use V, x;
      exact (h₁ φ x).not.mp hφ;
  )

end


namespace Modal

open Propositional.Formula (goedelTranslate)

variable {IL : Propositional.Logic ℕ}
variable {MS} [Entailment (Modal.Formula ℕ) MS]
variable {𝓜𝓢 : MS}  [Entailment.S4 𝓜𝓢]
variable {φ ψ χ : Propositional.Formula ℕ}

@[simp]
lemma goedelTranslated_efq : 𝓜𝓢 ⊢ (⊥ ➝ φ)ᵍ := by
  apply nec!;
  simp [goedelTranslate];

lemma goedelTranslated_axiomTc : 𝓜𝓢 ⊢ φᵍ ➝ □φᵍ := by
  induction φ using Propositional.Formula.rec' with
  | hfalsum => simp only [goedelTranslate, efq!];
  | hand φ ψ ihp ihq => exact C!_trans (CKK!_of_C!_of_C! ihp ihq) collect_box_and!
  | hor φ ψ ihp ihq => exact C!_trans (left_A!_intro (right_A!_intro_left ihp) (right_A!_intro_right ihq)) collect_box_or!
  | _ => simp only [goedelTranslate, axiomFour!];

lemma goedelTranslated_implyS : 𝓜𝓢 ⊢ (φ ➝ ψ ➝ φ)ᵍ := by
  exact nec! $ C!_trans goedelTranslated_axiomTc $ axiomK'! $ nec! $ imply₁!;

lemma goedelTranslated_implyK : 𝓜𝓢 ⊢ ((φ ➝ ψ ➝ χ) ➝ (φ ➝ ψ) ➝ φ ➝ χ)ᵍ := by
  apply nec! $ C!_trans (C!_trans (axiomK'! $ nec! ?b) axiomFour!) $ axiomK'! $ nec! $ C!_trans (axiomK'! $ nec! imply₂!) axiomK!;
  apply provable_iff_provable.mpr;
  apply deduct_iff.mpr;
  apply deduct_iff.mpr;
  have : [φᵍ, φᵍ ➝ □(ψᵍ ➝ χᵍ)] ⊢[𝓜𝓢] φᵍ := by_axm!;
  have : [φᵍ, φᵍ ➝ □(ψᵍ ➝ χᵍ)] ⊢[𝓜𝓢] (φᵍ ➝ □(ψᵍ ➝ χᵍ)) := by_axm!;
  have : [φᵍ, φᵍ ➝ □(ψᵍ ➝ χᵍ)] ⊢[𝓜𝓢] □(ψᵍ ➝ χᵍ) := (by assumption) ⨀ (by assumption);
  exact axiomT'! this;

lemma goedelTranslated_AndIntro : 𝓜𝓢 ⊢ (φ ➝ ψ ➝ φ ⋏ ψ)ᵍ := by
  exact nec! $ C!_trans goedelTranslated_axiomTc $ axiomK'! $ nec! $ and₃!

lemma goedelTranslated_OrElim : 𝓜𝓢 ⊢ (((φ ➝ χ) ➝ (ψ ➝ χ) ➝ (φ ⋎ ψ ➝ χ)))ᵍ := by
  exact nec! $ C!_trans axiomFour! $ axiomK'! $ nec! $ C!_trans (axiomK'! $ nec! $ or₃!) axiomK!;

lemma provable_goedelTranslated_of_provable
  (IH : Propositional.Hilbert ℕ) (𝓜𝓢 : MS) [Entailment.S4 𝓜𝓢]
  (hAx : ∀ φ ∈ IH.axiomInstances, 𝓜𝓢 ⊢ φᵍ)
  : IH ⊢ φ → 𝓜𝓢 ⊢ φᵍ := by
  intro h;
  induction h using Propositional.Hilbert.rec! with
  | @axm φ _ ih =>
    apply hAx;
    use φ;
    tauto;
  | mdp ihpq ihp =>
    exact axiomT'! $ axiomK''! ihpq $ nec! $ ihp;
  | verum => exact nec! C!_id;
  | andElimL => exact nec! and₁!;
  | andElimR => exact nec! and₂!;
  | orIntroL => exact nec! or₁!;
  | orIntroR => exact nec! or₂!;
  | K_intro => exact goedelTranslated_AndIntro;
  | orElim => exact goedelTranslated_OrElim;
  | implyS => exact goedelTranslated_implyS;
  | implyK => exact goedelTranslated_implyK;

end Modal

/-
lemma dp_of_mdp [ModalDisjunctive mH] [ModalCompanion iH mH] [Entailment.S4 mH] : iH ⊢ φ ⋎ ψ → iH ⊢ φ ∨ iH ⊢ ψ := by
    intro hpq;
    have : mH ⊢ □φᵍ ⋎ □ψᵍ := of_C!_of_C!_of_A! (right_A!_intro_left axiomTc_GTranslate!) (right_A!_intro_right axiomTc_GTranslate!) (by simpa using ModalCompanion.companion.mp hpq);
    cases ModalDisjunctive.modal_disjunctive this with
    | inl h => left; exact ModalCompanion.companion.mpr h;
    | inr h => right; exact ModalCompanion.companion.mpr h;

theorem disjunctive_of_modalDisjunctive [ModalDisjunctive mH] [ModalCompanion iH mH] [Entailment.S4 mH] : Disjunctive iH := ⟨dp_of_mdp (iH := iH) (mH := mH)⟩
-/

end LO
