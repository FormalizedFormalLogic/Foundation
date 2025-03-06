import Foundation.Modal.ModalCompanion.Basic
import Foundation.Propositional.Logic.WellKnown
import Foundation.Modal.Logic.WellKnown
import Foundation.Modal.Logic.Extension
import Foundation.Modal.Logic.Sublogic.Grz

namespace LO.Modal

open Entailment FiniteContext
open Propositional
open Propositional.Formula (goedelTranslate)
open Modal
open Modal.Kripke

namespace Hilbert

variable {IL : Propositional.Logic} {ML : Modal.Logic}
variable {IH : Propositional.Hilbert ℕ} {MH : Modal.Hilbert ℕ}
variable {φ ψ χ : Propositional.Formula ℕ}

variable [Entailment.S4 MH]

lemma goedelTranslated_axiomTc : MH ⊢! φᵍ ➝ □φᵍ := by
  induction φ using Propositional.Formula.rec' with
  | hfalsum => simp only [goedelTranslate, efq!];
  | hand φ ψ ihp ihq => exact imp_trans''! (and_replace! ihp ihq) collect_box_and!
  | hor φ ψ ihp ihq => exact imp_trans''! (or₃''! (imply_left_or'! ihp) (imply_right_or'! ihq)) collect_box_or!
  | _ => simp only [goedelTranslate, axiomFour!];

lemma goedelTranslated_implyS : MH ⊢! (φ ➝ ψ ➝ φ)ᵍ := by
  exact nec! $ imp_trans''! goedelTranslated_axiomTc $ axiomK'! $ nec! $ imply₁!;

lemma goedelTranslated_implyK : MH ⊢! ((φ ➝ ψ ➝ χ) ➝ (φ ➝ ψ) ➝ φ ➝ χ)ᵍ := by
  apply nec! $ imp_trans''! (imp_trans''! (axiomK'! $ nec! ?b) axiomFour!) $ axiomK'! $ nec! $ imp_trans''! (axiomK'! $ nec! imply₂!) axiomK!;
  apply provable_iff_provable.mpr;
  apply deduct_iff.mpr;
  apply deduct_iff.mpr;
  have : [φᵍ, φᵍ ➝ □(ψᵍ ➝ χᵍ)] ⊢[MH]! φᵍ := by_axm!;
  have : [φᵍ, φᵍ ➝ □(ψᵍ ➝ χᵍ)] ⊢[MH]! (φᵍ ➝ □(ψᵍ ➝ χᵍ)) := by_axm!;
  have : [φᵍ, φᵍ ➝ □(ψᵍ ➝ χᵍ)] ⊢[MH]! □(ψᵍ ➝ χᵍ) := (by assumption) ⨀ (by assumption);
  exact axiomT'! this;

lemma goedelTranslated_AndIntro : MH ⊢! (φ ➝ ψ ➝ φ ⋏ ψ)ᵍ := by
  exact nec! $ imp_trans''! goedelTranslated_axiomTc $ axiomK'! $ nec! $ and₃!

lemma goedelTranslated_OrElim : MH ⊢! (((φ ➝ χ) ➝ (ψ ➝ χ) ➝ (φ ⋎ ψ ➝ χ)))ᵍ := by
  exact nec! $ imp_trans''! axiomFour! $ axiomK'! $ nec! $ imp_trans''! (axiomK'! $ nec! $ or₃!) axiomK!;

lemma provable_GoedelTranslated_Modal_of_provable_Superint
  (IH : Propositional.Hilbert ℕ) (MH : Modal.Hilbert ℕ) [Entailment.S4 MH]
  (hAx : ∀ φ ∈ IH.axiomInstances, MH ⊢! φᵍ)
  : IH ⊢! φ → MH ⊢! φᵍ := by
  intro h;
  induction h using Propositional.Hilbert.Deduction.rec! with
  | maxm ih => apply hAx; assumption;
  | mdp ihpq ihp =>
    exact axiomT'! $ axiomK''! (ihpq) $ nec! $ ihp;
  | verum => exact nec! imp_id!;
  | andElimL => exact nec! and₁!;
  | andElimR => exact nec! and₂!;
  | orIntroL => exact nec! or₁!;
  | orIntroR => exact nec! or₂!;
  | andIntro => exact goedelTranslated_AndIntro;
  | orElim => exact goedelTranslated_OrElim;
  | implyS => exact goedelTranslated_implyS;
  | implyK => exact goedelTranslated_implyK;

end Hilbert


section S4

lemma Logic.gS4_of_Int : φ ∈ Logic.Int → φᵍ ∈ Logic.S4 := by
  apply Hilbert.provable_GoedelTranslated_Modal_of_provable_Superint Hilbert.Int Hilbert.S4;
  rintro _ ⟨φ, ⟨_⟩, ⟨s, rfl⟩⟩;
  apply nec! $ efq!;

lemma Logic.S4.is_minimamMC_of_Int : Logic.S4 = Logic.Int.minimamMC := by
  ext φ;
  constructor;
  . intro hφ;
    induction hφ using Hilbert.Deduction.rec! with
    | maxm h =>
      rcases (by simpa using h) with (⟨s, rfl⟩ | ⟨s, rfl⟩ | ⟨s, rfl⟩);
      . apply Logic.sumNormal.mem₁; simp;
      . apply Logic.sumNormal.mem₁; simp;
      . apply Logic.sumNormal.mem₁; simp;
    | mdp => apply Logic.sumNormal.mdp <;> assumption;
    | nec => apply Logic.sumNormal.nec; assumption;
    | _ => apply Logic.sumNormal.mem₁; simp;
  . intro hφ;
    induction hφ with
    | mem₁ h => tauto;
    | mdp hφ hψ ihφψ ihψ => apply Modal.Logic.mdp ihφψ ihψ;
    | subst h ih => apply Modal.Logic.subst ih;
    | nec h ih => apply Modal.Logic.nec ih;
    | mem₂ h =>
      rcases h with ⟨φ, hφ, rfl⟩;
      apply Logic.gS4_of_Int hφ;

instance : ModalCompanion Logic.Int Logic.S4 := by
  rw [Logic.S4.is_minimamMC_of_Int];
  exact Modal.instModalCompanion_of_minimamMC_via_KripkeSemantics
    (IC := Propositional.Kripke.AllFrameClass)
    (MC := Modal.Kripke.ReflexiveTransitiveFrameClass)
    (by
      intro φ;
      constructor;
      . apply Propositional.Hilbert.Int.Kripke.sound.sound;
      . apply Propositional.Hilbert.Int.Kripke.complete.complete;
    )
    (by
      rw [←Logic.S4.is_minimamMC_of_Int];
      intro φ;
      constructor;
      . apply Modal.Hilbert.S4.Kripke.sound.sound;
      . apply Modal.Hilbert.S4.Kripke.complete.complete;
    )
    (fun F hF => ⟨F.rel_refl, F.rel_trans⟩);


end S4



section Grz

lemma Logic.gGrz_of_Int : φ ∈ Logic.Int → φᵍ ∈ Logic.Grz := by
  intro h;
  exact S4_ssubset_Grz.1 $ Logic.gS4_of_Int h;

lemma Logic.Grz.is_maximalMC_of_Int : Logic.Grz = Logic.Int.maximalMC := by
  ext φ;
  constructor;
  . intro hφ;
    induction hφ using Hilbert.Deduction.rec! with
    | maxm h =>
      rcases (by simpa using h) with (⟨s, rfl⟩ | ⟨s, rfl⟩);
      . apply Logic.sumNormal.mem₁;
        apply Logic.sumNormal.mem₁;
        simp;
      . apply Logic.sumNormal.subst (φ := □(□((.atom 0) ➝ □(.atom 0)) ➝ (.atom 0)) ➝ (.atom 0)) (s := s);
        apply Logic.sumNormal.mem₂;
        simp;
    | mdp => apply Logic.sumNormal.mdp <;> assumption;
    | nec => apply Logic.sumNormal.nec; assumption;
    | _ => apply Logic.sumNormal.mem₁; apply Logic.sumNormal.mem₁; simp;
  . intro hφ;
    induction hφ with
    | mem₁ h =>
      apply S4_ssubset_Grz.1;
      rwa [Logic.S4.is_minimamMC_of_Int]
    | mdp hφ hψ ihφψ ihψ => apply Modal.Logic.mdp ihφψ ihψ;
    | subst h ih => apply Modal.Logic.subst ih;
    | nec h ih => apply Modal.Logic.nec ih;
    | mem₂ h =>
      rcases h with ⟨φ, hφ, rfl⟩; simp;

instance : ModalCompanion Logic.Int Logic.Grz := by
  rw [Logic.Grz.is_maximalMC_of_Int];
  exact Modal.instModalCompanion_of_maximalMC_via_KripkeSemantics
    (IC := Propositional.Kripke.AllFiniteFrameClass)
    (MC := Modal.Kripke.ReflexiveTransitiveAntiSymmetricFiniteFrameClass)
    (by
      intro φ;
      constructor;
      . apply Propositional.Hilbert.Int.Kripke.sound_finite.sound;
      . apply Propositional.Hilbert.Int.Kripke.complete_finite.complete;
    )
    (by
      rw [←Logic.Grz.is_maximalMC_of_Int];
      intro φ;
      constructor;
      . apply Modal.Hilbert.Grz.Kripke.sound.sound;
      . apply Modal.Hilbert.Grz.Kripke.complete.complete;
    )
    (by
      rintro F hF;
      use ({ World := F.World, Rel := F.Rel, world_finite := by tauto; });
      simp only [Set.mem_setOf_eq, and_true];
      refine ⟨F.rel_refl, F.rel_trans, F.rel_antisymm⟩;
    )

end Grz

end LO.Modal
