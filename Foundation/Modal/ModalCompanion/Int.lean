import Foundation.Modal.ModalCompanion.Basic
import Foundation.Propositional.Logic.WellKnown
import Foundation.Modal.Logic.WellKnown
import Foundation.Modal.Logic.Sublogic

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

lemma Logic.Int_of_gS4 : φᵍ ∈ Logic.S4 → φ ∈ Logic.Int := by
  contrapose;
  rw [Logic.Int.eq_AllKripkeFrameClass_Logic, Logic.S4.eq_ReflexiveTransitiveKripkeFrameClass_Logic];
  intro h;
  obtain ⟨M, w, hM, hp⟩ := Propositional.Formula.Kripke.ValidOnFrameClass.exists_model_world_of_not h;
  have h₁ : ∀ ψ x, Propositional.Formula.Kripke.Satisfies M x ψ ↔ (Modal.Formula.Kripke.Satisfies ⟨⟨M.World, M.Rel⟩, M.Val⟩ x (ψᵍ)) := by
    intro ψ x;
    induction ψ using Propositional.Formula.rec' generalizing x with
    | hatom a =>
      unfold goedelTranslate;
      constructor;
      . intro _ _ h;
        exact M.Val.hereditary h $ by assumption;
      . intro h;
        exact h x (M.rel_refl x);
    | hfalsum =>  rfl;
    | hor φ ψ ihp ihq =>
      unfold goedelTranslate;
      constructor;
      . rintro (hp | hq);
        . apply Formula.Kripke.Satisfies.or_def.mpr; left;
          exact ihp x |>.mp hp;
        . apply Formula.Kripke.Satisfies.or_def.mpr; right;
          exact ihq x |>.mp hq;
      . intro h;
        rcases Formula.Kripke.Satisfies.or_def.mp h with (hp | hq)
        . left; exact ihp x |>.mpr hp;
        . right; exact ihq x |>.mpr hq;
    | _ => simp_all [goedelTranslate, Propositional.Formula.Kripke.Satisfies, Modal.Formula.Kripke.Satisfies];
  apply Formula.Kripke.ValidOnFrameClass.not_of_exists_model;
  use {World := M.World, Rel := M.Rel, Val := M.Val};
  constructor;
  . constructor;
    . exact M.rel_refl;
    . exact M.rel_trans;
  . apply Formula.Kripke.ValidOnModel.not_of_exists_world;
    use w;
    exact (h₁ φ w).not.mp hp;

instance : ModalCompanion Logic.Int Logic.S4 := Modal.instModalCompanion Logic.gS4_of_Int Logic.Int_of_gS4

end S4



section Grz

lemma Logic.gGrz_of_Int : φ ∈ Logic.Int → φᵍ ∈ Logic.Grz := by
  intro h;
  exact S4_ssubset_Grz.1 $ Logic.gS4_of_Int h;

lemma Logic.Int_of_gGrz : φᵍ ∈ Logic.Grz → φ ∈ Logic.Int := by
  contrapose;
  rw [Logic.Int.eq_AllFiniteKripkeFrameClass_Logic, Logic.Grz.eq_ReflexiveTransitiveAntiSymmetricFiniteKripkeFrameClass_Logic];
  intro h;
  obtain ⟨M, w, hM, hp⟩ := Propositional.Formula.Kripke.ValidOnFrameClass.exists_model_world_of_not h;
  have h₁ : ∀ ψ x, Propositional.Formula.Kripke.Satisfies M x ψ ↔ (Modal.Formula.Kripke.Satisfies ⟨⟨M.World, M.Rel⟩, M.Val⟩ x (ψᵍ)) := by
    intro ψ x;
    induction ψ using Propositional.Formula.rec' generalizing x with
    | hatom a =>
      unfold goedelTranslate;
      constructor;
      . intro _ _ h;
        exact M.Val.hereditary h $ by assumption;
      . intro h;
        exact h x (M.rel_refl x);
    | hfalsum =>  rfl;
    | hor φ ψ ihp ihq =>
      unfold goedelTranslate;
      constructor;
      . rintro (hp | hq);
        . apply Formula.Kripke.Satisfies.or_def.mpr; left;
          exact ihp x |>.mp hp;
        . apply Formula.Kripke.Satisfies.or_def.mpr; right;
          exact ihq x |>.mp hq;
      . intro h;
        rcases Formula.Kripke.Satisfies.or_def.mp h with (hp | hq)
        . left; exact ihp x |>.mpr hp;
        . right; exact ihq x |>.mpr hq;
    | _ => simp_all [goedelTranslate, Propositional.Formula.Kripke.Satisfies, Modal.Formula.Kripke.Satisfies];
  apply Formula.Kripke.ValidOnFrameClass.not_of_exists_model;
  use {World := M.World, Rel := M.Rel, Val := M.Val};
  constructor;
  . simp [ReflexiveTransitiveAntiSymmetricFiniteFrameClass, FiniteFrameClass.toFrameClass];
    use ({ World := M.World, Rel := M.Rel, world_finite := by tauto; });
    simp;
    refine ⟨?_, ?_, ?_⟩;
    . exact M.rel_refl;
    . exact M.rel_trans;
    . exact M.rel_antisymm;
  . apply Formula.Kripke.ValidOnModel.not_of_exists_world;
    use w;
    exact (h₁ φ w).not.mp hp;

instance : ModalCompanion Logic.Int Logic.Grz := Modal.instModalCompanion Logic.gGrz_of_Int Logic.Int_of_gGrz

end Grz

end LO.Modal
