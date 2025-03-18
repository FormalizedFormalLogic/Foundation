import Foundation.Modal.ModalCompanion.Int
import Foundation.Modal.Logic.Sublogic.ModalCube
import Foundation.Modal.Kripke.Hilbert.S5


namespace LO.Modal

open Entailment FiniteContext
open Propositional
open Propositional.Formula (goedelTranslate)
open Propositional.Formula (atom)
open Modal
open Modal.Kripke

section S5

namespace Logic

open Formula.Kripke in
lemma S5.is_smallestMC_of_Cl.lemma₁ : (◇□(.atom 0) ➝ □(.atom 0)) ∈ Logic.Cl.smallestMC := by
  have : □(.atom 0) ⋎ □(∼□(.atom 0)) ∈ Logic.Cl.smallestMC := by
    apply Logic.sumNormal.mem₂;
    use Axioms.LEM (.atom 0);
    constructor;
    . simp;
    . tauto;
  apply Propositional.Logic.smallestMC.mdp_S4 ?_ this;
  apply imp_trans''! ?_ imply_of_not_or!;
  apply imp_trans''! ?_ or_comm!;
  apply or_replace!;
  . simp;
  . apply contra₁'!;
    exact diaDuality_mp!;

lemma S5.is_smallestMC_of_Cl : Logic.S5 = Logic.Cl.smallestMC := by
  ext φ;
  constructor;
  . intro hφ;
    induction hφ using Hilbert.Deduction.rec! with
    | maxm h =>
      rcases (by simpa using h) with (⟨s, rfl⟩ | ⟨s, rfl⟩ | ⟨s, rfl⟩);
      . apply Logic.sumNormal.mem₁; simp;
      . apply Logic.sumNormal.mem₁; simp;
      . have := Logic.sumNormal.subst (s := λ _ => ∼(s 0)) $ S5.is_smallestMC_of_Cl.lemma₁;
        apply Propositional.Logic.smallestMC.mdp_S4 ?_ this;
        simp;
        apply imp_trans''! ?_ imply_of_not_or!;
        apply imp_trans''! not_or_of_imply! ?_;
        apply imp_trans''! ?_ or_comm!;
        apply or_replace!;
        . apply contra₂'!;
          exact diaDuality_mp!;
        . apply contra₁'!;
          exact diaDuality_mp!;
    | mdp => apply Logic.sumNormal.mdp <;> assumption;
    | nec => apply Logic.sumNormal.nec; assumption;
    | _ => apply Logic.sumNormal.mem₁; simp;
  . intro hφ;
    induction hφ with
    | mdp hφ hψ ihφψ ihψ => apply Modal.Logic.mdp ihφψ ihψ;
    | subst h ih => apply Modal.Logic.subst ih;
    | nec h ih => apply Modal.Logic.nec ih;
    | mem₁ h => apply Logic.S4_ssubset_S5.1 h;
    | mem₂ h =>
      rcases h with ⟨φ, hφ, rfl⟩;
      haveI : Hilbert.S4 ⊢! ◇φᵍ := iff_provable_Cl_provable_dia_gS4.mp hφ;
      haveI : Hilbert.S4 ⊢! ◇□φᵍ := (diaK'! $ Hilbert.goedelTranslated_axiomTc) ⨀ this;
      exact rm_diabox'! $ Logic.S4_ssubset_S5.1 this;

instance modalCompanion_Cl_S5 : ModalCompanion Logic.Cl Logic.S5 := by
  rw [Logic.S5.is_smallestMC_of_Cl];
  exact Modal.instModalCompanion_of_smallestMC_via_KripkeSemantics
    (IC := Propositional.Kripke.FrameClass.euclidean)
    (MC := Modal.Kripke.FrameClass.refl_eucl)
    (by rw [Propositional.Logic.Cl.Kripke.eq_euclidean])
    (by rw [←Logic.S5.is_smallestMC_of_Cl, ←Logic.S5.eq_ReflexiveEuclideanKripkeFrameClass_Logic])
    (by
      simp;
      intro F hF;
      constructor;
      . infer_instance;
      . infer_instance;
    );

end Logic

end S5


end LO.Modal
