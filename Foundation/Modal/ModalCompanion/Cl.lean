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

noncomputable instance : Entailment.S4 Hilbert.S5 where
  Four φ := Logic.S4_ssubset_S5.1 (by simp) |>.some;

open Formula.Kripke in
lemma mem_gAxiomFive_smallestMC_of_Cl : (Axioms.Five (.atom 0)) ∈ Logic.Cl.smallestMC := by
  have : □(.atom 0) ⋎ □(∼□(.atom 0)) ∈ Logic.Cl.smallestMC := by
    apply Logic.sumNormal.mem₂;
    use Axioms.LEM (.atom 0);
    constructor;
    . simp;
    . tauto;
  apply Propositional.Logic.smallestMC.mdp_S4 ?_
    $ @Logic.subst Logic.Cl.smallestMC (by sorry) _ (λ _ => ∼(.atom 0)) this;
  apply imp_trans''! ?_ imply_of_not_or!;
  apply or_replace!;
  . apply contra₁'!;
    exact diaDuality_mp!;
  . apply axiomK'!;
    apply nec!;
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
      . exact Logic.sumNormal.subst $ mem_gAxiomFive_smallestMC_of_Cl;
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

end Logic

end S5


end LO.Modal
