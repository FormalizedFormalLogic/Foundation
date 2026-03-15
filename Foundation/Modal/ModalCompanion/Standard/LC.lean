module

public import Foundation.Logic.Embedding
public import Foundation.Modal.ModalCompanion.Standard.Int
public import Foundation.Modal.Boxdot.GLPoint3_GrzPoint3
-- public import Foundation.Propositional.Kripke.Logic.LC

@[expose] public section

namespace LO.Modal

open LO.Entailment LO.Entailment.FiniteContext LO.Modal.Entailment
open Propositional
open Propositional.Formula (atom gödelTranslate)
open Propositional.Logic (smallestMC largestMC)
open Modal
open Modal.Kripke
open Modal.Formula.Kripke

@[simp]
lemma S4.CCLL_CCL : Modal.S4 ⊢ □(□φ 🡒 □ψ) 🡒 □(□φ 🡒 ψ) := by
  apply Complete.complete (𝓜 := FrameClass.S4);
  rintro F ⟨_, _⟩ V x h₁ y Rxy h₂;
  apply @h₁ y Rxy h₂;
  apply Std.Refl.refl;

instance : Entailment.HasAxiomPoint3 (smallestMC Propositional.LC) where
  Point3 φ ψ := by
    constructor;
    apply Modal.Logic.iff_provable.mp;
    apply Modal.Logic.subst (L := (smallestMC Propositional.LC)) (φ := Modal.Axioms.Point3 (.atom 0) (.atom 1)) (s := λ a => match a with | 0 => φ | 1 => ψ | _ => .atom a);
    have : (smallestMC Propositional.LC) ⊢ □(□.atom 0 🡒 □.atom 1) ⋎ □(□.atom 1 🡒 □.atom 0) := by
      apply Logic.sumNormal.mem₂!;
      use Axioms.Dummett (.atom 0) (.atom 1);
      constructor;
      . apply Propositional.Logic.iff_provable.mp;
        simp;
      . tauto;
    apply ?_ ⨀ this;
    apply CAA!_of_C!_of_C! <;>
    . apply Entailment.WeakerThan.pbl (𝓢 := Modal.S4);
      simp;

namespace S4Point3

lemma gödelTranslated_axiomDummett : Modal.S4Point3 ⊢ □(□ψᵍ 🡒 χᵍ) 🡒 □(ψᵍ 🡒 χᵍ) := by
  apply axiomK'!;
  apply nec!;
  apply C!_swap;
  apply deduct'!;
  apply deduct!;
  have h₁ : [□ψᵍ 🡒 χᵍ, ψᵍ] ⊢[Modal.S4Point3] ψᵍ 🡒 □ψᵍ := of'! $ gödelTranslated_axiomTc;
  have h₂ : [□ψᵍ 🡒 χᵍ, ψᵍ] ⊢[Modal.S4Point3] ψᵍ := by_axm!;
  have h₃ : [□ψᵍ 🡒 χᵍ, ψᵍ] ⊢[Modal.S4Point3] □ψᵍ 🡒 χᵍ := by_axm!;
  exact h₃ ⨀ (h₁ ⨀ h₂);

instance : Modal.S4Point3 ≊ Propositional.LC.smallestMC := by
  apply Logic.equiv_of_provable;
  intro φ;
  constructor;
  . intro hφ;
    induction hφ using Modal.Hilbert.Normal.rec! with
    | axm s h =>
      rcases h with (rfl | rfl | rfl | rfl) <;> simp;
    | mdp ihφψ ihφ => exact ihφψ ⨀ ihφ;
    | nec ihφ => exact nec! ihφ;
    | _ => simp;
  . intro hφ;
    induction hφ using Logic.sumNormal.rec! with
    | mem₁ h => apply WeakerThan.pbl h;
    | mdp ihφψ ihψ => exact ihφψ ⨀ ihψ;
    | nec ihφ => exact nec! ihφ;
    | subst ihφ => apply Logic.subst _ ihφ;
    | mem₂ h =>
      rcases h with ⟨φ, hφ, rfl⟩;
      apply provable_gödelTranslated_of_provable ?_ (Propositional.Logic.iff_provable.mpr hφ);
      rintro _ ⟨_, (rfl | rfl), ⟨s, rfl⟩⟩;
      . simp;
      . apply A!_replace axiomPoint3! <;>
        apply S4Point3.gödelTranslated_axiomDummett;

lemma eq_smallestMC_of_KC : Modal.S4Point3 = Propositional.LC.smallestMC := Logic.eq_of_equiv

instance : Sound Propositional.LC.smallestMC FrameClass.S4Point3 := Kripke.sound_frameClass_of_equiv Modal.S4Point3 Propositional.LC.smallestMC

instance : ModalCompanion Propositional.LC Modal.S4Point3 := by
  apply eq_smallestMC_of_KC ▸ Modal.instModalCompanion_of_smallestMC_via_KripkeSemantics
    (IL := Propositional.LC)
    (IC := Propositional.Kripke.FrameClass.LC)
    (MC := Modal.Kripke.FrameClass.S4Point3)
  rintro F hF;
  simp_all only [Set.mem_setOf_eq];
  constructor;

end S4Point3


instance : Propositional.LC.smallestMC ⪯ Modal.GrzPoint3 := calc
  _ ≊ Modal.S4Point3  := by symm; infer_instance;
  _ ⪯ Modal.GrzPoint3 := inferInstance



section GrzPoint3

instance : Modal.GrzPoint3 ≊ Propositional.LC.largestMC := by
  apply Logic.equiv_of_provable;
  intro φ;
  constructor;
  . intro hφ;
    induction hφ using Modal.Hilbert.Normal.rec! with
    | axm _ h =>
      rcases h with (rfl | rfl | rfl);
      . simp;
      . simp;
      . apply WeakerThan.pbl (𝓢 := Propositional.LC.smallestMC); simp;
    | mdp ihφψ ihψ => exact ihφψ ⨀ ihψ;
    | nec ihφ => exact nec! ihφ;
    | _ => apply Logic.sumNormal.mem₁!; simp;
  . intro hφ;
    induction hφ using Logic.sumNormal.rec! with
    | mdp ihφψ ihψ => exact ihφψ ⨀ ihψ;
    | subst ih => apply Logic.subst _ ih;
    | nec ih => apply nec! ih;
    | mem₁ h => apply WeakerThan.pbl h;
    | mem₂ h => rcases h with ⟨φ, hφ, rfl⟩; simp;

lemma is_largestMC_of_LC : Modal.GrzPoint3 = Propositional.LC.largestMC := Logic.eq_of_equiv

instance : Sound Propositional.LC.largestMC FrameClass.finite_GrzPoint3 := Kripke.sound_frameClass_of_equiv Modal.GrzPoint3 Propositional.LC.largestMC

instance : ModalCompanion Propositional.LC Modal.GrzPoint3 := by
  apply is_largestMC_of_LC ▸ Modal.instModalCompanion_of_largestMC_via_KripkeSemantics
    Propositional.Kripke.FrameClass.finite_LC
    ({ F : Frame | F.IsFiniteGrzPoint3' })
  rintro F hF;
  simp_all only [Set.mem_setOf_eq];
  exact {}

end GrzPoint3


section boxdot

theorem embedding_LC_GLPoint3 {φ : Propositional.Formula ℕ} : Propositional.LC ⊢ φ ↔ Modal.GLPoint3 ⊢ φᵍᵇ :=
  Iff.trans ModalCompanion.companion iff_boxdot_GLPoint3_GrzPoint3.symm

instance : Entailment.FaithfullyEmbeddable Propositional.LC Modal.GLPoint3 where
  prop := ⟨(·ᵍᵇ), fun _ ↦ embedding_LC_GLPoint3.symm⟩

end boxdot


end LO.Modal
end
