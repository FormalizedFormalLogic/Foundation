import Foundation.Propositional.Hilbert.Basic
import Foundation.Propositional.Kripke.Basic

namespace LO.Propositional

open Kripke
open Formula
open Formula.Kripke


lemma Logic.eq_Hilbert_Logic_KripkeFrameClass_Logic {H : Hilbert ℕ} {C : FrameClass}
  [sound : Sound H C] [complete : Complete H C]
  : H.logic = C.logic := by
  ext φ;
  constructor;
  . exact sound.sound;
  . exact complete.complete;


namespace Hilbert.Kripke

variable {H : Hilbert ℕ} {Γ : Set (Formula ℕ)} {φ : Formula ℕ}

section

variable {C : Kripke.FrameClass}

lemma soundness_of_validates_axiomInstances (hV : C.Validates H.axiomInstances) : H ⊢! φ → C ⊧ φ := by
  intro hφ F hF;
  induction hφ using Hilbert.Deduction.rec! with
  | verum => apply ValidOnFrame.top;
  | implyS => apply ValidOnFrame.imply₁;
  | implyK => apply ValidOnFrame.imply₂;
  | andElimL => apply ValidOnFrame.andElim₁;
  | andElimR => apply ValidOnFrame.andElim₂;
  | K_intro => apply ValidOnFrame.andInst₃;
  | orIntroL => apply ValidOnFrame.orInst₁;
  | orIntroR => apply ValidOnFrame.orInst₂;
  | orElim => apply ValidOnFrame.orElim;
  | mdp => exact ValidOnFrame.mdp (by assumption) (by assumption);
  | maxm hi =>
    obtain ⟨ψ, h, ⟨s, rfl⟩⟩ := hi;
    apply hV F hF (ψ⟦s⟧);
    use ψ;
    constructor
    . assumption;
    . use s;

lemma validates_axioms_of_validates_axiomInstances (hV : C.Validates H.axioms) : C.Validates H.axiomInstances := by
  rintro F hF _ ⟨φ, hφ, ⟨s, rfl⟩⟩;
  exact ValidOnFrame.subst $ hV F hF φ hφ;

instance instSound_of_validates_axioms (hV : C.Validates H.axioms) : Sound H C := ⟨fun {_} =>
  soundness_of_validates_axiomInstances (validates_axioms_of_validates_axiomInstances hV)
⟩

lemma consistent_of_sound_frameclass (C : FrameClass) (hC : Set.Nonempty C) [sound : Sound H C] : Entailment.Consistent H := by
  apply Entailment.Consistent.of_unprovable (f := ⊥);
  apply not_imp_not.mpr sound.sound;
  apply Semantics.set_models_iff.not.mpr;
  push_neg;
  obtain ⟨F, hF⟩ := hC;
  use F;
  constructor;
  . assumption;
  . simp;

lemma finite_sound_of_sound (sound : Sound H C) : Sound H ({ F | F ∈ C ∧ Finite F }) := ⟨by
  rintro φ hφ F ⟨hF₁, _⟩;
  exact sound.sound hφ hF₁;
⟩

end

end Hilbert.Kripke

end LO.Propositional
