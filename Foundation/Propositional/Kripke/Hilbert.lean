module

public import Foundation.Propositional.Hilbert.Standard.Basic
public import Foundation.Propositional.Kripke.Basic

@[expose] public section

namespace LO.Propositional

open Kripke
open Formula
open Formula.Kripke

namespace Modal.Kripke

variable {Ax Ax₁ Ax₂ : Axiom ℕ} {Γ : Set (Formula ℕ)} {φ : Formula ℕ}

section FrameClass

variable {C C₁ C₂ : Kripke.FrameClass}

lemma soundness_of_validates_axioms (hV : C.Validates Ax) : (Hilbert.Standard Ax) ⊢ φ → C ⊧ φ := by
  intro hφ F hF;
  induction hφ with
  | verum => apply ValidOnFrame.top;
  | implyS => apply ValidOnFrame.implyK;
  | implyK => apply ValidOnFrame.implyS;
  | andElimL => apply ValidOnFrame.andElim₁;
  | andElimR => apply ValidOnFrame.andElim₂;
  | andIntro => apply ValidOnFrame.andInst₃;
  | orIntroL => apply ValidOnFrame.orInst₁;
  | orIntroR => apply ValidOnFrame.orInst₂;
  | orElim => apply ValidOnFrame.orElim;
  | mdp => exact ValidOnFrame.mdp (by assumption) (by assumption);
  | axm s hi =>
    apply ValidOnFrame.subst;
    apply hV F hF _ hi;

lemma instSound_of_validates_axioms (hV : C.Validates Ax) : Sound (Hilbert.Standard Ax) C := ⟨fun {_} => soundness_of_validates_axioms hV⟩

lemma consistent_of_sound_frameclass (C : FrameClass) (hC : Set.Nonempty C) [sound : Sound (Hilbert.Standard Ax) C] : Entailment.Consistent (Hilbert.Standard Ax) := by
  apply Entailment.Consistent.of_unprovable (φ := ⊥);
  apply not_imp_not.mpr sound.sound;
  apply Semantics.set_models_iff.not.mpr;
  push_neg;
  obtain ⟨F, hF⟩ := hC;
  use F;
  constructor;
  . assumption;
  . simp;

/-
lemma finite_sound_of_sound (sound : Sound H.logic C) : Sound H.logic ({ F | F ∈ C ∧ Finite F }) := ⟨by
  rintro φ hφ F ⟨hF₁, _⟩;
  exact sound.sound hφ hF₁;
⟩
-/

lemma weakerThan_of_subset_frameClass (C₁ C₂ : FrameClass) (hC : C₂ ⊆ C₁) [Sound (Hilbert.Standard Ax₁) C₁] [Complete (Hilbert.Standard Ax₂) C₂] : (Hilbert.Standard Ax₁) ⪯ (Hilbert.Standard Ax₂) := by
  apply Entailment.weakerThan_iff.mpr;
  intro φ hφ;
  apply Complete.complete (𝓜 := C₂);
  intro F hF;
  apply Sound.sound (𝓢 := (Hilbert.Standard Ax₁)) (𝓜 := C₁) hφ;
  apply hC hF;

/-
lemma eq_Hilbert_Logic_KripkeFrameClass_Logic [sound : Sound H C] [complete : Complete H C] : H.logic = C.logic := by
  ext φ;
  constructor;
  . intro h;
    apply sound.sound;
    simpa;
  . intro h;
    simpa using complete.complete h;

instance [Sound H C] : Sound H.logic C := by
  constructor;
  intro φ hφ;
  apply Sound.sound $ by simpa using hφ;

instance [Complete H C] : Complete H.logic C := by
  constructor;
  intro φ hφ;
  simpa using Complete.complete hφ;
-/

end FrameClass

end Modal.Kripke

end LO.Propositional
end
