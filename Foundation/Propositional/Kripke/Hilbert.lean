import Foundation.Propositional.Hilbert.Basic
import Foundation.Propositional.Kripke.Basic

namespace LO.Propositional

open Kripke
open Formula
open Formula.Kripke

namespace Hilbert.Kripke

variable {H H₁ H₂ : Hilbert ℕ} {Γ : Set (Formula ℕ)} {φ : Formula ℕ}

section FrameClass

variable {C C₁ C₂ : Kripke.FrameClass}

lemma soundness_of_validates_axioms (hV : C.Validates H.axioms) : H ⊢! φ → C ⊧ φ := by
  intro hφ F hF;
  induction hφ with
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
  | axm s hi =>
    apply ValidOnFrame.subst;
    apply hV F hF _ hi;

lemma instSound_of_validates_axioms (hV : C.Validates H.axioms) : Sound H C := ⟨fun {_} => soundness_of_validates_axioms hV⟩

lemma consistent_of_sound_frameclass (C : FrameClass) (hC : Set.Nonempty C) [sound : Sound H C] : Entailment.Consistent H := by
  apply Entailment.Consistent.of_unprovable (φ := ⊥);
  apply not_imp_not.mpr sound.sound;
  apply Semantics.set_models_iff.not.mpr;
  push_neg;
  obtain ⟨F, hF⟩ := hC;
  use F;
  constructor;
  . assumption;
  . simp;

lemma finite_sound_of_sound (sound : Sound H.logic C) : Sound H.logic ({ F | F ∈ C ∧ Finite F }) := ⟨by
  rintro φ hφ F ⟨hF₁, _⟩;
  exact sound.sound hφ hF₁;
⟩

lemma weakerThan_of_subset_frameClass (C₁ C₂ : FrameClass) (hC : C₂ ⊆ C₁) [Sound H₁ C₁] [Complete H₂ C₂] : H₁ ⪯ H₂ := by
  apply Entailment.weakerThan_iff.mpr;
  intro φ hφ;
  apply Complete.complete (𝓜 := C₂);
  intro F hF;
  apply Sound.sound (𝓢 := H₁) (𝓜 := C₁) hφ;
  apply hC hF;

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


section

open Lean Meta Elab Command

syntax (name := generatePropositionalKripke) "propositional_kripke " term : command

/-- WOW -/
@[command_elab generatePropositionalKripke]
def elabGenerateFinNatCoe : CommandElab
| `(propositional_kripke $H:term $C:term) => do
  let instSound ← `(instance : Sound $H $C := inferInstance)
  let instComplete ← `(instance : Complete $H $C := inferInstance)

  elabCommand instSound
  elabCommand instComplete
| _ => throwUnsupportedSyntax

end

end FrameClass

end Hilbert.Kripke

end LO.Propositional
