import Logic.Modal.Standard.Deduction
import Logic.Modal.Standard.Kripke.Semantics

namespace LO.Modal.Standard.Kripke

variable {W α : Type*}
variable {Λ : AxiomSet α}
variable [Inhabited α]

open Deduction
open Formula Formula.Kripke

lemma sound_on_frameclass (d : Λ ⊢ p) : 𝔽(Λ) ⊧ p := by
  induction d with
  | maxm h => exact validOnAxiomSetFrameClass_axiom h;
  | mdp _ _ ihpq ihp =>
    intro W _ F hF V w;
    exact (Semantics.Tarski.realize_imp.mp $ ihpq W F hF V w) (ihp W F hF V w);
  | nec _ ih =>
    intro W _ F hF V w w' _;
    exact ih W F hF V w';
  | disj₃ =>
    simp_all [ValidOnFrameClass, ValidOnFrame, ValidOnModel];
    intros; rename_i hpr hqr hpq;
    cases hpq with
    | inl hp => exact hpr hp;
    | inr hq => exact hqr hq;
  | _ => simp_all [ValidOnFrameClass, ValidOnFrame, ValidOnModel];

lemma sound!_on_frameclass : Λ ⊢! p → 𝔽(Λ) ⊧ p := λ ⟨d⟩ => sound_on_frameclass d

instance : Sound Λ (𝔽(Λ)) := ⟨sound!_on_frameclass⟩

lemma unprovable_bot [ne : FrameClass.Nonempty 𝔽(Λ)] : Λ ⊬! ⊥ := by
  intro h;
  obtain ⟨W, _, F, hf⟩ := ne.existsi;
  simpa [ValidOnFrame ,ValidOnModel] using sound!_on_frameclass h _ F hf;

instance [FrameClass.Nonempty 𝔽(Λ)] : System.Consistent Λ := System.Consistent.of_unprovable unprovable_bot

instance : System.Consistent (𝐊 : AxiomSet α) := inferInstance

end LO.Modal.Standard.Kripke
