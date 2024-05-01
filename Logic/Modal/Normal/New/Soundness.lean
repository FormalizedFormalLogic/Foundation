import Logic.Modal.Normal.New.Kripke
import Logic.Modal.Normal.New.Hilbert

namespace LO.Modal.Normal.Kripkean

variable {W α : Type*}

open Semantics.HilbertMinimal Semantics.HilbertClassical Semantics.Necessitation

instance {Λ : AxiomSet α} : Sound Λ (𝔽(Λ) : FrameClass W α) where
  sound d := by
    induction d.some with
    | maxm h => exact validOnAxiomSetFrameClass_axiom h;
    | mdp hpq hp ihpq ihp => exact realize_mdp (ihpq ⟨hpq⟩) (ihp ⟨hp⟩)
    | nec h ih => exact realize_nec (ih ⟨h⟩);
    | verum => apply realize_verum;
    | conj₁ => apply realize_conj₁;
    | conj₂ => apply realize_conj₂;
    | conj₃ => apply realize_conj₃;
    | disj₁ => apply realize_disj₁;
    | disj₂ => apply realize_disj₂;
    | disj₃ => apply realize_disj₃;
    | imply₁ => apply realize_imply₁;
    | imply₂ => apply realize_imply₂;
    | dne => apply realize_dne;

instance : Sound 𝐊 (𝔽(𝐊) : FrameClass W α) := inferInstance

end LO.Modal.Normal.Kripkean
