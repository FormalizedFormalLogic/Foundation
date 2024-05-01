import Logic.Modal.Normal.New.Kripke
import Logic.Modal.Normal.New.Hilbert

namespace LO.Modal.Normal.Kripkean

variable {W α : Type*}

open Formula.Kripkean

instance {Λ : AxiomSet α} : Sound Λ (𝔽(Λ) : FrameClass W α) where
  sound d := by
    induction d.some with
    | maxm h => intro F hF; exact hF.realize h;
    | mdp hpq hp ihpq ihp =>
      intro F hF V w;
      have := (ihpq ⟨hpq⟩) F hF V w;
      have := (ihp ⟨hp⟩) F hF V w;
      simp_all;
    | nec h ih =>
      intro F hF V w w' _;
      have := (ih ⟨h⟩) F hF V w';
      simp_all;
    | disj₃ =>
      simp_all [ValidOnFrameClass, ValidOnFrame, ValidOnModel];
      intros; rename_i hpr hqr hpq;
      cases hpq with
      | inl hp => exact hpr hp;
      | inr hq => exact hqr hq;
    | _ => simp_all [ValidOnFrameClass, ValidOnFrame, ValidOnModel];

instance : Sound 𝐊 (𝔽(𝐊) : FrameClass W α) := inferInstance

end LO.Modal.Normal.Kripkean
