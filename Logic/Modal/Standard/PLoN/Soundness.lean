import Logic.Modal.Standard.Deduction
import Logic.Modal.Standard.PLoN.Semantics

namespace LO.Modal.Standard

namespace PLoN

open Formula

variable {p : Formula α}

lemma sound!_on_N (d : 𝐍 ⊢! p) : ℕ𝔽(𝐍) ⊧ p := by
  induction d using Deduction.inducition! with
  | hMaxm h => simp at h;
  | hMdp ihpq ihp =>
    intro F hF V w;
    replace ihpq := ihpq F hF V w;
    replace ihp := ihp F hF V w;
    exact ihpq ihp;
  | hNec _ ih =>
    intro F hF V w w' _;
    exact ih F hF V w';
  | hLoeb => simp_all only [Bool.false_eq_true];
  | hHenkin => simp_all only [Bool.false_eq_true];
  | hDisj₃ =>
    simp_all [PLoN_ValidOnFrameClass, PLoN_ValidOnFrame, PLoN_ValidOnModel, PLoN_Satisfies];
    intros; rename_i hpr hqr hpq;
    cases hpq with
    | inl hp => exact hpr hp;
    | inr hq => exact hqr hq;
  | _ => simp_all [PLoN_ValidOnFrameClass, PLoN_ValidOnFrame, PLoN_ValidOnModel, PLoN_Satisfies];

instance : Sound (𝐍 : DeductionParameter α) ℕ𝔽(𝐍) := ⟨sound!_on_N⟩

lemma unprovable_bot_on_N : (𝐍 : DeductionParameter α) ⊬! ⊥ := by
  intro h;
  obtain ⟨F, hF⟩ := FrameClassNonempty.N;
  simpa using sound!_on_N h F hF;

instance : System.Consistent (𝐍 : DeductionParameter α) := System.Consistent.of_unprovable $ unprovable_bot_on_N

end PLoN

end LO.Modal.Standard
