import Foundation.Modal.PLoN.Semantics

namespace LO.Modal

namespace PLoN

open Formula

variable {φ : Formula α} {Λ : Hilbert α}

lemma sound (defines : Λ.DefinesPLoNFrameClass 𝔽) (d : Λ ⊢! φ) : 𝔽 ⊧ φ := by
  intro F hF;
  have := defines.mpr hF;
  exact Semantics.RealizeSet.setOf_iff.mp this φ d;

lemma sound_of_defines (defines : Λ.DefinesPLoNFrameClass 𝔽) : Sound Λ 𝔽 := ⟨sound defines⟩

lemma unprovable_bot_of_nonempty_frameclass (defines : Λ.DefinesPLoNFrameClass 𝔽) (nonempty : 𝔽.Nonempty) : Λ ⊬ ⊥ := by
  intro h;
  obtain ⟨⟨_, F⟩, hF⟩ := nonempty;
  simpa using sound defines h hF;

lemma consistent_of_defines (defines : Λ.DefinesPLoNFrameClass 𝔽) (nonempty : 𝔽.Nonempty) : System.Consistent Λ := by
  apply System.Consistent.of_unprovable;
  exact unprovable_bot_of_nonempty_frameclass defines nonempty;


instance : Sound (Hilbert.N α) (AllFrameClass α) := sound_of_defines N_defines

instance : System.Consistent (Hilbert.N α) := consistent_of_defines N_defines AllFrameClass.nonempty

end PLoN

end LO.Modal
