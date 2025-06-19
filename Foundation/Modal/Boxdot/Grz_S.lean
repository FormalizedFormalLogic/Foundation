import Foundation.Modal.Boxdot.GL_Grz
import Foundation.Modal.Boxdot.GL_S

namespace LO.Modal.Logic

lemma iff_provable_Grz_provable_boxdot_S {φ : Formula _} : φᵇ ∈ Logic.S ↔ φ ∈ Logic.Grz := by
  apply Iff.trans iff_provable_boxdot_GL_provable_boxdot_S.symm;
  exact iff_provable_boxdot_GL_provable_Grz;

instance : BoxdotProperty Logic.S Logic.Grz := ⟨iff_provable_Grz_provable_boxdot_S⟩

end LO.Modal.Logic
