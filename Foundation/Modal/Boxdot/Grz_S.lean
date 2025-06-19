import Foundation.Modal.Boxdot.GL_Grz
import Foundation.Modal.Boxdot.GL_S

namespace LO.Modal.Logic

lemma iff_provable_Grz_provable_boxdot_S {φ : Formula _} : φ ∈ Logic.Grz ↔ φᵇ ∈ Logic.S := by
  apply Iff.trans iff_provable_boxdot_GL_provable_Grz.symm;
  exact iff_provable_boxdot_GL_provable_boxdot_S;

end LO.Modal.Logic
