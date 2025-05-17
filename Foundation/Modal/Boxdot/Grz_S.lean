import Foundation.Modal.Boxdot.GL_Grz
import Foundation.Modal.Boxdot.GL_S

namespace LO

namespace Modal.Logic

lemma iff_provable_Grz_provable_boxdot_S {A : Formula _} : A ∈ Logic.Grz ↔ Aᵇ ∈ Logic.S := by
  apply Iff.trans iff_provable_boxdot_GL_provable_Grz.symm;
  exact iff_provable_boxdot_GL_provable_boxdot_S;

end Modal.Logic

end LO
