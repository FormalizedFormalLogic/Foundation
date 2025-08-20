import Foundation.Modal.Boxdot.GL_Grz
import Foundation.Modal.Boxdot.GL_S

namespace LO.Modal.Logic

lemma iff_provable_Grz_provable_boxdot_S : Modal.S ⊢! φᵇ ↔ Modal.Grz ⊢! φ := by
  apply Iff.trans iff_provable_boxdot_GL_provable_boxdot_S.symm
  simp only [Hilbert.Normal.iff_logic_provable_provable]
  exact iff_provable_boxdot_GL_provable_Grz

end LO.Modal.Logic
