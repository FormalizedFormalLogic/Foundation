module

public import Foundation.Modal.Boxdot.GL_Grz
public import Foundation.Modal.Boxdot.GL_S

@[expose] public section

namespace LO.Modal.Logic

lemma iff_provable_Grz_provable_boxdot_S : Modal.S ⊢ φᵇ ↔ Modal.Grz ⊢ φ := by
  apply Iff.trans iff_provable_boxdot_GL_provable_boxdot_S.symm iff_provable_boxdot_GL_provable_Grz;

end LO.Modal.Logic
end
