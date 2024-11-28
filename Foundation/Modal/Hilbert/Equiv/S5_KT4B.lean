import Foundation.Modal.Kripke.Geach

namespace LO.Modal.Hilbert

open System
open Modal.Kripke

theorem equiv_S5_KT4B : (Hilbert.S5 ℕ) =ₛ (Hilbert.KT4B ℕ) := by
  apply Kripke.equiv_of_eq_FrameClass ReflexiveEuclideanFrameClass ReflexiveTransitiveSymmetricFrameClass;
  apply Set.eq_of_subset_of_subset;
  . rintro F ⟨F_refl, F_eucl⟩;
    refine ⟨F_refl, trans_of_refl_eucl F_refl F_eucl, symm_of_refl_eucl F_refl F_eucl⟩;
  . rintro F ⟨F_refl, F_eucl, F_symm⟩;
    refine ⟨F_refl, eucl_of_symm_trans F_symm F_eucl⟩;

end LO.Modal.Hilbert
