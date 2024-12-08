import Foundation.Modal.Hilbert.Systems

namespace LO.Modal.Hilbert

open System

theorem GL_weakerThan_GLS : (Hilbert.GL α) ≤ₛ (Hilbert.GLS α) := by
  apply System.weakerThan_iff.mpr;
  intro φ h;
  exact Deduction.maxm! (by left; simpa);

end LO.Modal.Hilbert
