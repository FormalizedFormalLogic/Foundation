import Foundation.Modal.Hilbert2.WellKnown

namespace LO.Modal

namespace Hilbert

variable (α) [DecidableEq α] [h2 : HasElements 2 α]

protected def Geach (G : Set (GeachConfluent.Taple)) : Hilbert α := ⟨
  {Axioms.K (.atom (h2.vec[0])) (.atom (h2.vec[1]))}
  ∪ G.image (λ t => Axioms.Geach t (h2.vec[0]))
⟩

instance HasT_of_mem_0_0_1_0 (h : ⟨0, 0, 1, 0⟩ ∈ G) : HasT (Hilbert.Geach α G) where
  p := h2.vec[0]
  mem_T := by
    unfold Hilbert.Geach;
    simp;
    use ⟨0, 0, 1, 0⟩;
    simpa;

instance HasB_of_mem_0_1_0_1 (h : ⟨0, 1, 0, 1⟩ ∈ G) : HasB (Hilbert.Geach α G) where
  p := h2.vec[0]
  mem_B := by
    unfold Hilbert.Geach;
    simp;
    use ⟨0, 1, 0, 1⟩;
    simpa;

instance HasD_of_mem_0_0_1_1 (h : ⟨0, 0, 1, 1⟩ ∈ G) : HasD (Hilbert.Geach α G) where
  p := h2.vec[0]
  mem_D := by
    unfold Hilbert.Geach;
    simp;
    use ⟨0, 0, 1, 1⟩;
    simpa;

instance HasFour_of_mem_0_2_1_0 (h : ⟨0, 2, 1, 0⟩ ∈ G) : HasFour (Hilbert.Geach α G) where
  p := h2.vec[0]
  mem_Four := by
    unfold Hilbert.Geach;
    simp;
    use ⟨0, 2, 1, 0⟩;
    simpa;

instance HasFive_of_mem_1_1_0_1 (h : ⟨1, 1, 0, 1⟩ ∈ G) : HasFive (Hilbert.Geach α G) where
  p := h2.vec[0]
  mem_Five := by
    unfold Hilbert.Geach;
    simp;
    use ⟨1, 1, 0, 1⟩;
    simpa;

end Hilbert

end LO.Modal
