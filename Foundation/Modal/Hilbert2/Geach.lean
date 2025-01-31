import Foundation.Modal.Hilbert2.WellKnown

namespace LO.Modal

namespace Hilbert

variable (α) [DecidableEq α]

protected def Geach (G : Set (GeachConfluent.Taple)) : Hilbert ℕ := ⟨
  {Axioms.K (.atom 0) (.atom 1)}
  ∪ G.image (λ t => Axioms.Geach t (.atom 0))
⟩

instance HasT_of_mem_0_0_1_0 (h : ⟨0, 0, 1, 0⟩ ∈ G) : HasT (Hilbert.Geach G) where
  p := 0
  mem_T := by
    simp [Hilbert.Geach];
    use ⟨0, 0, 1, 0⟩;
    simpa;

instance HasB_of_mem_0_1_0_1 (h : ⟨0, 1, 0, 1⟩ ∈ G) : HasB (Hilbert.Geach G) where
  p := 0
  mem_B := by
    simp [Hilbert.Geach];
    use ⟨0, 1, 0, 1⟩;
    simpa;

instance HasD_of_mem_0_0_1_1 (h : ⟨0, 0, 1, 1⟩ ∈ G) : HasD (Hilbert.Geach G) where
  p := 0
  mem_D := by
    simp [Hilbert.Geach];
    use ⟨0, 0, 1, 1⟩;
    simpa;

instance HasFour_of_mem_0_2_1_0 (h : ⟨0, 2, 1, 0⟩ ∈ G) : HasFour (Hilbert.Geach G) where
  p := 0
  mem_Four := by
    simp [Hilbert.Geach];
    use ⟨0, 2, 1, 0⟩;
    simpa;

instance HasFive_of_mem_1_1_0_1 (h : ⟨1, 1, 0, 1⟩ ∈ G) : HasFive (Hilbert.Geach G) where
  p := 0
  mem_Five := by
    simp [Hilbert.Geach];
    use ⟨1, 1, 0, 1⟩;
    simpa;

instance HasDot2_of_mem_1_1_1_1 (h : ⟨1, 1, 1, 1⟩ ∈ G) : HasDot2 (Hilbert.Geach G) where
  p := 0
  mem_Dot2 := by
    simp [Hilbert.Geach];
    use ⟨1, 1, 1, 1⟩;
    simpa;

instance HasTc_of_mem_0_1_0_0 (h : ⟨0, 1, 0, 0⟩ ∈ G) : HasTc (Hilbert.Geach G) where
  p := 0
  mem_Tc := by
    simp [Hilbert.Geach];
    use ⟨0, 1, 0, 0⟩;
    simpa;

end Hilbert

end LO.Modal
