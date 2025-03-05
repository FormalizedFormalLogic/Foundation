import Foundation.Modal.Logic.WellKnown

namespace LO.Modal.Logic

open Formula
open Entailment
open Kripke

instance : ProperSublogic Logic.KTc Logic.Triv := ⟨by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.Triv ⊢! φ ∧ ¬CoreflexiveFrameClass ⊧ φ by
      simpa [KTc.eq_CoreflexiveKripkeFrameClass_Logic];
    use (Axioms.T (.atom 0));
    constructor;
    . exact axiomT!;
    . apply Formula.Kripke.ValidOnFrameClass.not_of_exists_model_world;
      use ⟨⟨Fin 2, λ x y => False⟩, λ w _ => False⟩, 0;
      constructor;
      . simp [Coreflexive];
      . simp [Satisfies, Semantics.Realize];
⟩

instance : ProperSublogic Logic.KTc Logic.Ver := ⟨by
  constructor;
  . rw [KTc.eq_CoreflexiveKripkeFrameClass_Logic, Ver.eq_IsolatedFrameClass_Logic];
    rintro φ hφ F F_iso;
    apply hφ;
    simp_all [Coreflexive, Isolated];
  . suffices ∃ φ, Hilbert.Ver ⊢! φ ∧ ¬CoreflexiveFrameClass ⊧ φ by
      simpa [KTc.eq_CoreflexiveKripkeFrameClass_Logic];
    use (Axioms.Ver ⊥);
    constructor;
    . exact axiomVer!;
    . apply Formula.Kripke.ValidOnFrameClass.not_of_exists_model_world;
      let M : Model := ⟨⟨Fin 1, λ x y => True⟩, λ w _ => False⟩;
      use M, 0;
      constructor;
      . simp [M, Coreflexive]; aesop;
      . suffices ∃ x, (0 : M.World) ≺ x by simpa [Satisfies, Semantics.Realize];
        use 0;
⟩

instance : ProperSublogic Logic.KB4 Logic.KTc := ⟨by
  constructor;
  . rw [KB4.eq_ReflexiveTransitiveKripkeFrameClass_Logic, KTc.eq_CoreflexiveKripkeFrameClass_Logic];
    rintro φ hφ F F_corefl;
    apply hφ;
    refine ⟨?_, ?_⟩;
    . intro x y Rxy;
      rw [F_corefl Rxy] at *;
      assumption;
    . intro x y z Rxy Ryz;
      rw [F_corefl Rxy, F_corefl Ryz] at *;
      assumption;
  . suffices ∃ φ, Hilbert.KTc ⊢! φ ∧ ¬SymmetricTransitiveFrameClass ⊧ φ by
      simpa [KB4.eq_ReflexiveTransitiveKripkeFrameClass_Logic];
    use (Axioms.Tc (.atom 0));
    constructor;
    . exact axiomTc!;
    . apply Formula.Kripke.ValidOnFrameClass.not_of_exists_model_world;
      let M : Model := ⟨⟨Fin 2, λ x y => True⟩, λ w _ => w = 0⟩;
      use M, 0;
      constructor;
      . simp [Symmetric, Transitive, M];
      . suffices ∃ x, (x : M.World) ≠ 0 by
          simp [M, Semantics.Realize, Satisfies];
          tauto;
        use 1;
        aesop;
⟩

end LO.Modal.Logic
