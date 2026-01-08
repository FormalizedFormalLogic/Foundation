import Foundation.Propositional.Kripke2.Basic
import Foundation.Propositional.Kripke2.AxiomSer
import Foundation.Vorspiel.Rel.Convergent
import Foundation.Vorspiel.Rel.Euclidean
import Foundation.Vorspiel.Rel.Coreflexive
import Foundation.Propositional.Kripke2.FTheory

namespace LO.Propositional

open Kripke2
open Formula.Kripke2

namespace Kripke2

variable {F : Kripke2.Frame} {φ ψ : Formula ℕ}

namespace Frame

protected abbrev IsSymmetric (F : Kripke2.Frame) := _root_.Std.Symm F.Rel
@[simp, grind →] lemma symm [F.IsSymmetric] : ∀ {x y : F}, x ≺ y → y ≺ x := by apply Std.Symm.symm

instance [F.IsSymmetric] : Frame.IsSerial F where
  serial x := by
    use F.root;
    apply F.symm;
    apply F.rooted;

end Frame


@[simp high, grind .]
lemma valid_axiomSym_of_isSymmetric [F.IsSymmetric] : F ⊧ Axioms.Sym φ ψ := by
  intro V x y Rxy h₁;
  apply Satisfies.def_or.mpr;
  apply or_iff_not_imp_left.mpr;
  intro h₂;
  apply Satisfies.def_neg.mpr;
  intro z Ryz;
  apply Satisfies.not_def_imp.mpr;
  use y;
  refine ⟨?_, ?_, ?_⟩;
  . apply F.symm Ryz;
  . assumption;
  . assumption;

lemma isSymmetric_of_valid_axiomSym (h : F ⊧ Axioms.Sym #0 #1) : F.IsSymmetric := by
  constructor;
  intro x y Rxy;
  rcases @h (λ w a => match a with | 0 => w = x | 1 => y ≺ w | _ => False) F.root x F.rooted (by tauto) with h | h;
  . assumption;
  . have := h Rxy;
    simp [Satisfies] at this;

end Kripke2

end LO.Propositional
