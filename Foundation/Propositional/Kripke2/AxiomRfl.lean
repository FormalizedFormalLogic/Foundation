module

public import Foundation.Propositional.Kripke2.AxiomSer

@[expose] public section

namespace LO.Propositional


open Kripke2
open Formula.Kripke2

namespace Kripke2

variable {F : Kripke2.Frame}


namespace Frame

protected abbrev IsReflexive (F : Kripke2.Frame) := _root_.Std.Refl F.Rel
@[simp, grind .] lemma refl [F.IsReflexive] : ∀ x : F, x ≺ x := Std.Refl.refl

instance [F.IsReflexive] : F.IsSerial := inferInstance

end Frame


@[simp high, grind .]
lemma valid_axiomRfl_of_isReflexive [F.IsReflexive] : F ⊧ Axioms.Rfl φ ψ := by
  intro V x y Rxy h;
  have ⟨h₁, h₂⟩ := Satisfies.def_and.mp h;
  apply h₂;
  . simp;
  . assumption;

lemma isReflexive_of_valid_axiomRfl (h : F ⊧ Axioms.Rfl #0 #1) : F.IsReflexive := by
  constructor;
  intro x;
  have := @h (λ w a => match a with | 0 => w = x | 1 => x ≺ w | _ => False) F.root x F.rooted $ by
    apply Satisfies.def_and.mpr;
    constructor;
    . tauto;
    . rintro y Rxy;
      tauto;
  exact this;

instance [Entailment.F L] [Entailment.HasAxiomRfl L] [Entailment.Disjunctive L] : Frame.IsReflexive (canonicalModel L).toFrame where
  refl := by
    rintro T φ ψ hφψ hφ;
    apply T.imp_closed (show L ⊢ Axioms.Rfl φ ψ from by simp);
    apply T.andIR <;> assumption;

end Kripke2

end LO.Propositional
end
