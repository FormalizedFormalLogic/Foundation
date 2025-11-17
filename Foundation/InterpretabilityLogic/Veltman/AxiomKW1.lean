import Foundation.InterpretabilityLogic.Veltman.Basic
import Foundation.InterpretabilityLogic.Veltman.AxiomJ2
import Foundation.InterpretabilityLogic.Veltman.AxiomW
import Foundation.InterpretabilityLogic.Veltman.Logic.IL
import Mathlib.Tactic.TFAE

def Rel.IsCofinal (U : Rel α α) (X Y : Set α) : Prop := ∀ x ∈ X, ∃ y ∈ Y, U x y

namespace LO.InterpretabilityLogic.Veltman

open Veltman Formula.Veltman

variable {F : Veltman.Frame} {φ ψ χ : Formula ℕ}


namespace Frame

def SR {F : Frame} (w : F.World) := Relation.Comp (· ≺[w] ·) (· ≺ ·)
notation:50 x:max " ≺[" w "]≺ " y:max => SR w x y

class HasAxiomKW1 (F : Frame) : Prop where
  -- S_KW1 : ∀ {w : F.World}, ∀ {x : { x // w ≺ x }}, ∃ y, (x ≺[w] y ∧ ({ z | x ≺[w] z } ∩ {z | y ≺[w]≺ z }) = ∅)
  S_KW1 : ∀ {w : F.World}, ∀ {x : { a // w ≺ a }}, ∃ y, (x ≺[w] y ∧ (∀ z, ({ a | z ≺ a } ∩ {a | y ≺[w]≺ a }) = ∅))
export HasAxiomKW1 (S_KW1)

end Frame


@[simp high, grind .]
lemma validate_axiomKW1_of_HasAxiomKW1 [F.IsIL] [F.HasAxiomKW1] : F ⊧ Axioms.KW1 φ := by
  intro V x h₁ y Rxy _;
  obtain ⟨z, Sxyz, h⟩ := F.S_KW1 (w := x) (x := ⟨y, Rxy⟩);
  use z;
  constructor;
  . assumption;
  . apply Satisfies.neg_def.mpr;
    contrapose! h;
    obtain ⟨u, Sxzu, hu⟩ := h₁ z (F.S_J4 Sxyz) h;
    obtain ⟨v, Ruv, _⟩ := Satisfies.dia_def.mp hu; clear hu;
    use u, v;
    constructor;
    . simpa;
    . use u;
    /-
    use u, v;
    constructor;
    . simpa;
    . use u;
    -/

@[simp high, grind .]
lemma validate_axiomKW1_or_axiomF_of_HasAxiomKW1 [F.IsIL] [F.HasAxiomKW1] : F ⊧ (Axioms.KW1 φ ⋎ Axioms.F ψ) := by
  intro V x;
  apply Satisfies.or_def.mpr;
  left;
  apply validate_axiomKW1_of_HasAxiomKW1;

open Formula (atom) in
lemma Frame.HasAxiomKW1.of_validate_axiomKW1 [F.IsIL] (h : F ⊧ Axioms.KW1 (.atom 0)) : F.HasAxiomKW1 := by
  constructor;
  contrapose! h;
  obtain ⟨w, ⟨x, Rwx⟩, h⟩ := h;
  obtain ⟨y, z, ⟨Ryz, ⟨u, Swxu, Ruz⟩⟩⟩ := h x (F.S_J1 Rwx);
  simp at Ryz;
  apply ValidOnFrame.iff_not_exists_valuation_world.mpr;
  use (λ a _ => x ≺[w] a), w;
  apply Satisfies.not_imp_def.mpr;
  constructor;
  . simp [Semantics.Models, Satisfies];
    intro v Rwv Swxv;
    use u;
    constructor;
    . sorry;
    . use z;
  . apply Satisfies.not_rhd_def.mpr;
    simp [Satisfies, Semantics.Models];
    use u;
    constructor;
    . apply F.S_J4 Swxu
    . intro v Swuv;
      apply F.S_J2 Swxu Swuv;

set_option push_neg.use_distrib true in
open Formula (atom) in
lemma Frame.HasAxiomKW1.of_validate_axiomF [F.IsIL] (h : F ⊧ Axioms.F (.atom 0)) : F.HasAxiomKW1 := by
  constructor;
  contrapose! h;
  obtain ⟨w, ⟨x, Rwx⟩, h⟩ := h;
  rcases h x with (nSwxx | ⟨y, z, Ryz, ⟨u, Swxu, Ruz⟩⟩);
  . exfalso;
    apply nSwxx;
    apply F.S_J1;
    assumption;
  . apply ValidOnFrame.iff_not_exists_valuation_world.mpr;
    use (λ a _ => x ≺[w] a), w;
    apply Satisfies.not_imp_def.mpr;
    constructor;
    . simp [Semantics.Models, Satisfies];
      intro v Rwv Swxv;
      use u;
      constructor;
      . sorry;
      . use v;
        constructor;
        . assumption;
        . assumption;
    . apply Satisfies.not_box_def.mpr;
      simp [Satisfies, Semantics.Models];
      use u;
      constructor;
      . apply F.S_J4 Swxu
      . assumption;



end LO.InterpretabilityLogic.Veltman
