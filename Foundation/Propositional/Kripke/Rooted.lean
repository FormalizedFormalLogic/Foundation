module

public import Foundation.Propositional.Kripke.Preservation

@[expose] public section

namespace LO.Propositional

namespace Kripke

open Formula.Kripke
open Relation

namespace Frame

class IsRooted (F : Kripke.Frame) (r : F.World) where
  root_generates : ∀ w ≠ r, r ≺ w

abbrev pointGenerate (F : Kripke.Frame) (r : F.World) : Kripke.Frame where
  World := { w // w = r ∨ r ≺ w }
  Rel x y := x.1 ≺ y.1
  world_nonempty := ⟨r, by tauto⟩
  rel_partial_order := {
    refl := by rintro ⟨x, (rfl | hx)⟩ <;> exact F.refl;
    trans := by
      rintro ⟨x, (rfl | hx)⟩ ⟨y, (rfl | hy)⟩ ⟨z, (rfl | hz)⟩ Rxy Ryz;
      any_goals assumption;
      any_goals apply F.refl;
      any_goals apply F.trans Rxy Ryz;
    antisymm := by
      rintro ⟨x, (rfl | hx)⟩ ⟨y, (rfl | hy)⟩ Rxy Ryx;
      . simp;
      . simp_all only [Subtype.mk.injEq];
        apply F.rel_partial_order.antisymm <;> assumption;
      . simp_all only [Subtype.mk.injEq];
        apply F.rel_partial_order.antisymm <;> assumption;
      . simp_all only [Subtype.mk.injEq];
        apply F.rel_partial_order.antisymm <;> assumption;
  }
infix:100 "↾" => Frame.pointGenerate

namespace pointGenerate

variable {F : Frame} {r : F.World}

protected abbrev root : (F↾r).World := ⟨r, by tauto⟩

instance instIsRooted : (F↾r).IsRooted pointGenerate.root where
  root_generates := by rintro ⟨w, (rfl | Rrw)⟩ hw <;> tauto;

instance [Finite F.World] : Finite (F↾r).World := Subtype.finite

instance [Finite F] : (F↾r).IsFinite := (isFinite_iff _).mpr inferInstance

instance [DecidableEq F.World] : DecidableEq (F↾r).World := Subtype.instDecidableEq

lemma rel_irrefl (F_irrefl : Irreflexive F) : Irreflexive (F↾r).Rel := by
  rintro ⟨x, (rfl | hx)⟩ h;
  all_goals apply F_irrefl; exact h;

def pMorphism : (F↾r) →ₚ F where
  toFun := λ ⟨x, _⟩ => x
  forth := by
    rintro ⟨x, (rfl | hx)⟩ ⟨y, (rfl | hy)⟩ hxy;
    repeat exact hxy;
  back := by
    rintro ⟨x, (rfl | hx)⟩ y Rwv;
    . simp at Rwv; use ⟨y, by tauto⟩
    . use ⟨y, by right; exact F.trans hx Rwv⟩;

end pointGenerate

end Frame


def Model.pointGenerate (M : Kripke.Model) (r : M.World) : Model where
  toFrame := M.toFrame↾r
  Val := ⟨
    λ a w => M.Val a w.1,
    by rintro ⟨x, (rfl | hx)⟩ ⟨y, (rfl | hy)⟩ r a hx; all_goals exact M.Val.hereditary (by tauto) hx;
  ⟩
infix:100 "↾" => Model.pointGenerate

namespace Model.pointGenerate

variable {M : Kripke.Model} {r : M.World}

protected abbrev root : (M↾r).World := ⟨r, by tauto⟩

protected def pMorphism : (M↾r) →ₚ M := by
  apply Model.PseudoEpimorphism.ofAtomic (Frame.pointGenerate.pMorphism (F := M.toFrame) (r := r));
  simp only [pointGenerate, Frame.pointGenerate, Subtype.forall];
  rintro p x (rfl | Rrx) <;> tauto;

protected def bisimulation (r : M.World) : (M↾r) ⇄ M := Model.pointGenerate.pMorphism.bisimulation

lemma modal_equivalent_at_root (r : M.World) : ModalEquivalent (M₁ := M↾r) (M₂ := M) ⟨r, by tauto⟩ r
  := PseudoEpimorphism.modal_equivalence (Model.pointGenerate.pMorphism) pointGenerate.root

end Model.pointGenerate

end Kripke

end LO.Propositional
end
