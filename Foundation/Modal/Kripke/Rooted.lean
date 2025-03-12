import Foundation.Modal.Kripke.Preservation

namespace LO.Modal

namespace Kripke

open Formula.Kripke


class Frame.Generated (F : Kripke.Frame) where
  roots : Set F.World
  roots_isRooted : ∀ w ∉ roots, ∃ r ∈ roots, r ≺^+ w

class Frame.Rooted (F : Kripke.Frame) where
  root : F.World
  root_isPointRooted : ∀ w ≠ root, root ≺^+ w

namespace PointRootedFrame


variable {F : Frame}

instance [rooted : F.Rooted] : F.Generated where
  roots := {rooted.root}
  roots_isRooted := by
    rintro x hx;
    use rooted.root;
    constructor;
    . tauto;
    . exact rooted.root_isPointRooted x hx;

end PointRootedFrame

namespace Frame

/-
def setGenerate (F : Kripke.Frame) (R : Set F.World) (R_nonempty : R.Nonempty := by tauto_set) : Kripke.Frame where
  World := { w // w ∈ R ∨ ∃ r ∈ R, r ≺^+ w }
  Rel x y := x.1 ≺ y.1
  world_nonempty := by
    let ⟨r, hr⟩ := R_nonempty;
    exact ⟨r, Or.inl hr⟩

namespace setGenerate

variable {F : Frame} {R : Set F.World} {R_nonempty : R.Nonempty}

instance instGenerated : (F.setGenerate R R_nonempty).Generated where
  roots := { r | r.1 ∈ R }
  roots_isRooted := by
    rintro ⟨x, (hr | ⟨r, hx₁, hx₂⟩)⟩ hw;
    . simp at hw; contradiction;
    . use ⟨r, by tauto⟩;
      constructor;
      . tauto;
      . sorry;

end setGenerate
-/


abbrev pointGenerate (F : Kripke.Frame) (r : F.World) : Kripke.Frame where
  World := { w // w = r ∨ r ≺^+ w }
  Rel x y := x.1 ≺ y.1
  world_nonempty := ⟨r, by tauto⟩
infix:100 "↾" => Frame.pointGenerate

namespace pointGenerate

open Relation

variable {F : Frame} {r : F.World}

lemma trans_rel_of_origin_trans_rel {hx : x = r ∨ r ≺^+ x} {hy : y = r ∨ r ≺^+ y} (Rxy : x ≺^+ y)
  : (RelTransGen (F := F↾r) ⟨x, hx⟩ ⟨y, hy⟩) := by
  induction Rxy using TransGen.head_induction_on with
  | base h => exact Frame.RelTransGen.single h;
  | @ih a c ha hb hc =>
    let b : (F↾r).World := ⟨c, by
      rcases hx with rfl | Rra <;>
      rcases hy with rfl | Rrb;
      . right; exact TransGen.single ha;
      . right; exact TransGen.single ha;
      . right; exact TransGen.tail Rra ha;
      . right; exact TransGen.tail Rra ha;
    ⟩;
    apply Relation.TransGen.head (b := b);
    . exact ha;
    . apply hc;

lemma origin_trans_rel_of_trans_rel {u v : (F↾r).World} (Ruv : u ≺^+ v) : u.1 ≺^+ v.1 := by
  induction Ruv using TransGen.head_induction_on with
  | base h => exact Frame.RelTransGen.single h;
  | ih a b c => exact TransGen.head a c;

-- set_option pp.proofs true in
instance instPointRooted : (F↾r).Rooted where
  root := ⟨r, by tauto⟩
  root_isPointRooted := by
    rintro ⟨w, (rfl | Rrw)⟩ hw;
    . simp at hw;
    . apply trans_rel_of_origin_trans_rel;
      exact Rrw;

instance [Finite F.World] : Finite (F↾r).World := Subtype.finite

instance [DecidableEq F.World] : DecidableEq (F↾r).World := Subtype.instDecidableEq

lemma rel_trans (F_trans : Transitive F) : Transitive (F↾r).Rel := by
  rintro ⟨x, (rfl | hx)⟩ ⟨y, (rfl | hy)⟩ ⟨z, (rfl | hz)⟩ hxy hyz;
  all_goals aesop;

lemma rel_irrefl (F_irrefl : Irreflexive F) : Irreflexive (F↾r).Rel := by
  rintro ⟨x, (rfl | hx)⟩ h;
  all_goals aesop;

/-
lemma rel_universal_of_refl_eucl (F_refl : Reflexive F) (F_eucl : Euclidean F) : Universal (F↾r).Rel := by
  have F_symm := symm_of_refl_eucl F_refl F_eucl;
  rintro ⟨x, (rfl | hx)⟩ ⟨y, (rfl | hy)⟩;
  . apply F_refl;
  .
    sorry;
  . apply F_symm;
    sorry;
  . sorry;
-/

def generatedSub : F↾r ⥹ F where
  toFun := λ ⟨x, _⟩ => x
  forth := by
    rintro ⟨x, (rfl | hx)⟩ ⟨y, (rfl | hy)⟩ hxy;
    repeat exact hxy;
  back := by
    rintro ⟨x, (rfl | hx)⟩ y Rwv;
    . simp at Rwv; use ⟨y, by tauto⟩
    . use ⟨y, by right; exact Frame.RelTransGen.tail hx Rwv⟩;
  monic := by simp;

end pointGenerate

end Frame


class Model.Rooted (M : Kripke.Model) where
  [frame_pointRooted : M.toFrame.Rooted]


def Model.pointGenerate (M : Kripke.Model) (r : M.World) : Model where
  toFrame := M.toFrame↾r
  Val := λ w a => M.Val w.1 a
infix:100 "↾" => Model.pointGenerate

namespace Model.pointGenerate

variable {M : Kripke.Model} {r : M.World}

instance : (M↾r).Rooted where
  frame_pointRooted := Frame.pointGenerate.instPointRooted

instance : (M↾r) ⥹ M := by
  letI g := Frame.pointGenerate.generatedSub (F := M.toFrame) (r := r);
  exact {
    toFun := g.toFun,
    forth := g.forth,
    back := g.back,
    monic := g.monic
    atomic := by
      simp [Model.pointGenerate, Frame.pointGenerate, g];
      rintro p x (rfl | Rrx) <;> tauto;
  }

def bisimulation_of_trans (r : M.World) : (M↾r) ⇄ M where
  toRel x y := x.1 = y
  atomic := by
    rintro x y a rfl;
    simp [Model.pointGenerate];
  forth := by
    rintro x₁ y₁ x₂ rfl Rx₂y₁;
    use y₁.1;
    constructor;
    . simp;
    . exact Rx₂y₁;
  back := by
    rintro ⟨x₁, (rfl | Rrx₁)⟩ x₂ y₂ rfl Rx₂y₂;
    . use ⟨y₂, by right; exact Frame.RelTransGen.single Rx₂y₂⟩;
      constructor;
      . simp;
      . exact Rx₂y₂;
    . use ⟨y₂, (by right; exact Relation.TransGen.tail Rrx₁ Rx₂y₂;)⟩;
      constructor;
      . simp;
      . exact Rx₂y₂;

lemma modal_equivalent_at_root (r : M.World) : ModalEquivalent (M₁ := M↾r) (M₂ := M) ⟨r, by tauto⟩ r
  := modal_equivalent_of_bisimilar (bisimulation_of_trans r) $ by simp [bisimulation_of_trans];

end Model.pointGenerate

end Kripke

end LO.Modal
