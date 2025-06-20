import Foundation.Modal.Kripke.Preservation
import Foundation.Modal.Kripke.Irreflexive
import Foundation.Modal.Kripke.Asymmetric
import Foundation.Modal.Kripke.AxiomWeakPoint2
import Foundation.Modal.Kripke.AxiomPoint3

namespace LO.Modal

namespace Kripke

variable {F : Kripke.Frame}

open Formula.Kripke
open Relation


class Frame.IsGenerated (F : Kripke.Frame) (R : { s : Set F.World // s.Nonempty }) where
  roots_generates : ∀ w ∉ R.1, ∃ r ∈ R.1, F.Rel.TransGen r w

class Frame.IsRooted (F : Kripke.Frame) (r : outParam F.World) where
  root_generates : ∀ w ≠ r, F.Rel.TransGen r w


protected abbrev Frame.IsConvergent (F : Frame) := _root_.IsConvergent F.Rel
lemma Frame.convergent [F.IsConvergent] : ∀ {x y : F.World}, x ≠ y → ∃ u, x ≺ u ∧ y ≺ u := by apply IsConvergent.convergent

protected abbrev Frame.IsStronglyConvergent (F : Frame) := _root_.IsStronglyConvergent F.Rel
lemma Frame.strongly_convergent [F.IsStronglyConvergent] : ∀ x y : F.World, ∃ u, x ≺ u ∧ y ≺ u := by apply IsStronglyConvergent.s_convergent



protected abbrev Frame.IsStronglyConnected (F : Frame) := _root_.IsTotal _ F.Rel
lemma Frame.s_connected [F.IsStronglyConnected] : ∀ {x y : F.World}, x ≺ y ∨ y ≺ x := by apply IsTotal.total

protected abbrev Frame.IsConnected (F : Frame) := _root_.IsTrichotomous _ F.Rel
lemma Frame.connected [F.IsConnected] : ∀ x y : F.World, x ≺ y ∨ x = y ∨ y ≺ x := by apply IsTrichotomous.trichotomous
lemma Frame.connected' [F.IsConnected] : ∀ x y : F.World, x ≠ y → x ≺ y ∨ y ≺ x := by
  rintro x y nexy;
  rcases F.connected x y with (Rxy | rfl | Ryx);
  . tauto;
  . contradiction;
  . tauto;

namespace Frame.IsRooted

variable {F : Frame} {r : F.World} [rooted : F.IsRooted r]

instance [rooted : F.IsRooted r] : F.IsGenerated (⟨{r}, by tauto⟩) where
  roots_generates := by
    rintro x hx;
    use r;
    constructor;
    . tauto;
    . exact rooted.root_generates x hx;

lemma direct_rooted_of_trans [F.IsTransitive] : ∀ x ≠ r, r ≺ x := by
  intro x hx;
  obtain ⟨n, Rrx⟩ := HRel.TransGen.exists_iterate.mp $ rooted.root_generates x hx;
  exact HRel.iterate.unwrap_of_trans Rrx;

end Frame.IsRooted

instance Frame.mkTransClosure.IsRooted {F : Frame} {r : F.World} [rooted : F.IsRooted r] : (F^+).IsRooted r where
  root_generates := by
    intro x hx;
    exact Relation.TransGen.single $ rooted.root_generates x hx;

namespace Frame


def setGenerate (F : Kripke.Frame) (R : { s : Set F.World // s.Nonempty }) : Kripke.Frame where
  World := { w // w ∈ R.1 ∨ ∃ r ∈ R.1, F.Rel.TransGen r w }
  Rel x y := x.1 ≺ y.1
  world_nonempty := by let ⟨r, hr⟩ := R.2; exact ⟨r, Or.inl hr⟩
infix:80 "↾" => Frame.setGenerate

namespace setGenerate

variable {F : Frame} {R}

protected abbrev roots : { s : Set (F↾R) // s.Nonempty } := ⟨{ r | r.1 ∈ R.1 }, by
  obtain ⟨r, hr⟩ := R.2;
  use ⟨r, by tauto⟩;
  tauto;
⟩

lemma trans_rel_of_origin_trans_rel {hx hy} (Rxy : F.Rel.TransGen x y)
  : ((F↾R)^+.Rel ⟨x, hx⟩ ⟨y, hy⟩) := by
  induction Rxy using TransGen.head_induction_on with
  | base h => exact _root_.Relation.TransGen.single h;
  | @ih a c ha hb hc =>
    let b : (F.setGenerate R).World := ⟨c, by
      rcases hx with hx | ⟨r₁, hR₁, Rr₁a⟩ <;>
      rcases hy with hy | ⟨r₂, hR₂, Rr₂b⟩;
      . right; use a; constructor; assumption; exact TransGen.single ha;
      . right; use a; constructor; assumption; exact TransGen.single ha;
      . right;
        use r₁;
        constructor;
        . assumption;
        . exact TransGen.tail Rr₁a ha;
      . right;
        use r₁;
        constructor;
        . assumption;
        . exact TransGen.tail Rr₁a ha;
    ⟩;
    apply Relation.TransGen.head (b := b);
    . exact ha;
    . apply hc;

instance instGenerated : (F↾R).IsGenerated (setGenerate.roots) where
  roots_generates := by
    rintro ⟨r, (hr | ⟨t, ht, Rtx⟩)⟩ _;
    . simp_all;
    . use ⟨t, by simp_all⟩;
      constructor;
      . simpa;
      . apply trans_rel_of_origin_trans_rel;
        exact Rtx;

end setGenerate


abbrev pointGenerate (F : Kripke.Frame) (r : F.World) : Kripke.Frame where
  World := { w // w = r ∨ F.TransGen r w }
  Rel x y := x.1 ≺ y.1
  world_nonempty := ⟨r, by tauto⟩
infix:80 "↾" => Frame.pointGenerate

namespace pointGenerate

variable {F : Frame} {r : outParam (F.World)}

lemma trans_rel_of_origin_trans_rel {hx hy} (Rxy : F.TransGen x y)
  : ((F↾r)^+.Rel ⟨x, hx⟩ ⟨y, hy⟩) := by
  induction Rxy using TransGen.head_induction_on with
  | base h => exact Relation.TransGen.single h;
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

lemma origin_trans_rel_of_trans_rel {u v : (F↾r).World} (Ruv : (F↾r).TransGen u v) : F.TransGen u.1 v.1 := by
  induction Ruv using TransGen.head_induction_on with
  | base h => exact Relation.TransGen.single h;
  | ih a b c => exact TransGen.head a c;

protected abbrev root : (F↾r).World := ⟨r, by tauto⟩

instance instIsRooted : (F↾r).IsRooted pointGenerate.root where
  root_generates := by
    rintro ⟨w, (rfl | Rrw)⟩ hw;
    . simp at hw;
    . apply trans_rel_of_origin_trans_rel;
      exact Rrw;

instance [Finite F] : Finite (F↾r) := inferInstance

instance isFinite [finite : F.IsFinite] : (F↾r).IsFinite := inferInstance

instance [DecidableEq F.World] : DecidableEq (F↾r).World := Subtype.instDecidableEq

instance isReflexive [F.IsReflexive] : (F↾r).IsReflexive where
  refl := by rintro ⟨x, (rfl | hx)⟩ <;> exact IsRefl.refl x;

instance isTransitive [F.IsTransitive] : (F↾r).IsTransitive where
  trans := by
    rintro ⟨x, (rfl | hx)⟩ ⟨y, (rfl | hy)⟩ ⟨z, (rfl | hz)⟩ hxy hyz;
    . assumption;
    . assumption;
    . have : z ≺ z := IsTrans.trans _ _ _ hxy hyz; exact this;
    . have : x ≺ z := IsTrans.trans _ _ _ hxy hyz; exact this;
    . assumption;
    . have : x ≺ z := IsTrans.trans _ _ _ hxy hyz; exact this;
    . have : x ≺ z := IsTrans.trans _ _ _ hxy hyz; exact this;
    . have : x ≺ z := IsTrans.trans _ _ _ hxy hyz; exact this;

instance isAntisymmetric [F.IsAntisymmetric] : (F↾r).IsAntisymmetric := ⟨by
  rintro ⟨x, (rfl | hx)⟩ ⟨y, (rfl | hy)⟩ Rxy Ryx;
  . tauto;
  . simp only [Subtype.mk.injEq]; apply F.antisymm Rxy Ryx;
  . simp only [Subtype.mk.injEq]; apply F.antisymm Rxy Ryx;
  . simp only [Subtype.mk.injEq]; apply F.antisymm Rxy Ryx;
⟩

instance isIrreflexive [F.IsIrreflexive] : (F↾r).IsIrreflexive := ⟨by rintro ⟨x, (rfl | hx)⟩ h <;> simp at h⟩

instance isAsymmetric [F.IsAsymmetric] : (F↾r).IsAsymmetric := ⟨by
  rintro ⟨x, (rfl | hx)⟩ ⟨y, (rfl | hy)⟩ Rxy <;>
  { dsimp at Rxy; apply IsAsymm.asymm _ _ Rxy; }
⟩

instance isConvergent [F.IsPiecewiseConvergent] [F.IsTransitive] [F.IsReflexive] : (F↾r).IsConvergent := ⟨by
  rintro ⟨x, (rfl | Rrx)⟩ ⟨y, (rfl | Rry)⟩ nexy;
  . tauto;
  . obtain ⟨u, ⟨Rxu, Ryu⟩⟩ := F.p_convergent (y := x)
      (by apply F.refl)
      (by apply HRel.TransGen.unwrap Rry)
      (by simpa using nexy);
    use ⟨u, by right; exact HRel.TransGen.single Rxu⟩;
  . obtain ⟨u, ⟨Ryu, Rux⟩⟩ := F.p_convergent (y := y)
      (by apply F.refl)
      (by apply HRel.TransGen.unwrap Rrx)
      (by simpa using nexy.symm);
    use ⟨u, by right; exact HRel.TransGen.single Ryu⟩;
  . obtain ⟨u, ⟨Rux, Ryu⟩⟩ := F.p_convergent (x := r) (y := x) (z := y)
      (by apply HRel.TransGen.unwrap Rrx)
      (by apply HRel.TransGen.unwrap Rry)
      (by simpa using nexy);
    use ⟨u, by right; exact HRel.TransGen.tail Rrx Rux⟩;
⟩

instance isStronglyConvergent [F.IsPiecewiseStronglyConvergent] [F.IsReflexive] [F.IsTransitive] : (F↾r).IsStronglyConvergent := ⟨by
  rintro ⟨x, (rfl | Rrx)⟩ ⟨y, (rfl | Rry)⟩;
  . use ⟨y, by tauto⟩;
    constructor <;> apply Frame.refl;
  . obtain ⟨u, Ryu, Rxu⟩ := F.ps_convergent
      (by apply HRel.TransGen.unwrap Rry)
      (by apply F.refl);
    use ⟨u, by right; exact HRel.TransGen.single Rxu⟩;
  . obtain ⟨u, Rxu, Ryu⟩ := F.ps_convergent
      (by apply HRel.TransGen.unwrap Rrx)
      (by apply F.refl);
    use ⟨u, by right; exact HRel.TransGen.single Ryu⟩;
  . obtain ⟨u, Rxu, Ryu⟩ := F.ps_convergent
      (by apply HRel.TransGen.unwrap Rrx)
      (by apply HRel.TransGen.unwrap Rry);
    use ⟨u, by right; exact HRel.TransGen.tail Rrx Rxu⟩
⟩

instance isConnected [F.IsPiecewiseConnected] [F.IsTransitive] : (F↾r).IsConnected := ⟨by
  rintro ⟨x, (rfl | Rrx)⟩ ⟨y, (rfl | Rry)⟩;
  . tauto;
  . left;
    simpa using HRel.TransGen.unwrap Rry;
  . right; right;
    simpa using HRel.TransGen.unwrap Rrx;
  . suffices x ≠ y → x ≺ y ∨ y ≺ x by simp; tauto;
    intro nexy;
    refine F.p_connected' (x := r) ?_ ?_ nexy;
    . simpa using HRel.TransGen.unwrap Rrx;
    . simpa using HRel.TransGen.unwrap Rry;
⟩

instance isStronglyConnected [F.IsPiecewiseStronglyConnected] [F.IsReflexive] [F.IsTransitive] : (F↾r).IsStronglyConnected := ⟨by
  rintro ⟨x, (rfl | Rrx)⟩ ⟨y, (rfl | Rry)⟩;
  . left; apply F.refl;
  . left;
    simpa using HRel.TransGen.unwrap Rry;
  . right;
    simpa using HRel.TransGen.unwrap Rrx;
  . suffices x ≺ y ∨ y ≺ x by simp; tauto;
    apply F.ps_connected (x := r);
    . simpa using HRel.TransGen.unwrap Rrx;
    . simpa using HRel.TransGen.unwrap Rry;
⟩

def pMorphism (F : Kripke.Frame) (r : F) : (F↾r) →ₚ F where
  toFun := λ ⟨x, _⟩ => x
  forth := by
    rintro ⟨x, (rfl | hx)⟩ ⟨y, (rfl | hy)⟩ hxy;
    repeat exact hxy;
  back := by
    rintro ⟨x, (rfl | hx)⟩ y Rwv;
    . simp at Rwv; use ⟨y, by tauto⟩
    . use ⟨y, by right; exact Relation.TransGen.tail hx Rwv⟩;

/-
def generatedSub : F↾r ⥹ F where
  toFun := λ ⟨x, _⟩ => x
  forth := by
    rintro ⟨x, (rfl | hx)⟩ ⟨y, (rfl | hy)⟩ hxy;
    repeat exact hxy;
  back := by
    rintro ⟨x, (rfl | hx)⟩ y Rwv;
    . simp at Rwv; use ⟨y, by tauto⟩
    . use ⟨y, by right; exact Relation.TransGen.tail hx Rwv⟩;
  monic := by simp;
-/

end pointGenerate

end Frame


def Model.pointGenerate (M : Kripke.Model) (r : M.World) : Model := ⟨M.toFrame↾r, λ w a => M.Val w.1 a⟩
infix:100 "↾" => Model.pointGenerate

namespace Model.pointGenerate

variable {M : Kripke.Model} {r : outParam M.World}

instance [M.IsFinite] : (M↾r).IsFinite := by dsimp [Model.pointGenerate]; infer_instance;

protected abbrev root : (M↾r).World := ⟨r, by tauto⟩

instance : (M↾r).IsRooted pointGenerate.root := by dsimp [Model.pointGenerate]; infer_instance;

protected def pMorphism : (M↾r) →ₚ M := by
  apply Model.PseudoEpimorphism.ofAtomic (Frame.pointGenerate.pMorphism M.toFrame r);
  simp only [pointGenerate, Frame.pointGenerate, Subtype.forall];
  rintro p x (rfl | Rrx) <;> tauto;

instance isReflexive [M.IsReflexive] : (M↾r).IsReflexive := Frame.pointGenerate.isReflexive
instance isTransitive [M.IsTransitive] : (M↾r).IsTransitive := Frame.pointGenerate.isTransitive
instance isAsymmetric [M.IsAsymmetric] : (M↾r).IsAsymmetric := Frame.pointGenerate.isAsymmetric
instance isAntisymmetric [M.IsAntisymmetric] : (M↾r).IsAntisymmetric := Frame.pointGenerate.isAntisymmetric
instance isPreorder [M.IsPreorder] : (M↾r).IsPreorder where
instance isPartialOrder [M.IsPartialOrder] : (M↾r).IsPartialOrder where
instance isConvergent [M.IsPiecewiseConvergent] [M.IsTransitive] [M.IsReflexive] : (M↾r).IsConvergent := Frame.pointGenerate.isConvergent
instance isStronglyConvergent [M.IsPiecewiseStronglyConvergent] [M.IsTransitive] [M.IsReflexive] : (M↾r).IsStronglyConvergent := Frame.pointGenerate.isStronglyConvergent
instance isConnected [M.IsPiecewiseConnected] [M.IsTransitive] : (M↾r).IsConnected := Frame.pointGenerate.isConnected
instance isStronglyConnected [M.IsPiecewiseStronglyConnected] [M.IsTransitive] [M.IsReflexive] : (M↾r).IsStronglyConnected := Frame.pointGenerate.isStronglyConnected

/-
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
-/

protected def bisimulation (r : M.World) : (M↾r) ⇄ M := Model.pointGenerate.pMorphism.bisimulation

lemma modal_equivalent_at_root (r : M.World) : ModalEquivalent (M₁ := M↾r) (M₂ := M) ⟨r, by tauto⟩ r
  := PseudoEpimorphism.modal_equivalence (Model.pointGenerate.pMorphism) pointGenerate.root

end Model.pointGenerate

end Kripke

end LO.Modal
