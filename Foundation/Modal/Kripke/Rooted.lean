module

public import Foundation.Modal.Kripke.Preservation
public import Foundation.Modal.Kripke.Irreflexive
public import Foundation.Modal.Kripke.Asymmetric
public import Foundation.Modal.Kripke.AxiomWeakPoint2
public import Foundation.Modal.Kripke.AxiomPoint3

@[expose] public section

namespace LO.Modal

namespace Kripke

variable {F : Kripke.Frame}

open Formula.Kripke
open Relation

namespace Frame

variable {r : outParam F.World}

protected abbrev IsConvergent (F : Frame) := _root_.IsConvergent F.Rel
lemma convergent [F.IsConvergent] : ∀ {x y : F.World}, x ≠ y → ∃ u, x ≺ u ∧ y ≺ u := by apply IsConvergent.convergent

protected abbrev IsStronglyConvergent (F : Frame) := _root_.IsStronglyConvergent F.Rel
lemma strongly_convergent [F.IsStronglyConvergent] : ∀ x y : F.World, ∃ u, x ≺ u ∧ y ≺ u := by apply IsStronglyConvergent.s_convergent


protected abbrev IsStronglyConnected (F : Frame) := _root_.Std.Total F.Rel
lemma s_connected [F.IsStronglyConnected] : ∀ {x y : F.World}, x ≺ y ∨ y ≺ x := by apply Std.Total.total

protected abbrev IsConnected (F : Frame) := _root_.IsTrichotomous _ F.Rel
lemma connected [F.IsConnected] : ∀ x y : F.World, x ≺ y ∨ x = y ∨ y ≺ x := by apply IsTrichotomous.trichotomous
lemma connected' [F.IsConnected] : ∀ x y : F.World, x ≠ y → x ≺ y ∨ y ≺ x := by
  rintro x y nexy;
  rcases F.connected x y with (Rxy | rfl | Ryx);
  . tauto;
  . contradiction;
  . tauto;


protected class IsGenerated (F : Kripke.Frame) (R : { s : Set F.World // s.Nonempty }) where
  roots_generates : ∀ w ∉ R.1, ∃ r ∈ R.1, F.Rel.TransGen r w

protected class IsRootedBy (F : Kripke.Frame) (r : outParam F.World) where
  root_generates : ∀ w ≠ r, F.Rel.TransGen r w

protected class IsRooted (F : Frame) where
  exists_root : ∃ r, F.IsRootedBy r

instance {r : outParam F.World} [F.IsRootedBy r] : F.IsRooted := ⟨by use r⟩

protected noncomputable def root (F : Frame) [F.IsRooted] : F.World := Classical.choose Frame.IsRooted.exists_root

lemma root_generates [F.IsRooted] : ∀ x ≠ F.root, F.root ≺^+ x := by
  apply @Frame.IsRooted.exists_root F _ |>.choose_spec |>.root_generates;

lemma root_generates' [F.IsRooted] [F.IsTransitive] : ∀ x ≠ F.root, F.root ≺ x := by
  intro x hx;
  exact Rel.TransGen.unwrap $ F.root_generates _ hx;

/-- `Frame.root` is first. -/
@[simp] lemma root_first [F.IsRooted] [F.IsTransitive] [F.IsReflexive] : ∀ x, F.root ≺ x := by
  intro x;
  by_cases hx : x = F.root;
  . subst hx; apply F.refl;
  . exact F.root_generates' x hx;


/-- Explicit version of `root_generates` for rooted by `r`. -/
lemma root_generates! [F.IsRootedBy r] : ∀ x ≠ r, r ≺^+ x := IsRootedBy.root_generates

/-- Explicit version of `root_generates'` for rooted by `r`. -/
lemma root_genaretes'! [F.IsTransitive] [F.IsRootedBy r] : ∀ x ≠ r, r ≺ x := by
  intro x hx;
  apply Rel.TransGen.unwrap;
  exact IsRootedBy.root_generates x hx;

@[simp] lemma root_first! [F.IsRootedBy r] [F.IsTransitive] [F.IsReflexive] : ∀ x, r ≺ x := by
  intro x;
  by_cases hx : x = r;
  . subst hx; apply F.refl;
  . exact F.root_genaretes'! x hx;


instance [F.IsRooted] : F.IsRootedBy F.root where
  root_generates := by apply @Frame.IsRooted.exists_root F _ |>.choose_spec |>.root_generates;


instance [rooted : F.IsRootedBy r] : F.IsGenerated (⟨{r}, by tauto⟩) where
  roots_generates := by
    rintro x hx;
    use r;
    constructor;
    . tauto;
    . exact rooted.root_generates x hx;



namespace isRooted

instance isConvergent [F.IsRooted] [F.IsPiecewiseConvergent] [F.IsTransitive] [F.IsReflexive] : F.IsConvergent := ⟨by
  rintro x y nexy;
  apply F.p_convergent (x := F.root) ?_ ?_ nexy;
  . by_cases ex : x = F.root;
    . subst ex; apply F.refl;
    . apply F.root_generates';
      tauto;
  . by_cases ey : y = F.root;
    . subst ey; apply F.refl;
    . apply F.root_generates';
      tauto;
⟩

instance isStronglyConvergent [F.IsRooted] [F.IsPiecewiseStronglyConvergent] [F.IsReflexive] [F.IsTransitive] : F.IsStronglyConvergent := ⟨by
  rintro x y;
  apply F.ps_convergent (x := F.root) ?_ ?_;
  . by_cases ex : x = F.root;
    . subst ex; apply F.refl;
    . apply F.root_generates';
      tauto;
  . by_cases ey : y = F.root;
    . subst ey; apply F.refl;
    . apply F.root_generates';
      tauto;
⟩

instance isConnected [F.IsRooted] [F.IsPiecewiseConnected] [F.IsReflexive] [F.IsTransitive] : F.IsConnected := ⟨by
  rintro x y;
  suffices x ≠ y → x ≺ y ∨ y ≺ x by tauto;
  intro nexy;
  apply F.p_connected' (x := F.root) ?_ ?_ nexy;
  . by_cases ex : x = F.root;
    . subst ex; apply F.refl;
    . apply F.root_generates';
      tauto;
  . by_cases ey : y = F.root;
    . subst ey; apply F.refl;
    . apply F.root_generates';
      tauto;
⟩

instance isStronglyConnected [F.IsRooted] [F.IsPiecewiseStronglyConnected] [F.IsReflexive] [F.IsTransitive] : F.IsStronglyConnected := ⟨by
  rintro x y;
  apply F.ps_connected (x := F.root) ?_ ?_;
  . by_cases ex : x = F.root;
    . subst ex; apply F.refl;
    . apply F.root_generates';
      tauto;
  . by_cases ey : y = F.root;
    . subst ey; apply F.refl;
    . apply F.root_generates';
      tauto;
⟩

end isRooted


instance [rooted : F.IsRootedBy r] : (F^+).IsRootedBy r where
  root_generates := by
    intro x hx;
    exact Relation.TransGen.single $ rooted.root_generates x hx;


end Frame




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
  | single h => exact _root_.Relation.TransGen.single h;
  | @head a c ha hb hc =>
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
  | single h => exact Relation.TransGen.single h;
  | @head a c ha hb hc =>
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
  | single h => exact Relation.TransGen.single h;
  | head a b c => exact TransGen.head a c;

protected abbrev root : (F↾r).World := ⟨r, by tauto⟩

instance : (F↾r).IsRootedBy pointGenerate.root where
  root_generates := by
    rintro ⟨w, (rfl | Rrw)⟩ hw;
    . grind;
    . apply trans_rel_of_origin_trans_rel;
      exact Rrw;

instance : (F↾r).IsRooted := inferInstance

instance [F.IsFinite] : (F↾r).IsFinite := inferInstance

instance [DecidableEq F.World] : DecidableEq (F↾r).World := Subtype.instDecidableEq

instance isReflexive [F.IsReflexive] : (F↾r).IsReflexive where
  refl := by rintro ⟨x, (rfl | hx)⟩ <;> exact Std.Refl.refl x;

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
  { dsimp at Rxy; apply Std.Asymm.asymm _ _ Rxy; }
⟩

instance isPiecewiseConvergent [F.IsPiecewiseConvergent] : (F↾r).IsPiecewiseConvergent := ⟨by
  rintro ⟨x, (rfl | Rrx)⟩ ⟨y, (rfl | Rry)⟩ ⟨z, (rfl | Rrz)⟩ Rxy Rxz nexy;
  case inl.inr.inr | inr.inr.inr =>
    have ⟨u, Ryu, Rzu⟩ := F.p_convergent Rxy Rxz $ by simp_all;
    use ⟨u, by right; apply Rel.TransGen.tail Rry Ryu⟩;
  all_goals
  . have ⟨u, _⟩ := F.p_convergent Rxy Rxz $ by simp_all;
    use ⟨u, by tauto⟩;
⟩

instance isPiecewiseStronglyConvergent [F.IsPiecewiseStronglyConvergent] : (F↾r).IsPiecewiseStronglyConvergent := ⟨by
  rintro ⟨x, (rfl | Rrx)⟩ ⟨y, (rfl | Rry)⟩ ⟨z, (rfl | Rrz)⟩ Rxy Rxz;
  case inl.inl.inl => tauto;
  case inr.inr.inr | inl.inr.inr =>
    obtain ⟨u, Ryu, Rzu⟩ := F.ps_convergent Rxy Rxz;
    use ⟨u, ?_⟩;
    . right; exact Rel.TransGen.tail Rry Ryu;
  all_goals
  . obtain ⟨u, Ryu, Rzu⟩ := F.ps_convergent Rxy Rxz;
    use ⟨u, by tauto⟩;
⟩

instance isPiecewiseConnected [F.IsPiecewiseConnected] : (F↾r).IsPiecewiseConnected := by
  apply IsPiecewiseConnected.mk';
  rintro ⟨x, (rfl | Rrx)⟩ ⟨y, (rfl | Rry)⟩ ⟨z, (rfl | Rrz)⟩ Rxy Rxz nexy;
  any_goals tauto;
  all_goals exact F.p_connected' Rxy Rxz $ by simp_all;;

instance isPiecewiseStronglyConnected [F.IsPiecewiseStronglyConnected] : (F↾r).IsPiecewiseStronglyConnected := ⟨by
  rintro ⟨x, (rfl | Rrx)⟩ ⟨y, (rfl | Rry)⟩ ⟨z, (rfl | Rrz)⟩ Rxy Rxz;
  any_goals tauto;
  all_goals exact F.ps_connected Rxy Rxz;
⟩

instance isConvergent [F.IsPiecewiseConvergent] [F.IsTransitive] [F.IsReflexive] : (F↾r).IsConvergent := isRooted.isConvergent

instance isStronglyConvergent [F.IsPiecewiseStronglyConvergent] [F.IsTransitive] [F.IsReflexive] : (F↾r).IsStronglyConvergent := isRooted.isStronglyConvergent

instance isConnected [F.IsPiecewiseConnected] [F.IsReflexive] [F.IsTransitive] : (F↾r).IsConnected := isRooted.isConnected

instance isStronglyConnected [F.IsPiecewiseStronglyConnected] [F.IsReflexive] [F.IsTransitive] : (F↾r).IsStronglyConnected := isRooted.isStronglyConnected


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

instance : (M↾r).IsRootedBy pointGenerate.root := by dsimp [Model.pointGenerate]; infer_instance;

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
instance isConvergent [M.IsPiecewiseConvergent] [M.IsReflexive] [M.IsTransitive] : (M↾r).IsConvergent := Frame.pointGenerate.isConvergent
instance isStronglyConvergent [M.IsPiecewiseStronglyConvergent] [M.IsReflexive] [M.IsTransitive] : (M↾r).IsStronglyConvergent := Frame.pointGenerate.isStronglyConvergent
instance isConnected [M.IsPiecewiseConnected] [M.IsReflexive] [M.IsTransitive] : (M↾r).IsConnected := Frame.pointGenerate.isConnected
instance isStronglyConnected [M.IsPiecewiseStronglyConnected] [M.IsReflexive] [M.IsTransitive] : (M↾r).IsStronglyConnected := Frame.pointGenerate.isStronglyConnected

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

lemma modal_equivalent_of_rel (r : M.World) (x : M.World) (Rrx : r ≺ x) : ModalEquivalent (M₁ := M↾r) (M₂ := M) ⟨x, by tauto⟩ x
  := PseudoEpimorphism.modal_equivalence Model.pointGenerate.pMorphism _

lemma modal_equivalent_at_root (r : M.World) : ModalEquivalent (M₁ := M↾r) (M₂ := M) ⟨r, by tauto⟩ r
  := PseudoEpimorphism.modal_equivalence Model.pointGenerate.pMorphism _

lemma modal_equivalent' (r : M.World) (x : M↾r) : ModalEquivalent (M₁ := M↾r) (M₂ := M) x x.1
  := PseudoEpimorphism.modal_equivalence Model.pointGenerate.pMorphism _

end Model.pointGenerate

end Kripke

end LO.Modal
end
