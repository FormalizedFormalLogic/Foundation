module

public import Foundation.Modal.Kripke.Preservation
public import Foundation.Modal.Kripke.Asymmetric
public import Foundation.Modal.Kripke.AxiomWeakPoint2
public import Foundation.Modal.Kripke.AxiomPoint3

@[expose] public section

namespace LO.Modal

namespace Kripke


namespace Frame

variable {F : Kripke.Frame} {r x y z : F.World}

section

protected abbrev IsConvergent (F : Frame) := _root_.IsConvergent F.Rel
lemma convergent [F.IsConvergent] : ∀ {x y : F.World}, x ≠ y → ∃ u, x ≺ u ∧ y ≺ u := by apply IsConvergent.convergent

protected abbrev IsStronglyConvergent (F : Frame) := _root_.IsStronglyConvergent F.Rel
lemma strongly_convergent [F.IsStronglyConvergent] : ∀ x y : F.World, ∃ u, x ≺ u ∧ y ≺ u := by apply IsStronglyConvergent.s_convergent


protected abbrev IsStronglyConnected (F : Frame) := _root_.Std.Total F.Rel
lemma s_connected [F.IsStronglyConnected] : ∀ {x y : F.World}, x ≺ y ∨ y ≺ x := by apply Std.Total.total

protected abbrev IsConnected (F : Frame) := Std.Trichotomous F.Rel
lemma connected [F.IsConnected] : ∀ x y : F.World, x ≺ y ∨ x = y ∨ y ≺ x := by grind [Std.Trichotomous.trichotomous (r := F.Rel)]
lemma connected' [F.IsConnected] : ∀ x y : F.World, x ≠ y → x ≺ y ∨ y ≺ x := by
  rintro x y nexy;
  rcases F.connected x y with (Rxy | rfl | Ryx);
  . tauto;
  . contradiction;
  . tauto;

end


abbrev IsRoot (F : Frame) (r : F.World) := ∀ x : F.World, x ≠ r → r ≺ x

abbrev Root (F : Frame) := { r // F.IsRoot r }


/-- Frame `F` is rooted by some root(s) (possibly have multiple roots). -/
abbrev IsRooted (F : Frame) := Inhabited F.Root

/-- Frame `F` is rooted by `F.root`. -/
abbrev IsPointRooted (F : Frame) := Unique F.Root


section

abbrev root (F : Frame) [F.IsRooted] : F.Root := Inhabited.default

instance instPointRooted_of_isRooted_of_isIrreflexive_of_isTransitive [F.IsIrreflexive] [F.IsTransitive] [F.IsRooted] : F.IsPointRooted where
  uniq r := by
    by_contra hr;
    exact F.irrefl r $ F.trans (r.2 F.root (by grind)) (F.root.2 r.1 (by grind));

end



abbrev transRoot (F : Frame) := { r : F.World // ∀ x : F.World, x ≠ r → r ≺^+ x }

def transRoot.toRoot {F : Frame} [F.IsTransitive] (r : F.transRoot) : F.Root := ⟨r.1, by
  intro x hx;
  apply Rel.TransGen.unwrap;
  apply r.2;
  exact hx;
⟩

abbrev IsTransRooted (F : Frame) := Nonempty F.transRoot

instance [F.IsTransRooted] [F.IsTransitive] : Nonempty F.Root := ⟨Nonempty.some (by assumption) |> transRoot.toRoot⟩



section

attribute [grind .] Frame.refl

instance instConvergentOfIsRootedOfReflexive [F.IsRooted] [F.IsReflexive] [F.IsPiecewiseConvergent] : F.IsConvergent := ⟨by
  rintro x y nxy;
  apply F.p_convergent (x := F.root) <;> grind;
⟩

instance instStronglyConvergentOfIsRootedOfReflexive [F.IsRooted] [F.IsReflexive] [F.IsPiecewiseStronglyConvergent] : F.IsStronglyConvergent := ⟨by
  rintro x y;
  apply F.ps_convergent (x := F.root) <;> grind;
⟩

instance instConnectedOfIsRootedOfReflexive [F.IsRooted] [F.IsPiecewiseConnected] [F.IsReflexive] : F.IsConnected := ⟨by
  suffices ∀ x y : F, x ≠ y → x ≺ y ∨ y ≺ x by grind;
  rintro x y nexy;
  apply F.p_connected' (x := F.root) <;> grind;
⟩

instance instStronglyConnectedOfIsRootedOfReflexive [F.IsRooted] [F.IsPiecewiseStronglyConnected] [F.IsReflexive] : F.IsStronglyConnected := ⟨by
  rintro x y;
  apply F.ps_connected (x := F.root) <;> grind;
⟩

end

instance [F.IsRooted] : (F^+).IsRooted := ⟨⟨F.root, fun x hx ↦ Relation.TransGen.single (by grind)⟩⟩


abbrev pointGenerate (F : Kripke.Frame) (r : F.World) : Kripke.Frame where
  World := { x // x = r ∨ r ≺ x }
  Rel x y := x.1 ≺ y.1
  world_nonempty := ⟨r, by tauto⟩
infix:80 "↾" => pointGenerate


namespace pointGenerate

@[grind <=]
lemma rel_of_origin_rel {hx hy} (Rxy : x ≺ y) : ((F↾r).Rel ⟨x, hx⟩ ⟨y, hy⟩) := by
  exact Rxy

attribute [grind <=] Frame.trans Frame.antisymm
attribute [grind .] Frame.irrefl

instance : (F↾r).IsRooted where
  default := ⟨⟨r, by tauto⟩, by grind⟩;

instance [F.IsFinite] : (F↾r).IsFinite := inferInstance
instance [F.IsReflexive] : (F↾r).IsReflexive := ⟨by grind⟩
instance [F.IsTransitive] : (F↾r).IsTransitive := ⟨by grind⟩
instance [F.IsAntisymmetric] : (F↾r).IsAntisymmetric := ⟨by grind⟩
instance [F.IsIrreflexive] : (F↾r).IsIrreflexive := ⟨by grind⟩
instance [F.IsAsymmetric] : (F↾r).IsAsymmetric := ⟨by grind⟩
instance [F.IsReflexive] [F.IsTransitive] : (F↾r).IsPreorder where
instance [F.IsPartialOrder] : (F↾r).IsPartialOrder where

instance [F.IsTransitive] [F.IsPiecewiseConvergent] : (F↾r).IsPiecewiseConvergent := by
  constructor;
  rintro x y z Rxy Rxz nexy;
  obtain ⟨u, _⟩ := F.p_convergent Rxy Rxz $ by grind;
  use ⟨u, by grind⟩;
instance [F.IsReflexive] [F.IsTransitive] [F.IsPiecewiseConvergent] : (F↾r).IsConvergent := (F↾r).instConvergentOfIsRootedOfReflexive

instance [F.IsTransitive] [F.IsPiecewiseStronglyConvergent] : (F↾r).IsPiecewiseStronglyConvergent := by
  constructor;
  rintro x y z Rxy Rxz;
  obtain ⟨u, _⟩ := F.ps_convergent Rxy Rxz;
  use ⟨u, by grind⟩;
instance [F.IsReflexive] [F.IsTransitive] [F.IsPiecewiseStronglyConvergent] : (F↾r).IsStronglyConvergent := (F↾r).instStronglyConvergentOfIsRootedOfReflexive

instance [F.IsTransitive] [F.IsPiecewiseConnected] : (F↾r).IsPiecewiseConnected := by
  constructor;
  rintro x y z Rxy Rxz;
  grind [F.p_connected];
instance [F.IsTransitive] [F.IsPiecewiseConnected] [F.IsReflexive] : (F↾r).IsConnected := (F↾r).instConnectedOfIsRootedOfReflexive

instance [F.IsTransitive] [F.IsStronglyConnected] : (F↾r).IsStronglyConnected := by
  constructor;
  rintro x y;
  grind [F.ps_connected];
instance [F.IsTransitive] [F.IsPiecewiseStronglyConnected] [F.IsReflexive] : (F↾r).IsStronglyConnected := (F↾r).instStronglyConnectedOfIsRootedOfReflexive

instance [F.IsIrreflexive] [F.IsTransitive] : (F↾r).IsPointRooted := instPointRooted_of_isRooted_of_isIrreflexive_of_isTransitive

protected abbrev pMorphism (F : Kripke.Frame) [F.IsTransitive] (r : F) : (F↾r) →ₚ F where
  toFun := λ ⟨x, _⟩ => x
  forth := by grind;
  back {x y} Rxy := by use ⟨y, by grind⟩

end pointGenerate



abbrev pointTransGenerate (F : Kripke.Frame) (r : F.World) : Kripke.Frame where
  World := { x // x = r ∨ r ≺^+ x }
  Rel x y := x.1 ≺ y.1
  world_nonempty := ⟨r, by tauto⟩
infix:80 "↾⁺" => pointTransGenerate

namespace pointTransGenerate

@[grind <=]
lemma trans_rel_of_origin_trans_rel {hx hy} (Rxy : x ≺^+ y)
  : ((F↾⁺r)^+.Rel ⟨x, hx⟩ ⟨y, hy⟩) := by
  induction Rxy using Relation.TransGen.head_induction_on with
  | single h =>
    exact Relation.TransGen.single h;
  | @head a c ha hb hc =>
    exact Relation.TransGen.head (b := ⟨c, by grind⟩) ha hc;

instance : (F↾⁺r).IsTransRooted := ⟨⟨⟨r, by tauto⟩, by grind⟩⟩

end pointTransGenerate


end Frame


namespace Model

variable {M : Kripke.Model} {r x y z : M.World}

abbrev pointGenerate (M : Kripke.Model) (r : M.World) : Kripke.Model where
  toFrame := (M.toFrame↾r)
  Val p w := M.Val p w.1
infix:80 "↾" => pointGenerate

namespace pointGenerate

protected abbrev pMorphism (M : Kripke.Model) [M.IsTransitive] (r : M) : (M↾r) →ₚ M := by
  apply Model.PseudoEpimorphism.ofAtomic (Frame.pointGenerate.pMorphism M.toFrame r);
  simp;

protected abbrev bisimulation (M : Kripke.Model) [M.IsTransitive] (r : M.World) : (M↾r) ⇄ M := Model.pointGenerate.pMorphism M r |>.bisimulation

variable [M.IsTransitive]

lemma modal_equivalent (r : M.World) (x : M↾r) : ModalEquivalent (M₁ := M↾r) (M₂ := M) x x.1
  := by apply Model.pointGenerate.pMorphism M r |>.modal_equivalence;

lemma modal_equivalent_at_root (r : M.World) : ModalEquivalent (M₁ := M↾r) (M₂ := M) ⟨r, by grind⟩ r
  := by apply modal_equivalent

end pointGenerate


end Model


end Kripke


end LO.Modal
