import Foundation.Modal.Kripke.Preservation

namespace LO.Modal

namespace Kripke

open Formula.Kripke
open Relation

class Frame.IsGenerated (F : Kripke.Frame) (R : Set F.World) (roots_nonempty : R.Nonempty := by tauto_set) where
  roots_generates : ∀ w ∉ R, ∃ r ∈ R, r ≺^+ w

class Frame.IsRooted (F : Kripke.Frame) (r : outParam F.World) where
  root_generates : ∀ w ≠ r, r ≺^+ w

namespace Frame.IsRooted

variable {F : Frame} {r : F.World} [rooted : F.IsRooted r]

instance [rooted : F.IsRooted r] : F.IsGenerated {r} where
  roots_generates := by
    rintro x hx;
    use r;
    constructor;
    . tauto;
    . exact rooted.root_generates x hx;

lemma direct_rooted_of_trans [IsTrans _ F.Rel] : ∀ x ≠ r, r ≺ x := by
  intro x hx;
  obtain ⟨n, hn, Rrx⟩ := Relation.TransGen.exists_iterate.mp $ rooted.root_generates x hx;
  exact Rel.iterate.unwrap_of_trans hn Rrx;

end Frame.IsRooted

instance Frame.mkTransClosure.IsRooted {F : Frame} {r : F.World} [rooted : F.IsRooted r] : (F^+).IsRooted r where
  root_generates := by
    intro x hx;
    exact Relation.TransGen.single $ rooted.root_generates x hx;

namespace Frame


def setGenerate (F : Kripke.Frame) (R : Set F.World) (R_nonempty : R.Nonempty := by tauto_set) : Kripke.Frame where
  World := { w // w ∈ R ∨ ∃ r ∈ R, r ≺^+ w }
  Rel x y := x.1 ≺ y.1
  world_nonempty := by
    let ⟨r, hr⟩ := R_nonempty;
    exact ⟨r, Or.inl hr⟩

namespace setGenerate

variable {F : Frame} {R : Set F.World} {R_nonempty : R.Nonempty}

protected abbrev roots : Set (F.setGenerate R R_nonempty) := { r | r.1 ∈ R }

@[simp]
lemma roots_nonempty : (setGenerate.roots (F := F) (R := R) (R_nonempty := R_nonempty)).Nonempty := by
  obtain ⟨r, hr⟩ := R_nonempty;
  use ⟨r, by tauto⟩;
  tauto;

lemma trans_rel_of_origin_trans_rel {hx : x ∈ R ∨ ∃ r ∈ R, r ≺^+ x} {hy : y ∈ R ∨ ∃ r ∈ R, r ≺^+ y} (Rxy : x ≺^+ y)
  : (RelTrans (F := F.setGenerate R R_nonempty) ⟨x, hx⟩ ⟨y, hy⟩) := by
  induction Rxy using TransGen.head_induction_on with
  | base h => exact Relation.TransGen.single h;
  | @ih a c ha hb hc =>
    let b : (F.setGenerate R R_nonempty).World := ⟨c, by
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

instance instGenerated : (F.setGenerate R R_nonempty).IsGenerated (setGenerate.roots) (by simp) where
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
  World := { w // w = r ∨ r ≺^+ w }
  Rel x y := x.1 ≺ y.1
  world_nonempty := ⟨r, by tauto⟩
infix:100 "↾" => Frame.pointGenerate

namespace pointGenerate

variable {F : Frame} {r : F.World}

lemma trans_rel_of_origin_trans_rel {hx : x = r ∨ r ≺^+ x} {hy : y = r ∨ r ≺^+ y} (Rxy : x ≺^+ y)
  : (RelTrans (F := F↾r) ⟨x, hx⟩ ⟨y, hy⟩) := by
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

lemma origin_trans_rel_of_trans_rel {u v : (F↾r).World} (Ruv : u ≺^+ v) : u.1 ≺^+ v.1 := by
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

instance isRefl [IsRefl _ F] : IsRefl (F↾r).World (F↾r).Rel := ⟨by
  rintro ⟨x, (rfl | hx)⟩ <;>
  . have : x ≺ x := IsRefl.refl x;
    exact this;
⟩

instance isTrans [trans : IsTrans _ F] : IsTrans (F↾r).World (F↾r).Rel := ⟨by
  rintro ⟨x, (rfl | hx)⟩ ⟨y, (rfl | hy)⟩ ⟨z, (rfl | hz)⟩ hxy hyz;
  . assumption;
  . assumption;
  . have : z ≺ z := IsTrans.trans _ _ _ hxy hyz; exact this;
  . have : x ≺ z := IsTrans.trans _ _ _ hxy hyz; exact this;
  . assumption;
  . have : x ≺ z := IsTrans.trans _ _ _ hxy hyz; exact this;
  . have : x ≺ z := IsTrans.trans _ _ _ hxy hyz; exact this;
  . have : x ≺ z := IsTrans.trans _ _ _ hxy hyz; exact this;
⟩

lemma rel_antisymm (F_antisymm : AntiSymmetric F) : AntiSymmetric (F↾r).Rel := by
  rintro ⟨x, (rfl | hx)⟩ ⟨y, (rfl | hy)⟩ hxy hyx;
  all_goals aesop;

instance isAntisymm [IsAntisymm _ F] : IsAntisymm _ (F↾r).Rel := ⟨rel_antisymm IsAntisymm.antisymm⟩

instance isPreorder [IsPreorder _ F] : IsPreorder _ (F↾r) where

instance isPartialOrder [IsPartialOrder _ F] : IsPartialOrder _ (F↾r) where

instance isIrrefl [IsIrrefl _ F] : IsIrrefl _ (F↾r).Rel := ⟨by
  rintro ⟨x, (rfl | hx)⟩ h;
  . exact IsIrrefl.irrefl _ $ by simpa using h;
  . exact IsIrrefl.irrefl _ $ by simpa using h;
⟩

instance isAsymm [assym : IsAsymm _ F] : IsAsymm (F↾r).World (F↾r).Rel := ⟨by
  rintro ⟨x, (rfl | hx)⟩ ⟨y, (rfl | hy)⟩ Rxy <;>
  { dsimp at Rxy; apply IsAsymm.asymm _ _ Rxy; }
⟩

/-
instance isConfluent [IsConfluent _ F] : IsConfluent _ (F↾r).Rel := ⟨by
  rintro ⟨x, (rfl | hx)⟩ ⟨y, (rfl | hy)⟩ ⟨z, (rfl | hz)⟩ ⟨Rxy, Rxz⟩;
  . obtain ⟨w, _, _⟩ := IsConfluent.confl (x := z) (y := z) (z := z) (by tauto);
    use ⟨w, by right; apply Relation.TransGen.single; tauto⟩;
  . obtain ⟨w, _, _⟩ := @IsConfluent.confl y y z (by tauto);
    use ⟨w, by right; apply Relation.TransGen.single; tauto⟩;
  . obtain ⟨w, _, _⟩ := @IsConfluent.confl z y z (by tauto);
    use ⟨w, by right; apply Relation.TransGen.single; tauto⟩;
  . obtain ⟨w, _, _⟩ := @IsConfluent.confl x y z (by tauto);
    use ⟨w, by right; apply Relation.TransGen.tail hy $ by assumption⟩;
  . obtain ⟨w, _, _⟩ := @IsConfluent.confl x z z (by tauto);
    use ⟨w, by right; apply Relation.TransGen.single; tauto⟩;
  . obtain ⟨w, _, _⟩ := @IsConfluent.confl x z y (by tauto);
    use ⟨w, by right; apply Relation.TransGen.single $ by assumption⟩;
  . obtain ⟨w, _, _⟩ := @IsConfluent.confl x y z (by tauto);
    use ⟨w, by right; apply Relation.TransGen.single $ by assumption⟩;
  . obtain ⟨w, _, _⟩ := @IsConfluent.confl x y z (by tauto);
    use ⟨w, by right; apply Relation.TransGen.tail hy $ by assumption⟩;
⟩

instance isConnected (F_connected : Connected F) : Connected (F↾r).Rel := by
  rintro ⟨x, (rfl | hx)⟩ ⟨y, (rfl | hy)⟩ ⟨z, (rfl | hz)⟩ ⟨Rxy, Rxz⟩;
  . tauto;
  . tauto;
  . tauto;
  . have := @F_connected x y z (by tauto); tauto;
  . have := @F_connected x z z (by tauto); tauto;
  . have := @F_connected x z y (by tauto); tauto;
  . have := @F_connected x y z (by tauto); tauto;
  . have := @F_connected x y z (by tauto); tauto;
-/

instance isUniversal [refl : IsRefl _ F] [eucl : IsEuclidean _ F] : IsUniversal _ (F↾r).Rel := ⟨by
  rintro ⟨x, (rfl | hx)⟩ ⟨y, (rfl | hy)⟩;
  . apply IsRefl.refl;
  . exact hy.unwrap;
  . suffices x ≺ y by simpa;
    exact IsSymm.symm _ _ hx.unwrap;
  . suffices x ≺ y by simpa;
    exact IsEuclidean.euclidean hy.unwrap hx.unwrap;
⟩

def pMorphism : (F↾r) →ₚ F where
  toFun := λ ⟨x, _⟩ => x
  forth := by
    rintro ⟨x, (rfl | hx)⟩ ⟨y, (rfl | hy)⟩ hxy;
    repeat exact hxy;
  back := by
    rintro ⟨x, (rfl | hx)⟩ y Rwv;
    . simp at Rwv; use ⟨y, by tauto⟩
    . use ⟨y, by right; exact Relation.TransGen.tail hx Rwv⟩;

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

end pointGenerate

end Frame


def Model.pointGenerate (M : Kripke.Model) (r : M.World) : Model := ⟨M.toFrame↾r, λ w a => M.Val w.1 a⟩
infix:100 "↾" => Model.pointGenerate

namespace Model.pointGenerate

variable {M : Kripke.Model} {r : M.World}

instance [M.IsFinite] : (M↾r).IsFinite := by
  simp [Model.pointGenerate];
  infer_instance;

protected abbrev root : (M↾r).World := ⟨r, by tauto⟩

instance : (M↾r).IsRooted pointGenerate.root := by
  simp [Model.pointGenerate];
  infer_instance;

protected def pMorphism : (M↾r) →ₚ M := by
  apply Model.PseudoEpimorphism.ofAtomic (Frame.pointGenerate.pMorphism (F := M.toFrame) (r := r));
  simp only [pointGenerate, Frame.pointGenerate, Subtype.forall];
  rintro p x (rfl | Rrx) <;> tauto;

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

protected def bisimulation (r : M.World) : (M↾r) ⇄ M := Model.pointGenerate.pMorphism.bisimulation

lemma modal_equivalent_at_root (r : M.World) : ModalEquivalent (M₁ := M↾r) (M₂ := M) ⟨r, by tauto⟩ r
  := PseudoEpimorphism.modal_equivalence (Model.pointGenerate.pMorphism) pointGenerate.root

end Model.pointGenerate

end Kripke

end LO.Modal
