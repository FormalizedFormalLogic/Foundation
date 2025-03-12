import Foundation.Vorspiel.Chain
import Foundation.Modal.Kripke.Rooted

namespace LO.Modal

namespace Kripke


class Frame.IsTree (F : Kripke.Frame) (root : F.World) extends F.IsRooted root where
  protected rel_assymetric : Assymetric F.Rel
  protected rel_transitive : Transitive F.Rel

namespace Frame.IsTree

variable {F : Frame} {r : F.World}

protected lemma rel_irreflexive [F.IsTree r] : Irreflexive F.Rel := irreflexive_of_assymetric (IsTree.rel_assymetric r)

end Frame.IsTree

class Frame.IsFiniteTree (F : Kripke.Frame) (r : F.World) extends F.IsFinite, F.IsTree r where



section TreeUnravelling

variable {F : Kripke.Frame} {r : F.World}

def Frame.mkTreeUnravelling (F : Frame) (r : F.World) : Kripke.Frame where
  World := { c : List F.World // [r] <+: c ∧ c.Chain' F.Rel }
  Rel cx cy := ∃ z, cy.1 = cx.1 ++ [z]
  world_nonempty := ⟨[r], (by simp)⟩

namespace Frame.treeUnravelling

@[simp]
lemma not_nil {c : (F.mkTreeUnravelling r).World} : c.1 ≠ [] := by
  have := c.2.1;
  by_contra;
  simp_all;

lemma rel_length {x y : (F.mkTreeUnravelling r).World} (h : x ≺ y) : x.1.length < y.1.length := by
  obtain ⟨z, hz⟩ := h;
  simp_all;


lemma transrel_def {cx cy : (F.mkTreeUnravelling r).World} : cx ≺^+ cy ↔ ∃ l ≠ [], cy.1 = cx.1 ++ l ∧ (List.Chain' F.Rel (cx.1.head (by simp) :: l)) := by
  constructor;
  . intro h;
    induction h using Relation.TransGen.head_induction_on with
    | base Rac =>
      obtain ⟨z, hz⟩ := Rac;
      use [z];
      refine ⟨by tauto, by tauto, ?_⟩;
      . sorry;
        /-
        have := cy.2.2;
        rw [hz] at this;
        have := List.chain'_append.mp this;
        simp at this;
        simp;
        -/
    | ih Rac b hc =>
      obtain ⟨z, hz⟩ := Rac;
      obtain ⟨l, ⟨hl₁, hl₂⟩⟩ := hc;
      use z :: l;
      refine ⟨?_, ?_, ?_⟩;
      . simp_all;
      . simp_all;
      . sorry;
  . rintro ⟨l, hl⟩;
    induction l generalizing cx with
    | nil => tauto;
    | cons z zs ih =>
      simp at hl;
      have := @ih ⟨[r, z], by sorry⟩
      apply Relation.TransGen.head;
      . use z;
        sorry;
      . sorry;
      . sorry;

protected lemma rel_irreflexive : Irreflexive (F.mkTreeUnravelling r).Rel := by
  intro x; simp [Frame.mkTreeUnravelling];

protected lemma rel_assymetric : Assymetric (F.mkTreeUnravelling r).Rel := by
  rintro x y hxy;
  by_contra hyx;
  replace hxy := rel_length hxy;
  replace hyx := rel_length hyx;
  exact hxy.not_lt hyx;

protected def pMorphism (F : Frame) (r : F) : F.mkTreeUnravelling r →ₚ F where
  toFun c := c.1.getLast (by simp)
  forth {cx cy} h := by
    obtain ⟨z, hz⟩ := h;
    have ⟨_, _, h⟩ := @List.chain'_append _ F.Rel cx.1 [z] |>.mp (by rw [←hz]; exact cy.2.2);
    refine h (cx.1.getLast (by aesop)) ?hx (cy.1.getLast (by aesop)) ?hy;
    . exact List.getLast?_eq_getLast_of_ne_nil (by simp);
    . simp;
      convert @List.getLast_append_singleton (l := cx.1) (a := z) |>.symm;
  back {cx y} h := by
    simp_all;
    use ⟨cx.1 ++ [y], ?_⟩;
    . constructor;
      . simp;
      . use y;
    . constructor;
      . obtain ⟨i, hi⟩ := cx.2.1;
        use (i ++ [y]);
        simp_rw [←List.append_assoc, hi];
      . apply List.Chain'.append;
        . exact cx.2.2;
        . simp;
        . intro z hz; simp;
          convert h;
          exact List.mem_getLast?_eq_getLast hz |>.2;

protected abbrev root : (F.mkTreeUnravelling r).World := ⟨[r], by tauto⟩

instance : (F.mkTreeUnravelling r).IsRooted treeUnravelling.root where
  root_generates := by
    rintro ⟨_, ⟨l, rfl⟩, l_chain⟩ hn;
    apply transrel_def.mpr;
    aesop;

end Frame.treeUnravelling


abbrev Frame.mkTransTreeUnravelling (F : Frame) (r : F.World) := (F.mkTreeUnravelling r)^+


namespace Frame.mkTransTreeUnravelling

@[simp]
lemma not_nil {c : (F.mkTransTreeUnravelling r).World} : c.1 ≠ [] := by
  by_contra;
  have := c.2.1;
  simp_all;

lemma rel_length {x y : (F.mkTransTreeUnravelling r).World} (Rxy : x ≺ y) : x.1.length < y.1.length := by
  induction Rxy with
  | single Rxy => exact treeUnravelling.rel_length Rxy;
  | tail _ h ih => have := treeUnravelling.rel_length h; omega;

protected lemma rel_transitive : Transitive (F.mkTransTreeUnravelling r) := Frame.RelTransGen.transitive

protected lemma rel_asymmetric : Assymetric (F.mkTransTreeUnravelling r) := by
  rintro x y hxy;
  by_contra hyx;
  replace hxy := rel_length hxy;
  replace hyx := rel_length hyx;
  exact hxy.not_lt hyx;

lemma rel_def {x y : (F.mkTransTreeUnravelling r).World} : x ≺ y ↔ (x.1.length < y.1.length ∧ x.1 <+: y.1) := by
  constructor;
  . intro Rxy;
    induction Rxy with
    | single Rxy =>
      obtain ⟨z, hz⟩ := Rxy;
      rw [hz];
      constructor;
      . simp;
      . use [z];
    | tail _ h ih =>
      obtain ⟨w, hw⟩ := h;
      obtain ⟨_, ⟨zs, hzs⟩⟩ := ih;
      rw [hw, ←hzs];
      constructor;
      . simp;
      . use zs ++ [w];
        simp [List.append_assoc];
  . replace ⟨xs, ⟨ws, hw⟩, hx₂⟩ := x;
    replace ⟨ys, ⟨vs, hv⟩, hy₂⟩ := y;
    subst hw hv;
    rintro ⟨hl, ⟨zs, hzs⟩⟩;
    simp at hzs;
    induction zs using List.induction_with_singleton generalizing ws vs with
    | hnil => simp_all;
    | hsingle z =>
      apply Relation.TransGen.single;
      use z;
      simp_all;
    | hcons z zs h ih =>
      simp_all;
      refine Relation.TransGen.head ?h₁ $ ih (ws ++ [z]) vs ?h₂ ?h₃ ?h₄ ?h₅;
      . use z; simp;
      . apply List.Chain'.prefix hy₂;
        use zs; simp_all;
      . exact hy₂;
      . rw [←hzs]; simp;
        by_contra hC;
        simp_all;
      . simp_all;


abbrev pMorphism (F : Frame) (F_trans : Transitive F.Rel) (r : F) : (F.mkTransTreeUnravelling r) →ₚ F := (treeUnravelling.pMorphism F r).TransitiveClosure F_trans

protected abbrev root : (F.mkTransTreeUnravelling r).World := treeUnravelling.root

instance instIsRooted : (F.mkTransTreeUnravelling r).IsRooted (mkTransTreeUnravelling.root) := inferInstance

instance instIsTree {F : Frame} [DecidableEq F.World] [F.IsFinite] {r : F.World} (F_trans : Transitive F) (F_irrefl : Irreflexive F)
  : (F.mkTransTreeUnravelling r).IsFiniteTree (mkTransTreeUnravelling.root) where
  root_generates := by
    intro w;
    exact Frame.mkTransTreeUnravelling.instIsRooted.root_generates w;
  rel_transitive := mkTransTreeUnravelling.rel_transitive
  rel_assymetric := mkTransTreeUnravelling.rel_asymmetric
  world_finite := by
    suffices h : Finite { x // List.Chain' F.Rel x } by
      exact
       Finite.of_injective
       (β := { x // List.Chain' F.Rel x })
       (fun x => ⟨x.1, x.2.2⟩)
       (by rintro ⟨x, hx⟩ ⟨y, hy⟩; simp_all);
    apply List.chains_finite F_trans F_irrefl;

end Frame.mkTransTreeUnravelling


instance {F : Frame} [DecidableEq F.World] [F.IsFinite] {r : F.World} (F_trans : Transitive F) (F_irrefl : Irreflexive F)
  : ((F↾r).mkTransTreeUnravelling Frame.pointGenerate.root).IsFiniteTree (Frame.mkTransTreeUnravelling.root) :=
    Frame.mkTransTreeUnravelling.instIsTree
    (Frame.pointGenerate.rel_trans F_trans)
    (Frame.pointGenerate.rel_irrefl F_irrefl)


def Model.mkTreeUnravelling (M : Kripke.Model) (r : M.World) : Kripke.Model := ⟨M.toFrame.mkTreeUnravelling r, λ c a => M.Val (c.1.getLast (by simp)) a⟩

def Model.mkTreeUnravelling.pMorphism (M : Kripke.Model) (r : M.World) : (M.mkTreeUnravelling r) →ₚ M :=
  PseudoEpimorphism.ofAtomic (Frame.treeUnravelling.pMorphism M.toFrame r) $ by rfl;


def Model.mkTransTreeUnravelling (M : Kripke.Model) (r : M.World) : Kripke.Model := ⟨M.toFrame.mkTransTreeUnravelling r, λ c a => M.Val (c.1.getLast (by simp)) a⟩

namespace Model.mkTransTreeUnravelling

protected def pMorphism (M : Kripke.Model) (M_trans : Transitive M.toFrame.Rel) (r : M.World) : M.mkTransTreeUnravelling r →ₚ M :=
  PseudoEpimorphism.ofAtomic (Frame.mkTransTreeUnravelling.pMorphism M.toFrame M_trans r) $ by rfl;

protected abbrev root {M : Kripke.Model} {r : M.World} : (M.mkTransTreeUnravelling r).World := Frame.mkTransTreeUnravelling.root

/-
instance instTree_of_trans_irrefl {M : Model} [DecidableEq M.World] [M.IsFinite] {r : M.World} (F_trans : Transitive M.Rel) (F_irrefl : Irreflexive M.Rel)
  : Model.IsFiniteTree ((M↾r).mkTransTreeUnravelling  pointGenerate.root) (mkTransTreeUnravelling.root) := by
  have := @Frame.mkTransTreeUnravelling.instTree_of_trans_irrefl M.toFrame _ _ r F_trans F_irrefl;
  sorry;
-/

/-
instance instIsTree {M : Model} [DecidableEq M.World] [M.IsFinite] {r : M.World} (M_trans : Transitive M.Rel) (M_irrefl : Irreflexive M.Rel)
  : (M.mkTransTreeUnravelling r).IsFiniteTree (mkTransTreeUnravelling.root) where
  frame_isFiniteTree := @Frame.mkTransTreeUnravelling.instIsTree M.toFrame _ _ r M_trans M_irrefl;
-/

protected lemma modal_equivalence_at_root (M : Kripke.Model) (M_trans : Transitive M.toFrame.Rel) (r : M.World)
  : ModalEquivalent (M₁ := M.mkTransTreeUnravelling r) (M₂ := M) (mkTransTreeUnravelling.root) r
  := Model.PseudoEpimorphism.modal_equivalence (Model.mkTransTreeUnravelling.pMorphism M M_trans r) (mkTransTreeUnravelling.root)

end Model.mkTransTreeUnravelling



end TreeUnravelling

end Kripke

end LO.Modal
