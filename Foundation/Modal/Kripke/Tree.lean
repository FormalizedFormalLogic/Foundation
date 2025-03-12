import Foundation.Vorspiel.Chain
import Foundation.Modal.Kripke.Rooted

namespace LO.Modal

namespace Kripke


class Frame.IsTree (F : Kripke.Frame) (r : F.World) extends F.IsRooted r where
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
  Rel X Y := ∃ z, Y.1 = X.1 ++ [z]
  world_nonempty := ⟨[r], (by simp)⟩

namespace Frame.treeUnravelling

variable {X Y : (F.mkTreeUnravelling r).World}

@[simp]
lemma not_nil : X.1 ≠ [] := by
  by_contra;
  have := X.2.1;
  simp_all;

lemma rel_length (h : X ≺ Y) : X.1.length < Y.1.length := by
  obtain ⟨z, hz⟩ := h;
  simp_all;

lemma transrel_def : X ≺^+ Y ↔ ∃ l ≠ [], Y.1 = X.1 ++ l ∧ (List.Chain' F.Rel (X.1 ++ l)) := by
  constructor;
  . intro h;
    induction h using Relation.TransGen.head_induction_on with
    | base RZY =>
      obtain ⟨w, hw⟩ := RZY;
      use [w];
      refine ⟨by tauto, by tauto, ?_⟩;
      rw [←hw];
      exact Y.2.2;
    | @ih Z U RZU UY ih =>
      obtain ⟨w, hw⟩ := RZU;
      obtain ⟨l, ⟨_, _, hl₃⟩⟩ := ih;
      use w :: l;
      refine ⟨by tauto, by simp_all, ?_⟩;
      rwa [hw, (show Z.1 ++ [w] ++ l = Z.1 ++ (w :: l) by simp)] at hl₃;
  . rintro ⟨l, hl⟩;
    induction l using List.induction_with_singleton generalizing X with
    | hnil => tauto;
    | hsingle z =>
      apply Relation.TransGen.single;
      use z;
      tauto;
    | hcons z zs h ih =>
      rcases hl with ⟨_, hl₂, hl₃⟩;
      apply Relation.TransGen.head (b := ⟨X.1 ++ [z], by
        constructor;
        . obtain ⟨l, hl⟩ := X.2.1;
          use (l ++ [z]);
          rw [←hl];
          simp;
        . apply List.Chain'.prefix hl₃;
          use zs;
          simp_all;
      ⟩);
      . use z;
      . apply ih;
        refine ⟨by simp_all, by simpa, by simpa⟩;

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
    simp only [ne_eq, List.cons_append, List.nil_append, List.cons.injEq, true_and, List.head_cons, existsAndEq];
    constructor;
    . by_contra hC;
      subst hC;
      simp at hn;
    . assumption;

end Frame.treeUnravelling


abbrev Frame.mkTransTreeUnravelling (F : Frame) (r : F.World) := (F.mkTreeUnravelling r)^+


namespace Frame.mkTransTreeUnravelling

variable {X Y : (F.mkTransTreeUnravelling r).World}

@[simp]
lemma not_nil : X.1 ≠ [] := by
  by_contra;
  have := X.2.1;
  simp_all;

lemma rel_length (Rxy : X ≺ Y) : X.1.length < Y.1.length := by
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

lemma rel_def : X ≺ Y ↔ (∃ l ≠ [], Y.1 = X.1 ++ l ∧ (List.Chain' F.Rel (X.1 ++ l))) := treeUnravelling.transrel_def

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

protected lemma modal_equivalence_at_root (M : Kripke.Model) (M_trans : Transitive M.toFrame.Rel) (r : M.World)
  : ModalEquivalent (M₁ := M.mkTransTreeUnravelling r) (M₂ := M) (mkTransTreeUnravelling.root) r
  := Model.PseudoEpimorphism.modal_equivalence (Model.mkTransTreeUnravelling.pMorphism M M_trans r) (mkTransTreeUnravelling.root)

end Model.mkTransTreeUnravelling



end TreeUnravelling

end Kripke

end LO.Modal
