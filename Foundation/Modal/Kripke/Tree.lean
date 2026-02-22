module

public import Foundation.Modal.Kripke.Root
public import Foundation.Vorspiel.List.Chain

@[expose] public section

namespace LO.Modal

namespace Kripke

section

variable {F : Kripke.Frame} {r : outParam F.World}

@[mk_iff] class Frame.IsTree (F : Kripke.Frame) [F.IsRooted] extends F.IsAsymmetric, F.IsTransitive where

@[mk_iff] class Frame.IsFiniteTree (F : Kripke.Frame) [F.IsRooted] extends F.IsFinite where

end

def Frame.mkTreeUnravelling (F : Frame) (r : F.World) : Kripke.Frame where
  World := { c : List F.World // [r] <+: c ∧ c.IsChain F.Rel }
  Rel X Y := ∃ z, Y.1 = X.1 ++ [z]
  world_nonempty := ⟨[r], (by simp)⟩

namespace Frame.treeUnravelling

variable {F : Kripke.Frame} {r : F.World}
variable {X Y : (F.mkTreeUnravelling r).World}

@[simp]
lemma not_nil : X.1 ≠ [] := by
  by_contra;
  have := X.2.1;
  simp_all;

@[grind →]
lemma rel_length (h : X ≺ Y) : X.1.length < Y.1.length := by
  obtain ⟨z, hz⟩ := h;
  simp_all;

lemma transrel_def : X ≺^+ Y ↔ ∃ l ≠ [], Y.1 = X.1 ++ l ∧ (List.IsChain F.Rel (X.1 ++ l)) := by
  constructor;
  . intro h;
    induction h using Relation.TransGen.head_induction_on with
    | single RZY =>
      obtain ⟨w, hw⟩ := RZY;
      use [w];
      refine ⟨by tauto, by tauto, ?_⟩;
      rw [←hw];
      exact Y.2.2;
    | @head Z U RZU UY ih =>
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
        . apply List.IsChain.prefix hl₃;
          use zs;
          simp_all;
      ⟩);
      . use z;
      . apply ih;
        refine ⟨by simp_all, by simpa, by simpa⟩;

protected instance isIrreflexive : (F.mkTreeUnravelling r).IsIrreflexive := ⟨by grind⟩
protected instance isAsymmetric : (F.mkTreeUnravelling r).IsAsymmetric := ⟨by grind⟩

protected def pMorphism (F : Frame) (r : F) : F.mkTreeUnravelling r →ₚ F where
  toFun c := c.1.getLast (by simp)
  forth {cx cy} h := by
    obtain ⟨z, hz⟩ := h;
    have ⟨_, _, h⟩ := @List.isChain_append _ F.Rel cx.1 [z] |>.mp (by rw [←hz]; exact cy.2.2);
    refine h (cx.1.getLast (by aesop)) ?hx (cy.1.getLast (by aesop)) ?hy;
    . exact List.getLast?_eq_getLast_of_ne_nil (by simp);
    . simp;
      convert @List.getLast_append_singleton (l := cx.1) (a := z) |>.symm;
  back {cx y} h := by
    use ⟨cx.1 ++ [y], ?_⟩;
    . constructor;
      . simp;
      . use y;
    . constructor;
      . obtain ⟨i, hi⟩ := cx.2.1;
        use (i ++ [y]);
        simp_rw [←List.append_assoc, hi];
      . apply List.IsChain.append;
        . exact cx.2.2;
        . simp;
        . intro z hz; simp;
          convert h;
          exact List.mem_getLast?_eq_getLast hz |>.2;

protected abbrev root (F : Kripke.Frame) (r : F.World) : (F.mkTreeUnravelling r).World := ⟨[r], by tauto⟩

instance : (F.mkTreeUnravelling r).IsTransRooted := by
  constructor;
  use treeUnravelling.root F r;
  rintro ⟨_, ⟨l, rfl⟩, l_chain⟩ hn;
  apply transrel_def.mpr;
  simp only [ne_eq, List.cons_append, List.nil_append, List.cons.injEq, true_and, existsAndEq];
  constructor;
  . by_contra hC;
    subst hC;
    simp at hn;
  . assumption;

end Frame.treeUnravelling


abbrev Frame.mkTransTreeUnravelling (F : Frame) (r : outParam F.World) := (F.mkTreeUnravelling r)^+

namespace Frame.mkTransTreeUnravelling

variable {F : Kripke.Frame} {r : outParam F.World}
variable {X Y : (F.mkTransTreeUnravelling r).World}

@[simp]
lemma not_nil : X.1 ≠ [] := by
  by_contra;
  have := X.2.1;
  simp_all;

@[grind →]
lemma rel_length (Rxy : X ≺ Y) : X.1.length < Y.1.length := by
  induction Rxy with
  | single Rxy => exact treeUnravelling.rel_length Rxy;
  | tail _ h ih => have := treeUnravelling.rel_length h; omega;

instance : (F.mkTransTreeUnravelling r).IsTransitive := inferInstance
instance : (F.mkTransTreeUnravelling r).IsAsymmetric := ⟨by grind⟩

lemma rel_def : X ≺ Y ↔ (∃ l ≠ [], Y.1 = X.1 ++ l ∧ (List.IsChain F.Rel (X.1 ++ l))) := treeUnravelling.transrel_def

abbrev pMorphism (F : Frame) [F.IsTransitive] (r : F) : (F.mkTransTreeUnravelling r) →ₚ F := (treeUnravelling.pMorphism F r).TransitiveClosure

protected abbrev root (F : Kripke.Frame) (r : F.World) : (F.mkTransTreeUnravelling r).World := treeUnravelling.root F r

instance : (F.mkTransTreeUnravelling r).IsRooted := by
  constructor;
  use mkTransTreeUnravelling.root F r;
  rintro ⟨_, ⟨l, rfl⟩, l_chain⟩ hn;
  apply rel_def.mpr;
  simp only [ne_eq, List.cons_append, List.nil_append, List.cons.injEq, true_and, existsAndEq];
  constructor;
  . by_contra hC;
    subst hC;
    simp at hn;
  . assumption;

instance instFinite [DecidableEq F.World] [F.IsFinite] [F.IsTransitive] [F.IsIrreflexive] : Finite (F.mkTransTreeUnravelling r).World := by
  suffices h : Finite { x // List.IsChain F.Rel x } by
    exact
     Finite.of_injective
     (β := { x // List.IsChain F.Rel x })
     (fun x => ⟨x.1, x.2.2⟩)
     (by rintro ⟨x, hx⟩ ⟨y, hy⟩; simp_all);
  apply List.chains_finite;

instance instIsTree : (F.mkTransTreeUnravelling r).IsTree where

instance instIsFiniteTree [DecidableEq F.World] [Finite F] [F.IsTransitive] [F.IsIrreflexive]
  : (F.mkTransTreeUnravelling r).IsFiniteTree where

end Frame.mkTransTreeUnravelling

/-
instance {F : Frame} [DecidableEq F.World] [Finite F] {r : F.World} (F_trans : Transitive F) (F_irrefl : Irreflexive F)
  : ((F↾r).mkTransTreeUnravelling Frame.pointGenerate.root).IsTree (Frame.mkTransTreeUnravelling.root) :=
    Frame.mkTransTreeUnravelling.instIsTree
    (Frame.pointGenerate.rel_trans F_trans)
    (Frame.pointGenerate.rel_irrefl F_irrefl)
-/

def Model.mkTreeUnravelling (M : Kripke.Model) (r : M.World) : Kripke.Model := ⟨M.toFrame.mkTreeUnravelling r, λ a c => M.Val a (c.1.getLast (by simp))⟩

def Model.mkTreeUnravelling.pMorphism (M : Kripke.Model) (r : M.World) : (M.mkTreeUnravelling r) →ₚ M :=
  PseudoEpimorphism.ofAtomic (Frame.treeUnravelling.pMorphism M.toFrame r) $ by rfl;

def Model.mkTransTreeUnravelling (M : Kripke.Model) (r : M.World) : Kripke.Model := ⟨M.toFrame.mkTransTreeUnravelling r, λ a c => M.Val a (c.1.getLast (by simp))⟩

namespace Model.mkTransTreeUnravelling

protected abbrev pMorphism (M : Kripke.Model) (r : M.World) [M.IsTransitive] : M.mkTransTreeUnravelling r →ₚ M :=
  PseudoEpimorphism.ofAtomic (Frame.mkTransTreeUnravelling.pMorphism M.toFrame r) $ by rfl;

protected abbrev root (M : Kripke.Model) (r : M.World) : (M.mkTransTreeUnravelling r).World := Frame.mkTransTreeUnravelling.root M.toFrame r

protected lemma modal_equivalence_at_root (M : Kripke.Model) (r : M.World) [M.IsTransitive]
  : ModalEquivalent (M₁ := M.mkTransTreeUnravelling r) (M₂ := M) (mkTransTreeUnravelling.root M r) r
  := Model.mkTransTreeUnravelling.pMorphism M r |>.modal_equivalence (mkTransTreeUnravelling.root M r)

end Model.mkTransTreeUnravelling

end Kripke

end LO.Modal
end
