import Mathlib.Data.Fintype.List
import Logic.Modal.Standard.Kripke.Preservation
import Logic.Modal.Standard.Kripke.GL.Completeness

-- TODO: Move to vorspiel or etc.
namespace List

variable {l l₁ l₂ : List α}
variable {R : α → α → Prop}

lemma Chain'.nodup_of_trans_irreflex (R_trans : Transitive R) (R_irrefl : Irreflexive R) (h_chain : l.Chain' R) : l.Nodup := by
  by_contra hC;
  replace ⟨d, hC⟩ := List.exists_duplicate_iff_not_nodup.mpr hC;
  have := List.duplicate_iff_sublist.mp hC;
  have := @List.Chain'.sublist α R [d, d] l ⟨by aesop⟩ h_chain this;
  simp at this;
  exact R_irrefl d this;

instance finiteNodupList [DecidableEq α] [Finite α] : Finite { l : List α // l.Nodup } := @fintypeNodupList α _ (Fintype.ofFinite α) |>.finite

lemma chains_finite [DecidableEq α] [Finite α] (R_trans : Transitive R) (R_irrefl : Irreflexive R) : Finite { l : List α // l.Chain' R } := by
  apply @Finite.of_injective { l : List α // l.Chain' R } { l : List α // l.Nodup } _ ?f;
  case f => intro ⟨l, hl⟩; refine ⟨l, List.Chain'.nodup_of_trans_irreflex R_trans R_irrefl hl⟩;
  simp [Function.Injective];

end List



namespace LO.Modal.Standard

namespace Kripke

-- open System
open Kripke
open Formula.Kripke

variable {α : Type u} [Inhabited α] [DecidableEq α]

open Relation (TransGen ReflTransGen)


section TreeUnravelling

def Frame.TreeUnravelling (F : Frame) (r : F.World) : Kripke.Frame where
  World := { c : List F.World | [r] <+: c ∧ c.Chain' F.Rel }
  World_nonempty := ⟨[r], (by simp)⟩
  Rel cx cy := ∃ z, cx.1 ++ [z] = cy.1

namespace Frame.TreeUnravelling

variable {F : Frame} {r : F.World}

@[simp]
lemma not_nil {c : (F.TreeUnravelling r).World} : c.1 ≠ [] := by
  have := c.2.1;
  by_contra;
  simp_all;

lemma rel_length {x y : (F.TreeUnravelling r).World} (h : x ≺ y) : x.1.length < y.1.length := by
  obtain ⟨z, hz⟩ := h;
  rw [←hz];
  simp;

lemma irreflexive : Irreflexive (F.TreeUnravelling r).Rel := by
  intro x; simp [TreeUnravelling];

lemma assymetric : Assymetric (F.TreeUnravelling r).Rel := by
  rintro x y hxy;
  by_contra hyx;
  replace hxy := rel_length hxy;
  replace hyx := rel_length hyx;
  exact hxy.not_lt hyx;

def PMorphism (F : Frame) (r : F) : F.TreeUnravelling r →ₚ F where
  toFun c := c.1.getLast (by simp)
  forth {cx cy} h := by
    obtain ⟨z, hz⟩ := h;
    have ⟨_, _, h⟩ := @List.chain'_append _ F.Rel cx.1 [z] |>.mp (by rw [hz]; exact cy.2.2);
    refine h (cx.1.getLast (by aesop)) ?hx (cy.1.getLast (by aesop)) ?hy;
    . exact List.getLast?_eq_getLast_of_ne_nil (by simp);
    . rw [←@List.getLast_append_singleton _ z cx.1]; simp_all;
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

end Frame.TreeUnravelling


def Model.TreeUnravelling (M : Kripke.Model α) (r : M.World) : Kripke.Model α where
  Frame := M.Frame.TreeUnravelling r
  Valuation c a := M.Valuation (c.1.getLast (by simp)) a

namespace Model.TreeUnravelling

variable {M : Kripke.Model α} {r : M.World} {p : Formula α}

def PMorphism (M : Kripke.Model α) (r : M.World) : M.TreeUnravelling r →ₚ M :=
  Model.PseudoEpimorphism.mkAtomic (Frame.TreeUnravelling.PMorphism M.Frame r) $ by aesop;

end Model.TreeUnravelling

end TreeUnravelling


section TransitiveTreeUnravelling

abbrev Frame.TransitiveTreeUnravelling (F : Frame) (r : F.World) := (F.TreeUnravelling r)^+

namespace Frame.TransitiveTreeUnravelling

variable {F : Frame} {r : F.World} {p : Formula α}

@[simp]
lemma not_nil {c : (F.TransitiveTreeUnravelling r).World} : c.1 ≠ [] := by
  by_contra;
  have := c.2.1;
  simp_all;

lemma rel_length {x y : (F.TransitiveTreeUnravelling r).World} (Rxy : x ≺ y) : x.1.length < y.1.length := by
  induction Rxy with
  | single Rxy => exact TreeUnravelling.rel_length Rxy;
  | tail _ h ih => have := TreeUnravelling.rel_length h; omega;

lemma rel_transitive : Transitive (F.TransitiveTreeUnravelling r) := TransitiveClosure.rel_transitive

lemma rel_asymmetric : Assymetric (F.TransitiveTreeUnravelling r).Rel := by
  rintro x y hxy;
  by_contra hyx;
  replace hxy := rel_length hxy;
  replace hyx := rel_length hyx;
  exact hxy.not_lt hyx;

lemma rel_def {x y : (F.TransitiveTreeUnravelling r).World} : x ≺ y ↔ (x.1.length < y.1.length ∧ x.1 <+: y.1) := by
  constructor;
  . intro Rxy;
    induction Rxy with
    | single Rxy =>
      obtain ⟨z, hz⟩ := Rxy;
      rw [←hz];
      constructor;
      . simp;
      . use [z];
    | tail _ h ih =>
      obtain ⟨w, hw⟩ := h;
      obtain ⟨_, ⟨zs, hzs⟩⟩ := ih;
      rw [←hw, ←hzs];
      constructor;
      . simp;
      . use zs ++ [w];
        simp [List.append_assoc];
  . replace ⟨xs, ⟨ws, hw⟩, hx₂⟩ := x;
    replace ⟨ys, ⟨vs, hv⟩, hy₂⟩ := y;
    subst hw hv;
    rintro ⟨hl, ⟨zs, hzs⟩⟩; simp at hzs;
    induction zs using List.induction_with_singleton generalizing ws vs with
    | hnil => simp_all;
    | hsingle z =>
      apply TransGen.single;
      use z;
      simp_all;
    | hcons z zs h ih =>
      simp_all;
      refine TransGen.head ?h₁ $ ih (ws ++ [z]) vs ?h₂ ?h₃ ?h₄ ?h₅;
      . use z; simp;
      . apply List.Chain'.prefix hy₂;
        use zs; simp_all;
      . exact hy₂;
      . rw [←hzs]; simp;
        by_contra hC;
        simp_all;
      . simp_all;

lemma rooted : (F.TransitiveTreeUnravelling r).isRooted ⟨[r], by tauto⟩ := by
  intro x ha;
  apply rel_def.mpr;
  obtain ⟨zs, hzs⟩ := x.2.1;
  constructor;
  . rw [←hzs];
    by_contra hC;
    simp at hC;
    simp_all;
  . use zs;

def PMorphism (F : Frame) (F_trans : Transitive F.Rel) (r : F) : (F.TransitiveTreeUnravelling r) →ₚ F := (Frame.TreeUnravelling.PMorphism F r).TransitiveClosure F_trans

end Frame.TransitiveTreeUnravelling


def Model.TransitiveTreeUnravelling (M : Kripke.Model α) (r : M.World) : Kripke.Model α where
  Frame := M.Frame.TransitiveTreeUnravelling r
  Valuation c a := M.Valuation (c.1.getLast (by simp)) a

namespace Model.TransitiveTreeUnravelling

def PMorphism (M : Kripke.Model α) (M_trans : Transitive M.Frame) (r : M.World) : M.TransitiveTreeUnravelling r →ₚ M :=
  Model.PseudoEpimorphism.mkAtomic (Frame.TransitiveTreeUnravelling.PMorphism M.Frame M_trans r) $ by aesop;

lemma modal_equivalence_to_root (M : Kripke.Model α) (M_trans : Transitive M.Frame) (r : M.World)
  : ModalEquivalent (M₁ := M.TransitiveTreeUnravelling r) (M₂ := M) ⟨[r], by simp⟩ r
  := modal_equivalence_of_modal_morphism (PMorphism M M_trans r) (⟨[r], by simp⟩)

end Model.TransitiveTreeUnravelling


end TransitiveTreeUnravelling


structure FiniteTransitiveTree extends Kripke.FiniteFrame, Kripke.RootedFrame where
  rel_assymetric : Assymetric Rel
  rel_transitive : Transitive Rel

set_option linter.unusedVariables false in
protected abbrev FiniteTransitiveTree.Dep (α : Type*) := FiniteTransitiveTree
protected abbrev FiniteTransitiveTree.alt (T : FiniteTransitiveTree) {α} : FiniteTransitiveTree.Dep α := T
postfix:max "#" => FiniteTransitiveTree.alt

namespace FiniteTransitiveTree

instance : Semantics (Formula α) (FiniteTransitiveTree.Dep α) := ⟨fun T ↦ Formula.Kripke.ValidOnFrame T.toFrame⟩

lemma rel_irreflexive (T : FiniteTransitiveTree) : Irreflexive T.Rel := irreflexive_of_assymetric $ T.rel_assymetric

end FiniteTransitiveTree

open Classical in
abbrev FiniteFrame.FiniteTransitiveTreeUnravelling
  (F : FiniteFrame) [DecidableEq F.World] (F_trans : Transitive F.toFrame) (F_irrefl : Irreflexive F.toFrame) (r : F.World) : FiniteTransitiveTree :=
  letI T := (F↾r).TransitiveTreeUnravelling ⟨r, by tauto⟩
  {
    World := T
    Rel := T.Rel
    rel_transitive := Frame.TransitiveTreeUnravelling.rel_transitive
    rel_assymetric := Frame.TransitiveTreeUnravelling.rel_asymmetric
    root_rooted := Frame.TransitiveTreeUnravelling.rooted
    World_finite := by
      have := F.World_finite;
      simp [Frame.TreeUnravelling];
      suffices h : Finite { x // List.Chain' (F.PointGenerated r).Rel x } by
        exact Finite.of_injective (β := { x // List.Chain' (F.PointGenerated r).Rel x })
          (fun x => ⟨x.1, x.2.2⟩) (by simp [Function.Injective]);
      exact List.chains_finite (Frame.PointGenerated.rel_transitive F_trans) (Frame.PointGenerated.rel_irreflexive F_irrefl)
  }

abbrev Model.FiniteTransitiveTreeUnravelling (M : Kripke.Model α) (r : M.World) : Kripke.Model α := (M↾r).TransitiveTreeUnravelling ⟨r, by tauto⟩


namespace Model.GLTreeUnravelling

end Model.GLTreeUnravelling


section

structure FiniteTransitiveTreeModel (α) where
  Tree : FiniteTransitiveTree
  Valuation : Valuation Tree.toFrame α

namespace FiniteTransitiveTreeModel

abbrev World (M : FiniteTransitiveTreeModel α) := M.Tree.World

abbrev root (M : FiniteTransitiveTreeModel α) : M.World := M.Tree.root

abbrev toFrame (M : FiniteTransitiveTreeModel α) : Kripke.Frame := M.Tree.toFrame

abbrev toModel (M : FiniteTransitiveTreeModel α) : Kripke.Model α := ⟨M.toFrame, M.Valuation⟩
instance : Coe (FiniteTransitiveTreeModel α) (Kripke.Model α) := ⟨toModel⟩

instance : CoeSort (FiniteTransitiveTreeModel α) (Type u) := ⟨World⟩

@[reducible]
instance {M : FiniteTransitiveTreeModel α} : Semantics (Formula α) (M.World) := Formula.Kripke.Satisfies.semantics (M := M.toModel)


end FiniteTransitiveTreeModel


section


/-
  TODO: `FiniteTransitiveTreeClass`のようなものを定義して適当に書き換える
-/

variable {p : Formula α}

open Classical

lemma valid_on_FiniteTransitiveTreeClass_of_valid_on_TransitiveIrreflexiveFrameClass (h : TransitiveIrreflexiveFrameClass.{v}ꟳ# ⊧ p) : ∀ T : FiniteTransitiveTree.{v}, T# ⊧ p := by
  simp at h;
  intro T;
  apply @h T.toFrame T.toFiniteFrame;
  . exact T.rel_transitive;
  . exact T.rel_irreflexive;
  . tauto;

lemma satisfies_at_root_on_FiniteTransitiveTree (h : ∀ F : FiniteTransitiveTree.{v}, F# ⊧ p) : ∀ M : FiniteTransitiveTreeModel.{u, v} α, Satisfies M.toModel M.root p := by
  intro M;
  exact h M.Tree M.Valuation M.root

lemma valid_on_TransitiveIrreflexiveFrameClass_of_satisfies_at_root_on_FiniteTransitiveTree : (∀ M : FiniteTransitiveTreeModel.{u, v} α, Satisfies M.toModel M.root p) → TransitiveIrreflexiveFrameClass.{v}ꟳ# ⊧ p := by
  rintro H _ ⟨F, ⟨F_trans, F_irrefl⟩, rfl⟩ V r;
  let M : Kripke.Model α := ⟨F, V⟩;
  apply Model.PointGenerated.modal_equivalent_to_root M F_trans r |>.mp;
  apply Model.TransitiveTreeUnravelling.modal_equivalence_to_root (M↾r) (Frame.PointGenerated.rel_transitive F_trans) ⟨r, by tauto⟩ |>.mp;
  exact H ⟨(F.FiniteTransitiveTreeUnravelling F_trans F_irrefl r), (M.FiniteTransitiveTreeUnravelling r).Valuation⟩;

/--
  _Segerberg [1971]_?
-/
theorem iff_provable_GL_satisfies_at_root_on_FiniteTransitiveTree : 𝐆𝐋 ⊢! p ↔ (∀ M : FiniteTransitiveTreeModel.{u, u} α, Satisfies M.toModel M.root p) := by
  constructor;
  . intro h M;
    have : TransitiveIrreflexiveFrameClassꟳ# ⊧ p := GL_sound.sound h;
    have := valid_on_FiniteTransitiveTreeClass_of_valid_on_TransitiveIrreflexiveFrameClass this;
    exact satisfies_at_root_on_FiniteTransitiveTree this M;
  . intro h;
    apply GL_complete.complete;
    intro F hF V;
    apply valid_on_TransitiveIrreflexiveFrameClass_of_satisfies_at_root_on_FiniteTransitiveTree h hF;

lemma iff_unprovable_GL_exists_unsatisfies_at_root_on_FiniteTransitiveTree : 𝐆𝐋 ⊬! p ↔ ∃ M : FiniteTransitiveTreeModel.{u, u} α, ¬Satisfies M.toModel M.root p := by
  constructor;
  . contrapose; simp;
    apply iff_provable_GL_satisfies_at_root_on_FiniteTransitiveTree.mpr;
  . contrapose; simp;
    apply iff_provable_GL_satisfies_at_root_on_FiniteTransitiveTree.mp;

end



def FiniteTransitiveTree.SimpleExtension (F : FiniteTransitiveTree) : Kripke.FiniteTransitiveTree where
  World := (Fin 1) ⊕ F.World
  Rel x y :=
    match x, y with
    | .inr x, .inr y => x ≺ y
    | .inl _, .inr _ => True
    | _ , _ => False
  root := .inl 0
  root_rooted := by
    intro w hw;
    simp at w;
    match w with
    | .inl ⟨r, hr⟩ => induction r <;> simp at hw hr;
    | .inr _ => simp [Frame.Rel'];
  rel_assymetric := by
    simp_all;
    intro x y hxy;
    match x, y with
    | .inl x, _ => simp;
    | .inr x, .inr y => exact F.rel_assymetric hxy;
  rel_transitive := by
    simp_all;
    intro x y z hxy hyz;
    match x, y, z with
    | .inl _, .inr _, .inr _ => simp;
    | .inr x, .inr y, .inr z => exact F.rel_transitive hxy hyz;
postfix:max "↧" => FiniteTransitiveTree.SimpleExtension

namespace FiniteTransitiveTree.SimpleExtension

variable {F : FiniteTransitiveTree} {x y : F.World}

instance : Coe (F.World) (F↧.World) := ⟨Sum.inr⟩

@[simp] lemma root_not_original : (Sum.inr x) ≠ F↧.root := by simp [SimpleExtension]

lemma root_eq {x : Fin 1} : (Sum.inl x) = F↧.root := by simp [SimpleExtension]; ext1; simp;

lemma forth (h : x ≺ y) : F↧.Rel x y := by simpa [SimpleExtension];

def p_morphism : F.toFrame →ₚ (F↧.toFrame) where
  toFun x := x
  forth := forth
  back {x y} h := by
    match y with
    | .inl r => simp [Frame.Rel', SimpleExtension] at h;
    | .inr y => use y; simp; exact h;

lemma through_original_root {x : F↧.World} (h : F↧.root ≺ x) : x = F.root ∨ (Sum.inr F.root ≺ x) := by
  match x with
  | .inl x =>
    simp [FiniteTransitiveTree.SimpleExtension.root_eq] at h;
    have := F↧.rel_irreflexive _ h;
    contradiction;
  | .inr x =>
    by_cases h : x = F.root;
    . subst h; left; tauto;
    . right; exact FiniteTransitiveTree.SimpleExtension.forth $ F.root_rooted x h;

end FiniteTransitiveTree.SimpleExtension

abbrev FiniteTransitiveTreeModel.SimpleExtension (M : FiniteTransitiveTreeModel α) : Kripke.FiniteTransitiveTreeModel α where
  Tree := M.Tree↧
  Valuation x a :=
    match x with
    | .inl _ => M.Valuation M.Tree.root a
    | .inr x => M.Valuation x a
postfix:max "↧" => FiniteTransitiveTreeModel.SimpleExtension


namespace FiniteTransitiveTreeModel.SimpleExtension

variable {M : FiniteTransitiveTreeModel α}

instance : Coe (M.World) (M↧.World) := ⟨Sum.inr⟩

def p_morphism : M →ₚ (M↧.toModel) := Model.PseudoEpimorphism.mkAtomic (FiniteTransitiveTree.SimpleExtension.p_morphism) $ by
  simp [FiniteTransitiveTree.SimpleExtension.p_morphism];

lemma modal_equivalence_original_world {x : M.toModel.World} : ModalEquivalent (M₁ := M) (M₂ := (M↧).toModel) x x := by
  apply Kripke.modal_equivalence_of_modal_morphism p_morphism;

end FiniteTransitiveTreeModel.SimpleExtension

-- def FiniteTransitiveTree.NthSimpleExplansion (T : FiniteTransitiveTree) (n : ℕ) : Kripke.FiniteTransitiveTree := (·⇓)^[n] T

end

end Kripke

section

open System
open Formula.Kripke (Satisfies)
open Kripke Kripke.FiniteTransitiveTreeModel

variable [DecidableEq α] [Inhabited α]
variable {p q : Formula α}

/-
  逆は以下を順に辿って構文論的に証明できる．
  - `System.imply_boxdot_boxdot_of_imply_boxdot_plain`
  - `System.imply_boxdot_axiomT_of_imply_boxdot_boxdot`
  - `System.imply_box_box_of_imply_boxdot_axiomT`
-/
lemma GL_imply_boxdot_plain_of_imply_box_box : 𝐆𝐋 ⊢! □p ⟶ □q → 𝐆𝐋 ⊢! ⊡p ⟶ q := by
  contrapose;
  intro h;
  have := iff_unprovable_GL_exists_unsatisfies_at_root_on_FiniteTransitiveTree.mp h;
  obtain ⟨M, hs⟩ := this;
  have hs : M.root ⊧ ⊡p ⋏ ~q := by simp_all [Satisfies, Semantics.Realize];
  replace hs := @FiniteTransitiveTreeModel.SimpleExtension.modal_equivalence_original_world α M M.root (⊡p ⋏ ~q) |>.mp hs;

  simp [Satisfies, Semantics.Realize] at hs;
  have ⟨hs₁, hs₂, hs₃⟩ := hs;

  have hbp : (Satisfies M↧.toModel (M↧.root) (□p)) := by
    intro x hx;
    rcases @FiniteTransitiveTree.SimpleExtension.through_original_root M.Tree x hx with (rfl | b)
    . assumption;
    . exact hs₂ _ b;
  have hbq : ¬(Satisfies M↧.toModel (M↧.root) (□q)) := by
    simp [Satisfies];
    use M.root;
    constructor;
    . apply M↧.Tree.toRootedFrame.root_rooted M.root;
      simp [SimpleExtension, FiniteTransitiveTree.SimpleExtension]; -- TODO: extract lemma
    . assumption;
  have : ¬(Satisfies M↧.toModel M↧.root (□p ⟶ □q)) := _root_.not_imp.mpr ⟨hbp, hbq⟩;

  apply iff_unprovable_GL_exists_unsatisfies_at_root_on_FiniteTransitiveTree.mpr;
  use M↧;

theorem GL_unnecessitation! : 𝐆𝐋 ⊢! □p → 𝐆𝐋 ⊢! p := by
  intro h;
  have : 𝐆𝐋 ⊢! □⊤ ⟶ □p := dhyp! (q := □⊤) h;
  have : 𝐆𝐋 ⊢! ⊡⊤ ⟶ p := GL_imply_boxdot_plain_of_imply_box_box this;
  exact this ⨀ boxdotverum!;

noncomputable instance : System.Unnecessitation (𝐆𝐋 : DeductionParameter α) where
  unnec := λ h => GL_unnecessitation! ⟨h⟩ |>.some

end

end LO.Modal.Standard
