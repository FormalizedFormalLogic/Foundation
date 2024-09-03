import Logic.Logic.Kripke.Tree
import Logic.Modal.Kripke.Preservation
import Logic.Modal.Kripke.GL.Completeness

namespace LO.Modal

namespace Kripke

open LO.Kripke
open Kripke
open Formula.Kripke

lemma modal_equivalence_at_root_on_treeUnravelling (M : Kripke.Model α) (M_trans : Transitive M.Frame) (r : M.World)
  : ModalEquivalent (M₁ := M.TransitiveTreeUnravelling r) (M₂ := M) ⟨[r], by simp⟩ r
  := modal_equivalence_of_modal_morphism (Model.TransitiveTreeUnravelling.pMorphism M M_trans r) (⟨[r], by simp⟩)

@[reducible] instance : Semantics (Formula α) (FiniteTransitiveTree.Dep α) := ⟨fun T ↦ Formula.Kripke.ValidOnFrame T.toFrame⟩

@[reducible] instance {M : FiniteTransitiveTreeModel α} : Semantics (Formula α) (M.World) := Formula.Kripke.Satisfies.semantics (M := M.toModel)


section

variable [Inhabited α] [DecidableEq α]
variable {p : Formula α}

open Classical

lemma valid_on_FiniteTransitiveTreeClass_of_valid_on_TransitiveIrreflexiveFrameClass (h : TransitiveIrreflexiveFrameClass.{v}ꟳ#α ⊧ p) : ∀ T : FiniteTransitiveTree.{v}, T# ⊧ p := by
  simp at h;
  intro T;
  apply @h T.toFrame T.toFiniteFrame;
  . exact T.rel_transitive;
  . exact T.rel_irreflexive;
  . tauto;

lemma satisfies_at_root_on_FiniteTransitiveTree (h : ∀ F : FiniteTransitiveTree.{v}, F# ⊧ p) : ∀ M : FiniteTransitiveTreeModel.{u, v} α, Satisfies M.toModel M.root p := by
  intro M;
  exact h M.Tree M.Valuation M.root

lemma valid_on_TransitiveIrreflexiveFrameClass_of_satisfies_at_root_on_FiniteTransitiveTree
  : (∀ M : FiniteTransitiveTreeModel.{u, v} α, M.root ⊧ p) → TransitiveIrreflexiveFrameClass.{v}ꟳ#α ⊧ p := by
  rintro H _ ⟨F, ⟨F_trans, F_irrefl⟩, rfl⟩ V r;
  let M : Kripke.Model α := ⟨F, V⟩;
  apply modal_equivalent_at_root_on_generated_model M F_trans r |>.mp;
  apply modal_equivalence_at_root_on_treeUnravelling (M↾r) (Frame.PointGenerated.rel_transitive F_trans) ⟨r, by tauto⟩ |>.mp;
  exact H ⟨(F.FiniteTransitiveTreeUnravelling F_trans F_irrefl r), (M.FiniteTransitiveTreeUnravelling r).Valuation⟩;

theorem iff_provable_GL_satisfies_at_root_on_FiniteTransitiveTree : 𝐆𝐋 ⊢! p ↔ (∀ M : FiniteTransitiveTreeModel.{u, u} α, M.root ⊧ p) := by
  constructor;
  . intro h M;
    have : TransitiveIrreflexiveFrameClassꟳ#α ⊧ p := GL_finite_sound.sound h;
    have := valid_on_FiniteTransitiveTreeClass_of_valid_on_TransitiveIrreflexiveFrameClass this;
    exact satisfies_at_root_on_FiniteTransitiveTree this M;
  . intro h;
    apply GL_complete.complete;
    intro F hF V;
    apply valid_on_TransitiveIrreflexiveFrameClass_of_satisfies_at_root_on_FiniteTransitiveTree h hF;

lemma iff_unprovable_GL_exists_unsatisfies_at_root_on_FiniteTransitiveTree : 𝐆𝐋 ⊬! p ↔ ∃ M : FiniteTransitiveTreeModel.{u, u} α, ¬M.root ⊧ p := by
  constructor;
  . contrapose; simp; apply iff_provable_GL_satisfies_at_root_on_FiniteTransitiveTree.mpr;
  . contrapose; simp; apply iff_provable_GL_satisfies_at_root_on_FiniteTransitiveTree.mp;

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

  apply iff_unprovable_GL_exists_unsatisfies_at_root_on_FiniteTransitiveTree.mpr;
  use M↧;
  exact _root_.not_imp.mpr ⟨hbp, hbq⟩;

theorem GL_unnecessitation! : 𝐆𝐋 ⊢! □p → 𝐆𝐋 ⊢! p := by
  intro h;
  have : 𝐆𝐋 ⊢! □⊤ ⟶ □p := dhyp! (q := □⊤) h;
  have : 𝐆𝐋 ⊢! ⊡⊤ ⟶ p := GL_imply_boxdot_plain_of_imply_box_box this;
  exact this ⨀ boxdotverum!;

noncomputable instance : System.Unnecessitation (𝐆𝐋 : DeductionParameter α) where
  unnec := λ h => GL_unnecessitation! ⟨h⟩ |>.some

end

end LO.Modal
