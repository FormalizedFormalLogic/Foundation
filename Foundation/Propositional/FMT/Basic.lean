import Foundation.Propositional.Logic.Basic
import Foundation.Propositional.Entailment.Corsi.Basic
import Foundation.Vorspiel.HRel.Basic

namespace LO.Propositional

variable {φ ψ χ : Formula ℕ}

namespace FMT

structure Frame where
  World : Type
  Rel : Formula ℕ → HRel World
  root : World
  rooted {φ : Formula ℕ} {w : World} : Rel φ root w

namespace Frame

variable {F : Frame}

attribute [simp, grind .] rooted

instance : CoeSort Frame (Type) := ⟨World⟩
instance : CoeFun Frame (λ F => Formula ℕ → HRel F.World) := ⟨Frame.Rel⟩
instance : Nonempty F.World := ⟨F.root⟩

abbrev Rel' {F : Frame} (φ : Formula ℕ) (x y : F.World) := F.Rel φ x y
notation:45 x:90 " ≺[" φ "] " y:90 => Frame.Rel' φ x y
notation:45 x:max " ≺[" φ "] " y:max " on " F:max => Frame.Rel F φ x y

end Frame

abbrev FrameClass := Set Frame



abbrev Valuation (F : Frame) := F.World → ℕ → Prop


structure Model extends Frame where
  Val : Valuation toFrame

namespace Model

instance : CoeSort (Model) (Type) := ⟨λ M => M.World⟩
instance : CoeFun (Model) (λ M => M.World → ℕ → Prop) := ⟨fun m => m.Val⟩

end Model

abbrev ModelClass := Set Model

end FMT



namespace Formula.FMT

open FMT

@[simp, grind .]
def Forces {M : outParam (FMT.Model)} (x : M.World) : Formula ℕ → Prop
  | atom a => M x a
  | ⊥      => False
  | φ ⋏ ψ  => Forces x φ ∧ Forces x ψ
  | φ ⋎ ψ  => Forces x φ ∨ Forces x ψ
  | φ ➝ ψ => ∀ {y}, x ≺[φ ➝ ψ] y → (Forces y φ → Forces y ψ)
infix:45 " ⊩ " => Forces

@[simp, grind .] abbrev NotForces {M : outParam (FMT.Model)} (x : M.World) (φ : Formula ℕ) : Prop := ¬(x ⊩ φ)
infix:45 " ⊮ " => NotForces

namespace Forces

variable {M : FMT.Model} {x y : M.World} {a : ℕ} {φ ψ χ : Formula ℕ}

@[grind =] protected lemma def_atom : x ⊩ (atom a) ↔ M x a := by rfl
@[simp, grind .] protected lemma def_bot : x ⊮ ⊥ := by simp;
@[simp, grind .] protected lemma def_top : x ⊩ ⊤ := by simp;

@[grind =] protected lemma def_and : x ⊩ φ ⋏ ψ ↔ x ⊩ φ ∧ x ⊩ ψ := by simp;
@[grind =] protected lemma not_def_and : x ⊮ φ ⋏ ψ ↔ x ⊮ φ ∨ x ⊮ ψ := by grind;

@[grind =] protected lemma def_or  : x ⊩ φ ⋎ ψ ↔ x ⊩ φ ∨ x ⊩ ψ := by simp;
@[grind =] protected lemma not_def_or : x ⊮ φ ⋎ ψ ↔ x ⊮ φ ∧ x ⊮ ψ := by grind;

@[grind =] protected lemma def_imp  : x ⊩ φ ➝ ψ ↔ ∀ {y}, x ≺[φ ➝ ψ] y → (y ⊩ φ → y ⊩ ψ) := by simp;
@[grind =] protected lemma not_def_imp : x ⊮ φ ➝ ψ ↔ ∃ y, x ≺[φ ➝ ψ] y ∧ (y ⊩ φ ∧ y ⊮ ψ) := by grind;

@[grind =] protected lemma def_neg  : x ⊩ ∼φ ↔ ∀ {y}, x ≺[∼φ] y → y ⊮ φ := by
  apply Iff.trans Forces.def_imp;
  tauto;
@[grind =] protected lemma not_def_neg : x ⊮ ∼φ ↔ ∃ y, x ≺[∼φ] y ∧ y ⊩ φ := by grind;

@[grind =] protected lemma def_iff : x ⊩ φ ⭤ ψ ↔ ((∀ {y}, x ≺[φ ➝ ψ] y → y ⊩ φ → y ⊩ ψ) ∧ (∀ {y}, x ≺[ψ ➝ φ] y → y ⊩ ψ → y ⊩ φ)) := by
  apply Iff.trans Forces.def_and;
  grind;
@[grind =] protected lemma not_def_iff : x ⊮ φ ⭤ ψ ↔ (∃ y, x ≺[φ ➝ ψ] y ∧ (y ⊩ φ ∧ y ⊮ ψ)) ∨ (∃ y, x ≺[ψ ➝ φ] y ∧ (y ⊩ ψ ∧ y ⊮ φ)) := by grind;

end Forces


instance : Semantics (FMT.Model) (Formula ℕ) := ⟨fun M φ => ∀ x : M.World, x ⊩ φ⟩

namespace ValidOnModel

variable {M : FMT.Model}

@[simp, grind =] lemma iff_models : M ⊧ φ ↔ ∀ x : M.World, x ⊩ φ := iff_of_eq rfl
@[simp, grind =] lemma iff_not_models : M ⊭ φ ↔ ∃ x : M.World, x ⊮ φ := by simp [Semantics.NotModels, Semantics.Models];

@[simp, grind .] protected lemma def_verum : M ⊧ ⊤ := by simp;
instance : Semantics.Top (FMT.Model) := ⟨by simp⟩

@[simp, grind .] protected lemma def_bot : M ⊭ ⊥ := by simp;
instance : Semantics.Bot (FMT.Model) := ⟨by simp⟩

@[grind =>] lemma forces_at_root (h : M ⊧ φ) : M.root ⊩ φ := h M.root

lemma valid_andElim₁ : M ⊧ Axioms.AndElim₁ φ ψ := by grind;
lemma valid_andElim₂ : M ⊧ Axioms.AndElim₂ φ ψ := by grind;
lemma valid_orIntro₁ : M ⊧ Axioms.OrInst₁ φ ψ := by grind;
lemma valid_orIntro₂ : M ⊧ Axioms.OrInst₂ φ ψ := by grind;
lemma valid_distributeAndOr : M ⊧ Axioms.DistributeAndOr φ ψ χ := by grind
lemma valid_collectOrAnd : M ⊧ Axioms.CollectOrAnd φ ψ χ := by grind
lemma valid_impId : M ⊧ Axioms.ImpId φ := by grind
lemma valid_efq : M ⊧ Axioms.EFQ φ := by grind

attribute [simp high, grind .]
  valid_andElim₁ valid_andElim₂
  valid_orIntro₁ valid_orIntro₂
  valid_distributeAndOr
  valid_impId
  valid_efq

@[grind =>] lemma valid_mdp (h₁ : M ⊧ φ ➝ ψ) (h₂ : M ⊧ φ) : M ⊧ ψ := by grind;
lemma valid_AF (h : M ⊧ φ) : M ⊧ ψ ➝ φ := by grind;
lemma valid_AR (h₁ : M ⊧ φ) (h₂ : M ⊧ ψ) : M ⊧ φ ⋏ ψ := by grind;
lemma valid_RuleD (h₁ : M ⊧ φ ➝ χ) (h₂ : M ⊧ ψ ➝ χ) : M ⊧ φ ⋎ ψ ➝ χ := by grind;
lemma valid_RuleC (h₁ : M ⊧ φ ➝ ψ) (h₂ : M ⊧ φ ➝ χ) : M ⊧ φ ➝ (ψ ⋏ χ) := by grind;
lemma valid_RuleI (h₁ : M ⊧ φ ➝ ψ) (h₂ : M ⊧ ψ ➝ χ) : M ⊧ φ ➝ χ := by grind;

attribute [grind <=]
  valid_AF
  valid_AR
  valid_RuleD
  valid_RuleC
  valid_RuleI

/-
lemma invalid_RuleE :
  letI M : FMT.Model := {
    World := Fin 2,
    Rel φ x y :=
      match φ with
      | #0 ➝ #1 => True
      | #2 ➝ #3 => True
      | _ => True,
    root := 0,
    rooted {φ} := by
      match φ with
      | #0 ➝ #1 => tauto;
      | #2 ➝ #3 => tauto;
      | _ => sorry,
    Val := fun x a => match x with
      | 0 => true
      | 1 => a = 0
  };
  M ⊧ #0 ⭤ #1 → M ⊧ #2 ⭤ #3 → M ⊭ (#0 ➝ #2) ⭤ (#1 ➝ #3) := by
  intro H₁ H₂;
  apply iff_not_models.mpr;
  sorry;
-/

lemma iff_not_exists_world : M ⊭ φ ↔ ∃ x : M.World, x ⊮ φ := by
  apply not_iff_not.mp;
  push_neg;
  tauto;
alias ⟨exists_world_of_not, not_of_exists_world⟩ := iff_not_exists_world

end ValidOnModel


instance : Semantics (FMT.Frame) (Formula ℕ) := ⟨fun F φ => ∀ V, (⟨F, V⟩ : FMT.Model) ⊧ φ⟩

namespace ValidOnFrame

variable {F : FMT.Frame}

@[simp, grind .] lemma iff_models : F ⊧ φ ↔ ∀ V, (⟨F, V⟩ : FMT.Model) ⊧ φ := by rfl
@[simp, grind .] lemma iff_not_models : F ⊭ φ ↔ ∃ V, (⟨F, V⟩ : FMT.Model) ⊭ φ := by simp [Semantics.NotModels, Semantics.Models];

@[simp, grind .] protected lemma def_verum : F ⊧ ⊤ := by simp;
instance : Semantics.Top (FMT.Frame) := ⟨by grind⟩

@[simp, grind .] protected lemma def_bot : F ⊭ ⊥ := by simp;
instance : Semantics.Bot (FMT.Frame) := ⟨by grind⟩

end ValidOnFrame

end Formula.FMT


namespace FMT


open Formula.FMT


section

variable {FC : FrameClass} {φ ψ χ : Formula ℕ}

lemma iff_not_validOnFrameClass_exists_frame : FC ⊭ φ ↔ ∃ F ∈ FC, ¬F ⊧ φ := by
  apply not_iff_not.mp;
  push_neg;
  tauto;
alias ⟨exists_frame_of_not_validOnFrameClass, not_validOnFrameClass_of_exists_frame⟩ := iff_not_validOnFrameClass_exists_frame

lemma iff_not_validOnFrameClass_exists_model : FC ⊭ φ ↔ ∃ M : FMT.Model, M.toFrame ∈ FC ∧ M ⊭ φ := by
  apply not_iff_not.mp;
  push_neg;
  tauto;
alias ⟨exists_model_of_not_validOnFrameClass, not_validOnFrameClass_of_exists_model⟩ := iff_not_validOnFrameClass_exists_model

lemma iff_not_validOnFrameClass_exists_model_world : FC ⊭ φ ↔ ∃ M : FMT.Model, ∃ x : M, M.toFrame ∈ FC ∧ x ⊮ φ := by
  apply not_iff_not.mp;
  push_neg;
  tauto;
alias ⟨exists_model_world_of_not_validOnFrameClass, not_validOnFrameClass_of_exists_model_world⟩ := iff_not_validOnFrameClass_exists_model_world

end


section

variable {MC : ModelClass} {φ ψ χ : Formula ℕ}

lemma iff_not_validOnModelClass_exists_model : MC ⊭ φ ↔ ∃ M ∈ MC, ¬M ⊧ φ := by
  apply not_iff_not.mp;
  push_neg;
  tauto;
alias ⟨exists_model_of_not_validOnModelClass, not_validOnModelClass_of_exists_model⟩ := iff_not_validOnModelClass_exists_model

lemma iff_not_validOnModelClass_exists_model_world : MC ⊭ φ ↔ ∃ M : FMT.Model, ∃ x : M, M ∈ MC ∧ x ⊮ φ := by
  apply not_iff_not.mp;
  push_neg;
  tauto;
alias ⟨exists_model_world_of_not_validOnModelClass, not_validOnModelClass_of_exists_model_world⟩ := iff_not_validOnModelClass_exists_model_world

end

end FMT

end LO.Propositional
