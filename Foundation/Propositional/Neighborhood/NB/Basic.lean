module
import Foundation.Propositional.Logic.Basic
import Foundation.Propositional.Entailment.Corsi.Basic
import Foundation.Vorspiel.Rel.Basic

namespace LO.Propositional

variable {φ ψ χ : Formula ℕ}

namespace NBNeighborhood

structure Frame where
  World : Type
  𝓧 : Set World
  NB : World → Set (𝒫 𝓧 × 𝒫 𝓧)
  NB_spec : ∀ {w X Y}, X.1 ⊆ Y.1 → (X, Y) ∈ NB w
  𝓧_closed_inter : ∀ {X₁ X₂ : 𝒫 𝓧}, X₁.1 ∩ X₂.1 ⊆ 𝓧
  𝓧_closed_union : ∀ {X₁ X₂ : 𝒫 𝓧}, X₁.1 ∪ X₂.1 ⊆ 𝓧
  𝓧_closed_imp   : ∀ {X₁ X₂}, { w | (X₁, X₂) ∈ NB w } ⊆ 𝓧
  r : World
  r_rooted : NB r = { (X, Y) | X.1 ⊆ Y.1 }

namespace Frame

attribute [simp] 𝓧_closed_inter 𝓧_closed_union 𝓧_closed_imp r_rooted
attribute [grind .] r_rooted
attribute [grind <=] NB_spec

variable {F : Frame}

instance : CoeSort Frame (Type) := ⟨World⟩
instance : Nonempty F.World := ⟨F.r⟩

lemma NB_spec_not : (X, Y) ∉ F.NB w → ¬(X.1 ⊆ Y.1)  := by
  contrapose!;
  apply F.NB_spec;

end Frame

abbrev FrameClass := Set Frame



abbrev Valuation (F : Frame) := ℕ → 𝒫 F.𝓧


structure Model extends Frame where
  Val : Valuation toFrame

namespace Model

variable {M : Model} {φ ψ χ : Formula ℕ}

instance : CoeSort (Model) (Type) := ⟨λ M => M.World⟩
instance : CoeFun (Model) (λ M => ℕ → 𝒫 M.𝓧) := ⟨fun m => m.Val⟩

instance : EmptyCollection (𝒫 M.𝓧) := ⟨⟨∅, by tauto⟩⟩

def truthset (M : Model) : Formula ℕ → 𝒫 M.𝓧
  | .atom a => M.Val a
  | ⊥      => ⟨∅, by tauto⟩
  | φ ⋏ ψ  => ⟨truthset M φ ∩ truthset M ψ, M.𝓧_closed_inter⟩
  | φ ⋎ ψ  => ⟨truthset M φ ∪ truthset M ψ, M.𝓧_closed_union⟩
  | φ ➝ ψ  => ⟨{ w | (truthset M φ, truthset M ψ) ∈ M.NB w }, M.𝓧_closed_imp⟩
instance : CoeFun (Model) (λ M => Formula ℕ → 𝒫 M.𝓧) := ⟨truthset⟩

@[simp, grind =] lemma truthset_atom {a : ℕ} : M (.atom a) = M.Val a := rfl
@[simp, grind =] lemma truthset_bot : M ⊥ = ⟨∅, by tauto⟩ := rfl
@[simp, grind =] lemma truthset_and : M (φ ⋏ ψ) = ⟨M φ ∩ M ψ, M.𝓧_closed_inter⟩ := rfl
@[simp, grind =] lemma truthset_or : M (φ ⋎ ψ) = ⟨M φ ∪ M ψ, M.𝓧_closed_union⟩ := rfl
@[simp, grind =] lemma truthset_imp : M (φ ➝ ψ) = ⟨{ w | (M φ, M ψ) ∈ M.NB w }, M.𝓧_closed_imp⟩ := rfl
@[simp, grind .] lemma truthset_top : (M ⊤).1 = Set.univ := by simp [truthset, M.NB_spec];
@[simp, grind =] lemma truthset_neg : M (∼φ) = ⟨{ w | (M φ, ∅) ∈ M.NB w }, M.𝓧_closed_imp⟩ := by grind;
@[simp, grind =] lemma truthset_iff : M (φ ⭤ ψ) = ⟨{ w | (M φ, M ψ) ∈ M.NB w ∧ (M ψ, M φ) ∈ M.NB w }, @M.𝓧_closed_inter (M (φ ➝ ψ)) (M (ψ ➝ φ))⟩ := by grind;

end Model

abbrev ModelClass := Set Model


end NBNeighborhood



namespace Formula.NBNeighborhood

open NBNeighborhood

open Classical in
@[simp, grind .] abbrev Forces {M : outParam (NBNeighborhood.Model)} (x : M.World) (φ : Formula ℕ) : Prop := x ∈ (M φ).1
infix:45 " ⊩ " => Forces

@[simp, grind .] abbrev NotForces {M : outParam (NBNeighborhood.Model)} (x : M.World) (φ : Formula ℕ) : Prop := ¬(x ⊩ φ)
infix:45 " ⊮ " => NotForces

namespace Forces

variable {M : NBNeighborhood.Model} {x y : M.World} {a : ℕ} {φ ψ χ : Formula ℕ}

@[grind =] protected lemma def_atom : x ⊩ (atom a) ↔ x ∈ (M.Val a).1 := by rfl
@[simp, grind .] protected lemma def_bot : x ⊮ ⊥ := by simp;
@[simp, grind .] protected lemma def_top : x ⊩ ⊤ := by simp;

@[grind =] protected lemma def_and : x ⊩ φ ⋏ ψ ↔ x ⊩ φ ∧ x ⊩ ψ := by simp;
@[grind =] protected lemma not_def_and : x ⊮ φ ⋏ ψ ↔ x ⊮ φ ∨ x ⊮ ψ := by grind;

@[grind =] protected lemma def_or  : x ⊩ φ ⋎ ψ ↔ x ⊩ φ ∨ x ⊩ ψ := by simp;
@[grind =] protected lemma not_def_or : x ⊮ φ ⋎ ψ ↔ x ⊮ φ ∧ x ⊮ ψ := by grind;

@[grind =] protected lemma def_imp  : x ⊩ φ ➝ ψ ↔ (M φ, M ψ) ∈ M.NB x := by simp;
@[grind =] protected lemma not_def_imp : x ⊮ φ ➝ ψ ↔ (M φ, M ψ) ∉ M.NB x := by simp;

@[grind =] protected lemma def_neg  : x ⊩ ∼φ ↔ (M φ, ∅) ∈ M.NB x := by simp;
@[grind =] protected lemma not_def_neg : x ⊮ ∼φ ↔ (M φ, ∅) ∉ M.NB x := by simp;

@[grind =] protected lemma def_iff : x ⊩ φ ⭤ ψ ↔ ((M φ, M ψ) ∈ M.NB x ∧ (M ψ, M φ) ∈ M.NB x) := by
  apply Iff.trans Forces.def_and
  grind;
@[grind =] protected lemma not_def_iff : x ⊮ φ ⭤ ψ ↔ ((M φ, M ψ) ∉ M.NB x ∨ (M ψ, M φ) ∉ M.NB x) := by grind

end Forces


instance : Semantics (NBNeighborhood.Model) (Formula ℕ) := ⟨fun M φ => ∀ x : M.World, x ⊩ φ⟩

namespace ValidOnModel

variable {M : NBNeighborhood.Model}

@[simp, grind =] lemma iff_models : M ⊧ φ ↔ ∀ x : M.World, x ⊩ φ := iff_of_eq rfl
@[simp, grind =] lemma iff_not_models : M ⊭ φ ↔ ∃ x : M.World, x ⊮ φ := by simp [Semantics.NotModels, Semantics.Models];

@[simp, grind .] protected lemma def_verum : M ⊧ ⊤ := by simp;
instance : Semantics.Top (NBNeighborhood.Model) := ⟨by simp⟩

@[simp, grind .] protected lemma def_bot : M ⊭ ⊥ := by simp;
instance : Semantics.Bot (NBNeighborhood.Model) := ⟨by simp⟩

@[grind =>] lemma forces_at_root (h : M ⊧ φ) : M.r ⊩ φ := h M.r
@[grind =>] lemma subset_truthset_of_valid (h : M ⊧ φ ➝ ψ) : (M φ).1 ⊆ (M ψ).1 := by grind;

lemma valid_andElim₁ : M ⊧ Axioms.AndElim₁ φ ψ := by grind;
lemma valid_andElim₂ : M ⊧ Axioms.AndElim₂ φ ψ := by grind;
lemma valid_orIntro₁ : M ⊧ Axioms.OrInst₁ φ ψ := by grind;
lemma valid_orIntro₂ : M ⊧ Axioms.OrInst₂ φ ψ := by grind;
lemma valid_distributeAndOr : M ⊧ Axioms.DistributeAndOr φ ψ χ := by grind
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

@[grind =>] lemma valid_andElimL (h : M ⊧ φ ⋏ ψ) : M ⊧ φ := by grind;
@[grind =>] lemma valid_andElimR (h : M ⊧ φ ⋏ ψ) : M ⊧ ψ := by grind;

@[grind =>]
lemma eq_truthset_of_valid (h : M ⊧ φ ⭤ ψ) : (M φ).1 = (M ψ).1 := by
  apply Set.Subset.antisymm;
  . apply subset_truthset_of_valid;
    apply valid_andElimL h;
  . apply subset_truthset_of_valid;
    apply valid_andElimR h;

@[grind <=]
lemma valid_RuleE (h₁ : M ⊧ φ ⭤ ψ) (h₂ : M ⊧ χ ⭤ ξ) : M ⊧ (φ ➝ χ) ⭤ (ψ ➝ ξ) := by
  replace h₁ := eq_truthset_of_valid h₁;
  replace h₂ := eq_truthset_of_valid h₂;
  grind;


end ValidOnModel


instance : Semantics (NBNeighborhood.Frame) (Formula ℕ) := ⟨fun F φ => ∀ V, (⟨F, V⟩ : NBNeighborhood.Model) ⊧ φ⟩

namespace ValidOnFrame

variable {F : NBNeighborhood.Frame}

@[simp, grind .] lemma iff_models : F ⊧ φ ↔ ∀ V, (⟨F, V⟩ : NBNeighborhood.Model) ⊧ φ := by rfl
@[simp, grind .] lemma iff_not_models : F ⊭ φ ↔ ∃ V, (⟨F, V⟩ : NBNeighborhood.Model) ⊭ φ := by simp [Semantics.NotModels, Semantics.Models];

@[simp, grind .] protected lemma def_verum : F ⊧ ⊤ := by simp;
instance : Semantics.Top (NBNeighborhood.Frame) := ⟨by grind⟩

@[simp, grind .] protected lemma def_bot : F ⊭ ⊥ := by
  suffices ∃ X, X ⊆ F.𝓧 by simpa;
  use ∅;
  tauto;
instance : Semantics.Bot (NBNeighborhood.Frame) := ⟨by grind⟩

end ValidOnFrame

end Formula.NBNeighborhood


namespace NBNeighborhood


open Formula.NBNeighborhood


section

variable {FC : FrameClass} {φ ψ χ : Formula ℕ}

lemma iff_not_validOnFrameClass_exists_frame : FC ⊭ φ ↔ ∃ F ∈ FC, ¬F ⊧ φ := by
  apply not_iff_not.mp;
  push_neg;
  tauto;
alias ⟨exists_frame_of_not_validOnFrameClass, not_validOnFrameClass_of_exists_frame⟩ := iff_not_validOnFrameClass_exists_frame

lemma iff_not_validOnFrameClass_exists_model : FC ⊭ φ ↔ ∃ M : NBNeighborhood.Model, M.toFrame ∈ FC ∧ M ⊭ φ := by
  apply not_iff_not.mp;
  push_neg;
  tauto;
alias ⟨exists_model_of_not_validOnFrameClass, not_validOnFrameClass_of_exists_model⟩ := iff_not_validOnFrameClass_exists_model

lemma iff_not_validOnFrameClass_exists_model_world : FC ⊭ φ ↔ ∃ M : NBNeighborhood.Model, ∃ x : M, M.toFrame ∈ FC ∧ x ⊮ φ := by
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

lemma iff_not_validOnModelClass_exists_model_world : MC ⊭ φ ↔ ∃ M : NBNeighborhood.Model, ∃ x : M, M ∈ MC ∧ x ⊮ φ := by
  apply not_iff_not.mp;
  push_neg;
  tauto;
alias ⟨exists_model_world_of_not_validOnModelClass, not_validOnModelClass_of_exists_model_world⟩ := iff_not_validOnModelClass_exists_model_world

end

end NBNeighborhood

end LO.Propositional
