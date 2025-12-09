import Foundation.Modal.Formula

namespace LO.Modal

open Formula (atom)
variable {φ ψ χ : Formula ℕ}

namespace PLoN

structure Frame where
  World : Type
  Rel : Formula ℕ → World → World → Prop
  [World_nonempty : Nonempty World]

namespace Frame

variable {F : PLoN.Frame}

noncomputable abbrev default {F : PLoN.Frame} : F.World := F.World_nonempty.some

instance : CoeSort PLoN.Frame (Type) := ⟨World⟩
instance : CoeFun PLoN.Frame (λ F => Formula ℕ → F.World → F.World → Prop) := ⟨Frame.Rel⟩
instance : Nonempty F.World := F.World_nonempty

abbrev Rel' {F : PLoN.Frame} (φ : Formula ℕ) (x y : F.World) := F.Rel φ x y
notation:45 x:90 " ≺[" φ "] " y:90 => Rel' φ x y

end Frame



abbrev terminalFrame : PLoN.Frame where
  World := Unit
  Rel := λ _ _ _ => True



abbrev FrameClass := Set (PLoN.Frame)

abbrev Valuation (F : PLoN.Frame) := F.World → ℕ → Prop

structure Model extends PLoN.Frame where
  Valuation : PLoN.Valuation toFrame

end PLoN



open PLoN

namespace Formula.PLoN

@[simp, grind .]
def Forces {M : PLoN.Model} (w : M.World) : Formula ℕ → Prop
  | atom a  => M.Valuation w a
  | falsum  => False
  | φ ➝ ψ => (Forces w φ) → (Forces w ψ)
  | □φ   => ∀ {w'}, w ≺[φ] w' → (Forces w' φ)
infix:45 " ⊩ " => Forces

@[simp, grind .] abbrev NotForces {M : outParam (PLoN.Model)} (x : M.World) (φ : Formula ℕ) : Prop := ¬(x ⊩ φ)
infix:45 " ⊮ " => NotForces


namespace Forces

variable {M : PLoN.Model} {x : M.World}

@[grind .] protected lemma bot_def : x ⊮ ⊥ := by simp [Forces];
@[grind .] protected lemma top_def : x ⊩ ⊤ := by simp [Forces];

@[grind =] protected lemma imp_def : x ⊩ φ ➝ ψ ↔ (x ⊩ φ) → (x ⊩ ψ) := by tauto;
@[grind =] protected lemma not_def_imp : x ⊮ φ ➝ ψ ↔ (x ⊩ φ ∧ x ⊮ ψ) := by grind

@[grind =] protected lemma or_def : x ⊩ φ ⋎ ψ ↔ x ⊩ φ ∨ x ⊩ ψ := by dsimp [Forces]; grind;
@[grind =] protected lemma not_def_or : x ⊮ φ ⋎ ψ ↔ x ⊮ φ ∧ x ⊮ ψ := by dsimp [Forces]; grind;

@[grind =] protected lemma and_def : x ⊩ φ ⋏ ψ ↔ x ⊩ φ ∧ x ⊩ ψ := by dsimp [Forces]; grind;
@[grind =] protected lemma not_def_and : x ⊮ φ ⋏ ψ ↔ x ⊮ φ ∨ x ⊮ ψ := by grind;

@[grind =] protected lemma def_neg : x ⊩ ∼φ ↔ x ⊮ φ := by dsimp [Forces]; grind;
@[grind =] protected lemma not_def_neg : x ⊮ ∼φ ↔ x ⊩ φ := by dsimp [Forces]; grind;


@[grind =] protected lemma def_iff : x ⊩ φ ⭤ ψ ↔ ((x ⊩ φ) ↔ (x ⊩ ψ)) := by dsimp [LogicalConnective.iff]; grind;
@[grind =] protected lemma not_def_iff : x ⊮ φ ⭤ ψ ↔ ((x ⊩ φ) ∧ x ⊮ ψ) ∨ (x ⊮ φ ∧ (x ⊩ ψ)) := by grind;

@[grind =] lemma box_def : x ⊩ □φ ↔ ∀ y, x ≺[φ] y → y ⊩ φ := by simp [PLoN.Forces];
@[grind =] lemma not_box_def : x ⊮ □φ ↔ ∃ y, x ≺[φ] y ∧ y ⊮ φ := by grind;

end Forces


instance : Semantics (PLoN.Model) (Formula ℕ) := ⟨fun M φ => ∀ x : M.World, x ⊩ φ⟩

namespace ValidOnModel

variable {M : PLoN.Model}

@[simp, grind =] lemma iff_models : M ⊧ φ ↔ ∀ x : M.World, x ⊩ φ := iff_of_eq rfl
@[simp, grind =] lemma iff_not_models : M ⊭ φ ↔ ∃ x : M.World, x ⊮ φ := by simp [Semantics.NotModels, Semantics.Models];

@[simp, grind .] protected lemma def_verum : M ⊧ ⊤ := by grind;
instance : Semantics.Top (PLoN.Model) := ⟨by grind⟩

@[simp, grind .] protected lemma def_bot : M ⊭ ⊥ := by
  apply iff_not_models.mpr;
  use M.default;
  simp;
instance : Semantics.Bot (PLoN.Model) := ⟨by grind⟩

@[grind .] protected lemma implyK : M ⊧ (Axioms.ImplyK φ ψ) := by grind;
@[grind .] protected lemma implyS : M ⊧ (Axioms.ImplyS φ ψ χ) := by grind;
@[grind .] protected lemma elimContra : M ⊧ (Axioms.ElimContra φ ψ) := by grind;
@[grind <=] protected lemma nec (h : M ⊧ φ) : M ⊧ □φ := by grind;
@[grind <=] protected lemma mdp (h₁ : M ⊧ φ ➝ ψ) (h₂ : M ⊧ φ) : M ⊧ ψ := fun x ↦ h₁ x (h₂ x)

protected lemma re : ¬∀ M : Model, ∀ φ ψ, M ⊧ φ ⭤ ψ → M ⊧ □φ ⭤ □ψ := by
  push_neg;
  let M : Model := {
    World := Fin 2,
    Rel ξ x y := if ξ = (.atom 1) then True else False,
    Valuation x a := x = 0
  };
  use M, (.atom 0), (.atom 1);
  constructor;
  . grind;
  . suffices (∃ x : M.World, ∀ y : M.World, x ≺[atom 0] y → y = 0) ∧ ∃ x : M.World, x ≠ 0 by
      simp [M];
      grind;
    constructor;
    . use 0;
      intro x;
      match x with
      | 0 => tauto;
      | 1 => simp [M, Frame.Rel'];
    . use 1;
      simp [M];


end ValidOnModel


instance : Semantics (PLoN.Frame) (Formula ℕ) := ⟨fun F φ => ∀ V, (⟨F, V⟩ : PLoN.Model) ⊧ φ⟩

namespace ValidOnFrame

variable {F : PLoN.Frame}

@[simp, grind .] lemma iff_models : F ⊧ φ ↔ ∀ V, (⟨F, V⟩ : PLoN.Model) ⊧ φ := by rfl
@[simp, grind .] lemma iff_not_models : F ⊭ φ ↔ ∃ V, (⟨F, V⟩ : PLoN.Model) ⊭ φ := by simp [Semantics.NotModels, Semantics.Models];

@[simp, grind .] protected lemma def_verum : F ⊧ ⊤ := by simp;
instance : Semantics.Top (PLoN.Frame) := ⟨by grind⟩

@[simp, grind .] protected lemma def_bot : F ⊭ ⊥ := by simp;
instance : Semantics.Bot (PLoN.Frame) := ⟨by grind⟩

end ValidOnFrame

end Formula.PLoN


namespace PLoN

section

variable {C : PLoN.FrameClass}

lemma iff_not_validOnFrameClass_exists_frame : (C ⊭ φ) ↔ (∃ F ∈ C, F ⊭ φ) := by
  apply not_iff_not.mp;
  push_neg;
  tauto;
alias ⟨exists_frame_of_not_validOnFrameClass, not_validOnFrameClass_of_exists_frame⟩ := iff_not_validOnFrameClass_exists_frame


lemma iff_not_validOnFrameClass_exists_model : (C ⊭ φ) ↔ (∃ M : PLoN.Model, M.toFrame ∈ C ∧ M ⊭ φ) := by
  apply not_iff_not.mp;
  push_neg;
  tauto;
alias ⟨exists_model_of_not_validOnFrameClass, not_validOnFrameClass_of_exists_model⟩ := iff_not_validOnFrameClass_exists_model

lemma iff_not_validOnFrameClass_exists_model_world : (C ⊭ φ) ↔ (∃ M : PLoN.Model, ∃ w : M.World, M.toFrame ∈ C ∧ w ⊮ φ) := by
  apply not_iff_not.mp;
  push_neg;
  tauto;
alias ⟨exists_model_world_of_not_validOnFrameClass, not_validOnFrameClass_of_exists_model_world⟩ := iff_not_validOnFrameClass_exists_model_world

end

end PLoN

end LO.Modal
