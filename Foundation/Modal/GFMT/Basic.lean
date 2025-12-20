import Foundation.Modal.Formula
import Foundation.Modal.Axioms

namespace LO.Modal

open Formula (atom)
variable {φ ψ χ : Formula ℕ}

namespace GFMT

structure Frame where
  World : Type
  Rel : Formula ℕ → World → World → Prop
  Phi : Formula ℕ → Set (Formula ℕ)
  [World_nonempty : Nonempty World]

namespace Frame

variable {F : GFMT.Frame}

noncomputable abbrev default {F : GFMT.Frame} : F.World := F.World_nonempty.some

instance : CoeSort GFMT.Frame (Type) := ⟨World⟩
instance : CoeFun GFMT.Frame (λ F => Formula ℕ → F.World → F.World → Prop) := ⟨Frame.Rel⟩
instance : Nonempty F.World := F.World_nonempty

abbrev Rel' {F : GFMT.Frame} (φ : Formula ℕ) (x y : F.World) := F.Rel φ x y
notation:45 x:90 " ≺[" φ "] " y:90 => Rel' φ x y

end Frame



abbrev terminalFrame : GFMT.Frame where
  World := Unit
  Rel := λ _ _ _ => True
  Phi := λ _ => ∅


abbrev FrameClass := Set (GFMT.Frame)

abbrev Valuation (F : GFMT.Frame) := F.World → ℕ → Prop

structure Model extends GFMT.Frame where
  Valuation : GFMT.Valuation toFrame

end GFMT



open GFMT

namespace Formula.GFMT

@[simp, grind .]
def Forces {M : outParam GFMT.Model} (x : M.World) : Formula ℕ → Prop
  | atom a  => M.Valuation x a
  | falsum  => False
  | φ ➝ ψ => (Forces x φ) → (Forces x ψ)
  | □φ   => ∀ ψ ∈ M.Phi φ, ∀ y, x ≺[ψ] y → (Forces y φ)
infix:45 " ⊩ " => Forces

@[simp, grind .] abbrev NotForces {M : outParam GFMT.Model} (x : M.World) (φ : Formula ℕ) : Prop := ¬(x ⊩ φ)
infix:45 " ⊮ " => NotForces


namespace Forces

variable {M : GFMT.Model} {x : M.World}

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

@[grind =] lemma box_def : x ⊩ □φ ↔ ∀ ψ, ψ ∈ M.Phi φ → ∀ y, x ≺[ψ] y → y ⊩ φ := by simp [GFMT.Forces];
@[grind =] lemma not_box_def : x ⊮ □φ ↔ ∃ ψ, ψ ∈ M.Phi φ ∧ ∃ y, x ≺[ψ] y ∧ y ⊮ φ := by grind;

end Forces


instance : Semantics (GFMT.Model) (Formula ℕ) := ⟨fun M φ => ∀ x : M.World, x ⊩ φ⟩

namespace ValidOnModel

variable {M : GFMT.Model}

@[simp, grind =] lemma iff_models : M ⊧ φ ↔ ∀ x : M.World, x ⊩ φ := iff_of_eq rfl
@[simp, grind =] lemma iff_not_models : M ⊭ φ ↔ ∃ x : M.World, x ⊮ φ := by simp [Semantics.NotModels, Semantics.Models];

@[simp, grind .] protected lemma def_verum : M ⊧ ⊤ := by grind;
instance : Semantics.Top (GFMT.Model) := ⟨by grind⟩

@[simp, grind .] protected lemma def_bot : M ⊭ ⊥ := by
  apply iff_not_models.mpr;
  use M.default;
  simp;
instance : Semantics.Bot (GFMT.Model) := ⟨by grind⟩

@[grind .] protected lemma implyK : M ⊧ (Axioms.ImplyK φ ψ) := by grind;
@[grind .] protected lemma implyS : M ⊧ (Axioms.ImplyS φ ψ χ) := by grind;
@[grind .] protected lemma elimContra : M ⊧ (Axioms.ElimContra φ ψ) := by grind;
@[grind <=] protected lemma nec (h : M ⊧ φ) : M ⊧ □φ := by grind;
@[grind <=] protected lemma mdp (h₁ : M ⊧ φ ➝ ψ) (h₂ : M ⊧ φ) : M ⊧ ψ := fun x ↦ h₁ x (h₂ x)

end ValidOnModel


instance : Semantics (GFMT.Frame) (Formula ℕ) := ⟨fun F φ => ∀ V, (⟨F, V⟩ : GFMT.Model) ⊧ φ⟩

namespace ValidOnFrame

variable {F : GFMT.Frame}

@[simp, grind .] lemma iff_models : F ⊧ φ ↔ ∀ V, (⟨F, V⟩ : GFMT.Model) ⊧ φ := by rfl
@[simp, grind .] lemma iff_not_models : F ⊭ φ ↔ ∃ V, (⟨F, V⟩ : GFMT.Model) ⊭ φ := by simp [Semantics.NotModels, Semantics.Models];

@[simp, grind .] protected lemma def_verum : F ⊧ ⊤ := by simp;
instance : Semantics.Top (GFMT.Frame) := ⟨by grind⟩

@[simp, grind .] protected lemma def_bot : F ⊭ ⊥ := by simp;
instance : Semantics.Bot (GFMT.Frame) := ⟨by grind⟩

end ValidOnFrame

end Formula.GFMT


namespace GFMT

section

variable {C : GFMT.FrameClass}

lemma iff_not_validOnFrameClass_exists_frame : (C ⊭ φ) ↔ (∃ F ∈ C, F ⊭ φ) := by
  apply not_iff_not.mp;
  push_neg;
  tauto;
alias ⟨exists_frame_of_not_validOnFrameClass, not_validOnFrameClass_of_exists_frame⟩ := iff_not_validOnFrameClass_exists_frame


lemma iff_not_validOnFrameClass_exists_model : (C ⊭ φ) ↔ (∃ M : GFMT.Model, M.toFrame ∈ C ∧ M ⊭ φ) := by
  apply not_iff_not.mp;
  push_neg;
  tauto;
alias ⟨exists_model_of_not_validOnFrameClass, not_validOnFrameClass_of_exists_model⟩ := iff_not_validOnFrameClass_exists_model

lemma iff_not_validOnFrameClass_exists_model_world : (C ⊭ φ) ↔ (∃ M : GFMT.Model, ∃ w : M.World, M.toFrame ∈ C ∧ w ⊮ φ) := by
  apply not_iff_not.mp;
  push_neg;
  tauto;
alias ⟨exists_model_world_of_not_validOnFrameClass, not_validOnFrameClass_of_exists_model_world⟩ := iff_not_validOnFrameClass_exists_model_world

end

end GFMT


namespace GFMT

namespace Frame

class HasC (F : GFMT.Frame) where
  Phi_CL : ∀ {φ ψ χ}, χ ∈ F.Phi (φ ⋏ ψ) → χ ∈ F.Phi φ
  Phi_CR : ∀ {φ ψ χ}, χ ∈ F.Phi (φ ⋏ ψ) → χ ∈ F.Phi ψ
export HasC (Phi_CL Phi_CR)

class HasM (F : GFMT.Frame) where
  Phi_ML : ∀ {φ ψ χ}, χ ∈ F.Phi φ → χ ∈ F.Phi (φ ⋏ ψ)
  Phi_MR : ∀ {φ ψ χ}, χ ∈ F.Phi ψ → χ ∈ F.Phi (φ ⋏ ψ)
export HasM (Phi_ML Phi_MR)

end Frame

variable {F : GFMT.Frame} {φ ψ : Formula ℕ}

open Formula.GFMT
open Frame

lemma valid_axiomC [Frame.HasC F] : F ⊧ (Axioms.C φ ψ) := by
  intros V x hx χ hχ y RΦxy;
  replace ⟨hxφ, hxψ⟩ := Forces.and_def.mp hx;
  apply Forces.and_def.mpr;
  constructor;
  . apply hxφ χ;
    . apply Phi_CL hχ;
    . exact RΦxy;
  . apply hxψ χ;
    . apply Phi_CR hχ;
    . exact RΦxy;

lemma valid_axiomM [Frame.HasM F] : F ⊧ (Axioms.M φ ψ) := by
  intro V x hx
  apply Forces.and_def.mpr;
  constructor;
  . intro χ hχ y Rxy;
    apply (Forces.and_def.mp $ hx χ ?_ y Rxy) |>.1;
    apply Phi_ML hχ;
  . intro χ hχ y Rxy;
    apply (Forces.and_def.mp $ hx χ ?_ y Rxy) |>.2;
    apply Phi_MR hχ;

end GFMT



end LO.Modal
