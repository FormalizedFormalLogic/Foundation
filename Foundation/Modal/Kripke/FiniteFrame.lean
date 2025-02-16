import Foundation.Modal.Kripke.Basic

namespace LO.Modal

namespace Kripke

structure FiniteFrame extends Frame where
  [world_finite : Finite toFrame.World]

instance {F : FiniteFrame} : Finite F.World := F.world_finite


def Frame.toFinite (F : Frame) [Finite F.World] : FiniteFrame where
  toFrame := F


abbrev FiniteFrameClass := Set FiniteFrame

def FrameClass.restrictFinite (C : FrameClass) : FiniteFrameClass := { F : FiniteFrame | F.toFrame ∈ C }

def FiniteFrameClass.toFrameClass (C : FiniteFrameClass) : FrameClass := C.image (·.toFrame)

instance : Coe (FiniteFrameClass) (FrameClass) := ⟨FiniteFrameClass.toFrameClass⟩


abbrev reflexivePointFrame : FiniteFrame where
  World := Unit
  Rel := fun _ _ => True

abbrev irreflexivePointFrame : FiniteFrame where
  World := Unit
  Rel := fun _ _ => False

end Kripke


namespace Formula.Kripke

def ValidOnFiniteFrame (F : Kripke.FiniteFrame) (φ : Formula ℕ) := F.toFrame ⊧ φ

namespace ValidOnFiniteFrame

instance semantics : Semantics (Formula ℕ) (Kripke.FiniteFrame) := ⟨fun F ↦ Formula.Kripke.ValidOnFiniteFrame F⟩

variable {F : Kripke.FiniteFrame}

@[simp] protected lemma models_iff : F ⊧ φ ↔ Kripke.ValidOnFiniteFrame F φ := iff_of_eq rfl

lemma models_set_iff : F ⊧* Φ ↔ ∀ φ ∈ Φ, F ⊧ φ := by simp [Semantics.realizeSet_iff];

protected lemma top_def : F ⊧ ⊤ := by simp [ValidOnFiniteFrame];

protected lemma bot_def : ¬F ⊧ ⊥ := by simp [ValidOnFiniteFrame];

instance : Semantics.Top (Kripke.FiniteFrame) where
  realize_top _ := ValidOnFrame.top_def;

instance : Semantics.Bot (Kripke.FiniteFrame) where
  realize_bot _ := ValidOnFrame.bot_def

lemma iff_not_exists_valuation : (¬F ⊧ φ) ↔ (∃ V : Kripke.Valuation F.toFrame, ¬(⟨F.toFrame, V⟩ : Kripke.Model) ⊧ φ) := by
  exact ValidOnFrame.iff_not_exists_valuation;

alias ⟨exists_valuation_of_not, not_of_exists_valuation⟩ := iff_not_exists_valuation

lemma iff_not_exists_valuation_world : (¬F ⊧ φ) ↔ (∃ V : Kripke.Valuation F.toFrame, ∃ x : (⟨F.toFrame, V⟩ : Kripke.Model).World, ¬Satisfies _ x φ) := by
  exact ValidOnFrame.iff_not_exists_valuation_world;

alias ⟨exists_valuation_world_of_not, not_of_exists_valuation_world⟩ := iff_not_exists_valuation_world

end ValidOnFiniteFrame


def ValidOnFiniteFrameClass (C : Kripke.FiniteFrameClass) (φ : Formula ℕ) := C.toFrameClass ⊧ φ

namespace ValidOnFiniteFrameClass

protected instance semantics : Semantics (Formula ℕ) (Kripke.FiniteFrameClass) := ⟨fun C ↦ Kripke.ValidOnFrameClass C⟩

variable {C : Kripke.FiniteFrameClass}

@[simp] protected lemma models_iff : C ⊧ φ ↔ Formula.Kripke.ValidOnFrameClass C φ := iff_of_eq rfl

lemma iff_not_exists_frame : (¬C ⊧ φ) ↔ (∃ F ∈ C, ¬F ⊧ φ) := by
  convert ValidOnFrameClass.iff_not_exists_frame;
  simp [Kripke.FiniteFrameClass.toFrameClass, ValidOnFiniteFrame ];

alias ⟨exists_frame_of_not, not_of_exists_frame⟩ := iff_not_exists_frame

end ValidOnFiniteFrameClass

end Formula.Kripke



namespace Kripke

namespace FiniteFrameClass

class DefinedBy (C : Kripke.FiniteFrameClass) (Γ : Set (Formula ℕ)) where
  defines : ∀ F, F ∈ C ↔ (∀ φ ∈ Γ, F ⊧ φ)

class FiniteDefinedBy (C Γ) extends FiniteFrameClass.DefinedBy C Γ where
  finite : Set.Finite Γ

abbrev DefinedByFormula (C) (φ : Formula ℕ) := FiniteFrameClass.DefinedBy C {φ}

lemma definedByFormula_of_iff_mem_validate (h : ∀ F, F ∈ C ↔ F ⊧ φ) : DefinedByFormula C φ := by
  constructor;
  simpa;

instance definedBy_inter
  (C₁ Γ₁) [h₁ : DefinedBy C₁ Γ₁]
  (C₂ Γ₂) [h₂ : DefinedBy C₂ Γ₂]
  : DefinedBy (C₁ ∩ C₂) (Γ₁ ∪ Γ₂) := ⟨by
  rintro F;
  constructor
  . rintro ⟨hF₁, hF₂⟩;
    rintro φ (hφ₁ | hφ₂);
    . exact h₁.defines F |>.mp hF₁ _ hφ₁;
    . exact h₂.defines F |>.mp hF₂ _ hφ₂;
  . intro h;
    constructor;
    . apply h₁.defines F |>.mpr;
      intro φ hφ;
      apply h;
      left;
      assumption;
    . apply h₂.defines F |>.mpr;
      intro φ hφ;
      apply h;
      right;
      assumption;
⟩

class IsNonempty (C : Kripke.FiniteFrameClass) where
  nonempty : Nonempty C

end FiniteFrameClass


abbrev AllFiniteFrameClass : FiniteFrameClass := Set.univ

instance AllFiniteFrameClass.DefinedBy : AllFiniteFrameClass.DefinedByFormula (Axioms.K (.atom 0) (.atom 1)) :=
  FiniteFrameClass.definedByFormula_of_iff_mem_validate $ by
    simp only [Set.mem_univ, true_iff];
    intro F;
    exact Formula.Kripke.ValidOnFrame.axiomK;

instance AllFiniteFrameClass.IsNonempty : AllFiniteFrameClass.IsNonempty := by
  use ⟨Unit, λ _ _ => True⟩;
  simp;


namespace FiniteFrameClass

variable {C : Kripke.FiniteFrameClass}

instance definedBy_with_axiomK (defines : C.DefinedBy Γ) : DefinedBy C (insert (Axioms.K (.atom 0) (.atom 1)) Γ) := by
  convert FiniteFrameClass.definedBy_inter AllFiniteFrameClass {Axioms.K (.atom 0) (.atom 1)} C Γ
  simp;

end FiniteFrameClass

end Kripke

end LO.Modal
