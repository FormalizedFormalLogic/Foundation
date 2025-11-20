import Foundation.Propositional.Logic.Basic
import Foundation.Propositional.Entailment.Corsi.Basic
import Foundation.Vorspiel.HRel.Basic

namespace LO.Propositional

namespace Kripke2

structure Frame where
  World : Type
  Rel : HRel World
  root : World
  rooted {w : World} : Rel root w

namespace Frame

variable {F : Frame}

instance : CoeSort Frame (Type) := ⟨World⟩
instance : CoeFun Frame (λ F => HRel F.World) := ⟨Frame.Rel⟩
instance : Nonempty F.World := ⟨F.root⟩

abbrev Rel' {F : Frame} (x y : F.World) := F.Rel x y
infix:45 " ≺ " => Rel'

abbrev Rel_on (F : Frame) (x y : F.World) := F.Rel x y
notation:45 x:max " ≺ " y:max " on " F:max => Rel_on F x y

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

end Kripke2



namespace Formula.Kripke2

open Kripke2

def Satisfies (M : Kripke2.Model) (x : M.World) : Formula ℕ → Prop
  | atom a => M x a
  | ⊥      => False
  | φ ⋏ ψ  => Satisfies M x φ ∧ Satisfies M x ψ
  | φ ⋎ ψ  => Satisfies M x φ ∨ Satisfies M x ψ
  | φ ➝ ψ => ∀ {y : M.World}, x ≺ y → (Satisfies M y φ → Satisfies M y ψ)

namespace Satisfies

instance semantics (M : Kripke2.Model) : Semantics M (Formula ℕ) := ⟨fun x ↦ Formula.Kripke2.Satisfies M x⟩

variable {M : Kripke2.Model} {x y : M.World} {a : ℕ} {φ ψ χ : Formula ℕ}

@[simp, grind =] protected lemma iff_models : x ⊧ φ ↔ Satisfies M x φ := iff_of_eq rfl

@[grind =] protected lemma def_atom : x ⊧ atom a ↔ M x a := by simp [Satisfies];
@[simp high, grind .] protected lemma def_top : x ⊧ ⊤ := by simp [Satisfies];
@[simp high, grind .] protected lemma def_bot : x ⊭ ⊥ := by simp [Semantics.NotModels, Satisfies];
@[grind =] protected lemma def_and : x ⊧ φ ⋏ ψ ↔ x ⊧ φ ∧ x ⊧ ψ := by simp [Satisfies];

@[grind =] protected lemma def_or  : x ⊧ φ ⋎ ψ ↔ x ⊧ φ ∨ x ⊧ ψ := by simp [Satisfies];
@[grind =] protected lemma not_def_or : x ⊭ φ ⋎ ψ ↔ x ⊭ φ ∧ x ⊭ ψ := by
  dsimp [Semantics.NotModels];
  grind;

@[grind =] protected lemma def_imp  : x ⊧ φ ➝ ψ ↔ ∀ {y : M.World}, (x ≺ y) → (y ⊧ φ → y ⊧ ψ) := by simp [Satisfies];
@[grind =] protected lemma not_def_imp : x ⊭ φ ➝ ψ ↔ ∃ y : M.World, (x ≺ y) ∧ (y ⊧ φ) ∧ (y ⊭ ψ) := by
  dsimp [Semantics.NotModels];
  grind;

@[grind =] protected lemma def_neg  : x ⊧ ∼φ ↔ ∀ {y : M.World}, (x ≺ y) → ¬(y ⊧ φ) := by simp [Satisfies];
@[grind =] protected lemma not_def_neg : x ⊭ ∼φ ↔ ∃ y : M.World, (x ≺ y) ∧ (y ⊧ φ) := by grind;

instance : Semantics.Top M.World := ⟨by grind⟩
instance : Semantics.Bot M.World := ⟨by grind⟩
instance : Semantics.And M.World := ⟨by grind⟩
instance : Semantics.Or M.World := ⟨by grind⟩

lemma iff_subst_self {F : Kripke2.Frame} {V : Kripke2.Valuation F} {x : F.World} (s : Substitution ℕ) :
  letI U : Kripke2.Valuation F := λ w a => Satisfies ⟨F, V⟩ w ((.atom a)⟦s⟧)
  Satisfies ⟨F, U⟩ x φ ↔ Satisfies ⟨F, V⟩ x (φ⟦s⟧) := by
  induction φ generalizing x with
  | hatom a => simp [Satisfies];
  | hfalsum => simp [Satisfies];
  | hand φ ψ ihφ ihψ =>
    constructor;
    . rintro ⟨hφ, hψ⟩; constructor <;> grind
    . rintro ⟨hφ, hψ⟩; constructor <;> grind;
  | hor φ ψ ihφ ihψ =>
    constructor;
    . rintro (hφ | hψ);
      . left; apply ihφ.mp hφ;
      . right; apply ihψ.mp hψ;
    . rintro (hφ | hψ);
      . left; apply ihφ.mpr hφ;
      . right; apply ihψ.mpr hψ;
  | himp φ ψ ihφ ihψ =>
    constructor;
    . intro hφψ y Rxy hφs;
      apply ihψ.mp;
      apply hφψ Rxy;
      apply ihφ.mpr hφs;
    . intro hφψs y Rxy hφ;
      apply ihψ.mpr;
      apply hφψs Rxy;
      apply ihφ.mp hφ;

end Satisfies


def ValidOnModel (M : Kripke2.Model) (φ : Formula ℕ) : Prop := ∀ x : M.World, Satisfies M x φ

namespace ValidOnModel

instance semantics : Semantics Kripke2.Model (Formula ℕ) := ⟨fun M ↦ ValidOnModel M⟩

variable {M : Kripke2.Model} {φ ψ χ : Formula ℕ}

@[simp, grind =] protected lemma iff_models : M ⊧ φ ↔ ∀ x : M, x ⊧ φ := iff_of_eq rfl

@[grind .] protected lemma def_verum : M ⊧ ⊤ := by simp;
@[grind .] protected lemma def_bot : M ⊭ ⊥ := by simp [Semantics.NotModels];

instance : Semantics.Top (Kripke2.Model) := ⟨by grind⟩
instance : Semantics.Bot (Kripke2.Model) := ⟨by grind⟩

lemma iff_not_models_exists_world : (M ⊭ φ) ↔ (∃ x : M.World, ¬x ⊧ φ) := by grind;
alias ⟨exists_world_of_not, not_of_exists_world⟩ := iff_not_models_exists_world


end ValidOnModel


def ValidOnFrame (F : Kripke2.Frame) (φ : Formula ℕ) : Prop := ∀ V : Kripke2.Valuation F, (⟨F, V⟩ : Kripke2.Model) ⊧ φ

namespace ValidOnFrame

instance semantics : Semantics Kripke2.Frame (Formula ℕ) := ⟨fun F ↦ ValidOnFrame F⟩

variable {F : Kripke2.Frame} {φ ψ χ : Formula ℕ}

@[simp, grind =] protected lemma iff_models : F ⊧ φ ↔ ∀ V : Kripke2.Valuation F, (⟨F, V⟩ : Kripke2.Model) ⊧ φ := iff_of_eq rfl

@[grind .] protected lemma def_verum : F ⊧ ⊤ := by simp;
@[grind .] protected lemma def_bot : F ⊭ ⊥ := by simp [Semantics.NotModels];

instance : Semantics.Top (Kripke2.Frame) := ⟨by grind⟩
instance : Semantics.Bot (Kripke2.Frame) := ⟨by grind⟩


lemma iff_not_exists_valuation : (F ⊭ φ) ↔ (∃ V : Kripke2.Valuation F, ¬(⟨F, V⟩ : Kripke2.Model) ⊧ φ) := by grind;
alias ⟨exists_valuation_of_not, not_of_exists_valuation⟩ := iff_not_exists_valuation


lemma iff_not_exists_valuation_world : (F ⊭ φ) ↔ (∃ V : Kripke2.Valuation F, ∃ x : (⟨F, V⟩ : Kripke2.Model).World, ¬Satisfies _ x φ) := by
  simp [ValidOnFrame, ValidOnModel, Semantics.Models, Semantics.NotModels];
alias ⟨exists_valuation_world_of_not, not_of_exists_valuation_world⟩ := iff_not_exists_valuation_world

@[grind =>]
protected lemma subst (s : Substitution ℕ) (h : F ⊧ φ) : F ⊧ φ⟦s⟧ := by
  by_contra hC;
  obtain ⟨V, ⟨x, hx⟩⟩ := exists_valuation_world_of_not hC;
  apply Satisfies.iff_subst_self s |>.not.mpr hx;
  apply h;

end ValidOnFrame

end Formula.Kripke2


namespace Kripke2


open Formula.Kripke2


section

variable {C : Set Frame} {φ ψ χ : Formula ℕ}

lemma iff_not_validOnFrameClass_exists_frame : C ⊭ φ ↔ ∃ F ∈ C, ¬F ⊧ φ := by
  apply not_iff_not.mp;
  push_neg;
  tauto;
alias ⟨exists_frame_of_not_validOnFrameClass, not_validOnFrameClass_of_exists_frame⟩ := iff_not_validOnFrameClass_exists_frame

lemma iff_not_validOnFrameClass_exists_model : C ⊭ φ ↔ ∃ M : Kripke2.Model, M.toFrame ∈ C ∧ M ⊭ φ := by
  apply not_iff_not.mp;
  push_neg;
  tauto;
alias ⟨exists_model_of_not_validOnFrameClass, not_validOnFrameClass_of_exists_model⟩ := iff_not_validOnFrameClass_exists_model

lemma iff_not_validOnFrameClass_exists_model_world : C ⊭ φ ↔ ∃ M : Kripke2.Model, ∃ x : M, M.toFrame ∈ C ∧ x ⊭ φ := by
  apply not_iff_not.mp;
  push_neg;
  tauto;
alias ⟨exists_model_world_of_not_validOnFrameClass, not_validOnFrameClass_of_exists_model_world⟩ := iff_not_validOnFrameClass_exists_model_world

end


section

variable {F : Frame} {φ ψ χ : Formula ℕ}

open Formula (atom)

lemma valid_andElim₁ : F ⊧ φ ⋏ ψ ➝ φ := by rintro V x y Rxy ⟨_, _⟩; assumption;
lemma valid_andElim₂ : F ⊧ φ ⋏ ψ ➝ ψ := by rintro V x y Rxy ⟨_, _⟩; assumption;
lemma valid_axiomC : F ⊧ (φ ➝ ψ) ⋏ (ψ ➝ χ) ➝ (φ ➝ (ψ ⋏ χ)) := by
  rintro V x y Rxy ⟨h₁, h₂⟩ z Ryz h₃;
  constructor;
  . apply h₁ <;> assumption;
  . apply h₂;
    . assumption;
    . apply h₁;
      . assumption;
      . assumption;

lemma valid_orIntro₁ : F ⊧ φ ➝ φ ⋎ ψ := by rintro V x y Rxy hφ; left; assumption;
lemma valid_orIntro₂ : F ⊧ ψ ➝ φ ⋎ ψ := by rintro V x y Rxy hψ; right; assumption;
lemma valid_axiomD : F ⊧ (φ ➝ χ) ⋏ (ψ ➝ χ) ➝ (φ ⋎ ψ ➝ χ) := by
  rintro V x y Rxy ⟨h₁, h₂⟩ z Ryz (hφ | hψ);
  . apply h₁ <;> assumption;
  . apply h₂ <;> assumption;

lemma valid_distributeAndOr : F ⊧ φ ⋏ (ψ ⋎ χ) ➝ (φ ⋏ ψ) ⋎ (φ ⋏ χ) := by
  rintro V x y Rxy ⟨hφ, (hψ | hχ)⟩
  . left; constructor <;> assumption;
  . right; constructor <;> assumption;

lemma valid_axiomI : F ⊧ (φ ➝ ψ) ⋏ (ψ ➝ χ) ➝ (φ ➝ χ) := by
  rintro V x y Rxy ⟨h₁, h₂⟩ z Ryz h₃;
  exact h₂ Ryz $ h₁ Ryz h₃;
lemma valid_impId : F ⊧ φ ➝ φ := by rintro V x y Rxy hφ; assumption;

attribute [simp high, grind .]
  valid_andElim₁ valid_andElim₂
  valid_axiomC
  valid_orIntro₁ valid_orIntro₂
  valid_axiomD
  valid_distributeAndOr
  valid_axiomI
  valid_impId

@[grind ⇒]
lemma valid_afortiori (h : F ⊧ φ) : F ⊧ ψ ➝ φ := by
  rintro V x y Rxy _;
  apply h;

@[grind ⇒]
lemma valid_conjunction_rule (h₁ : F ⊧ φ) (h₂ : F ⊧ ψ) : F ⊧ φ ⋏ ψ := by
  rintro V x;
  constructor;
  . apply h₁;
  . apply h₂;

@[grind ⇒]
lemma valid_modusponens (h₁ : F ⊧ φ ➝ ψ) (h₂ : F ⊧ φ) : F ⊧ ψ := by
  rintro V x;
  apply h₁;
  . apply F.rooted;
  . apply h₂;

lemma invalid_implyS :
  let F : Frame := ⟨Fin 3, (λ x y => x = 0 ∨ (x = 1 ∧ y = 2)), 0, by omega⟩
  F ⊭ (atom 0) ➝ (atom 1) ➝ (atom 0) := by
  intro F;
  apply ValidOnFrame.iff_not_exists_valuation_world.mpr;
  use (λ x a => match a with | 0 => x = 1 | 1 => x = 0 ∨ x = 2 | _ => False), 0;
  suffices 0 ≺ 1 on F ∧ ∃ x, 1 ≺ x on F ∧ (x = 0 ∨ x = 2) ∧ x ≠ 1 by simpa [F, Satisfies];
  constructor;
  . tauto;
  . use 2;
    grind;

end

end Kripke2


end LO.Propositional
