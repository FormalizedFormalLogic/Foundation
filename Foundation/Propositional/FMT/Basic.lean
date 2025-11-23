/-
  Fitting-Marek-Truszczyński Semantics
-/
import Foundation.Propositional.Logic.Basic
import Foundation.Propositional.Entailment.Corsi.Basic
import Foundation.Vorspiel.HRel.Basic

namespace LO.Propositional

namespace FMT

structure Frame where
  World : Type
  Rel : Formula ℕ → HRel World
  root : World
  rooted {φ} {w : World} : Rel φ root w

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

def Satisfies (M : FMT.Model) (x : M.World) : Formula ℕ → Prop
  | atom a => M x a
  | ⊥      => False
  | φ ⋏ ψ  => Satisfies M x φ ∧ Satisfies M x ψ
  | φ ⋎ ψ  => Satisfies M x φ ∨ Satisfies M x ψ
  | φ ➝ ψ => ∀ {y : M.World}, x ≺[φ] y → (Satisfies M y φ → Satisfies M y ψ)

namespace Satisfies

instance semantics (M : FMT.Model) : Semantics M (Formula ℕ) := ⟨fun x ↦ Formula.FMT.Satisfies M x⟩

variable {M : FMT.Model} {x y : M.World} {a : ℕ} {φ ψ χ : Formula ℕ}

@[simp, grind =] protected lemma iff_models : x ⊧ φ ↔ Satisfies M x φ := iff_of_eq rfl

@[grind =] protected lemma def_atom : x ⊧ atom a ↔ M x a := by simp [Satisfies];
@[simp high, grind .] protected lemma def_top : x ⊧ ⊤ := by simp [Satisfies];
@[simp high, grind .] protected lemma def_bot : x ⊭ ⊥ := by simp [Semantics.NotModels, Satisfies];

@[grind =] protected lemma def_and : x ⊧ φ ⋏ ψ ↔ x ⊧ φ ∧ x ⊧ ψ := by simp [Satisfies];
@[grind =] protected lemma not_def_and : x ⊭ φ ⋏ ψ ↔ x ⊭ φ ∨ x ⊭ ψ := by
  dsimp [Semantics.NotModels];
  grind;

@[grind =] protected lemma def_or  : x ⊧ φ ⋎ ψ ↔ x ⊧ φ ∨ x ⊧ ψ := by simp [Satisfies];
@[grind =] protected lemma not_def_or : x ⊭ φ ⋎ ψ ↔ x ⊭ φ ∧ x ⊭ ψ := by
  dsimp [Semantics.NotModels];
  grind;

@[grind =] protected lemma def_imp  : x ⊧ φ ➝ ψ ↔ ∀ {y : M.World}, (x ≺[φ] y) → (y ⊧ φ → y ⊧ ψ) := by simp [Satisfies];
@[grind =] protected lemma not_def_imp : x ⊭ φ ➝ ψ ↔ ∃ y : M.World, (x ≺[φ] y) ∧ (y ⊧ φ) ∧ (y ⊭ ψ) := by
  dsimp [Semantics.NotModels];
  grind;

@[grind =] protected lemma def_neg  : x ⊧ ∼φ ↔ ∀ {y : M.World}, (x ≺[φ] y) → ¬(y ⊧ φ) := by simp [Satisfies];
@[grind =] protected lemma not_def_neg : x ⊭ ∼φ ↔ ∃ y : M.World, (x ≺[φ] y) ∧ (y ⊧ φ) := by grind;

instance : Semantics.Top M.World := ⟨by grind⟩
instance : Semantics.Bot M.World := ⟨by grind⟩
instance : Semantics.And M.World := ⟨by grind⟩
instance : Semantics.Or M.World := ⟨by grind⟩

/-
lemma iff_subst_self {F : FMT.Frame} {V : FMT.Valuation F} {x : F.World} (s : Substitution ℕ) :
  letI U : FMT.Valuation F := λ w a => Satisfies ⟨F, V⟩ w ((.atom a)⟦s⟧)
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
      apply hφψ;
      apply hφψ Rxy;
      apply ihφ.mpr hφs;
    . intro hφψs y Rxy hφ;
      apply ihψ.mpr;
      apply hφψs Rxy;
      apply ihφ.mp hφ;
-/

end Satisfies


def ValidOnModel (M : FMT.Model) (φ : Formula ℕ) : Prop := ∀ x : M.World, Satisfies M x φ

namespace ValidOnModel

instance semantics : Semantics FMT.Model (Formula ℕ) := ⟨fun M ↦ ValidOnModel M⟩

variable {M : FMT.Model} {φ ψ χ : Formula ℕ}

@[simp, grind =] protected lemma iff_models : M ⊧ φ ↔ ∀ x : M, x ⊧ φ := iff_of_eq rfl

@[grind .] protected lemma def_verum : M ⊧ ⊤ := by simp;
@[grind .] protected lemma def_bot : M ⊭ ⊥ := by simp [Semantics.NotModels];

instance : Semantics.Top (FMT.Model) := ⟨by grind⟩
instance : Semantics.Bot (FMT.Model) := ⟨by grind⟩

lemma iff_not_models_exists_world : (M ⊭ φ) ↔ (∃ x : M.World, ¬x ⊧ φ) := by grind;
alias ⟨exists_world_of_not, not_of_exists_world⟩ := iff_not_models_exists_world


end ValidOnModel


def ValidOnFrame (F : FMT.Frame) (φ : Formula ℕ) : Prop := ∀ V : FMT.Valuation F, (⟨F, V⟩ : FMT.Model) ⊧ φ

namespace ValidOnFrame

instance semantics : Semantics FMT.Frame (Formula ℕ) := ⟨fun F ↦ ValidOnFrame F⟩

variable {F : FMT.Frame} {φ ψ χ : Formula ℕ}

@[simp, grind =] protected lemma iff_models : F ⊧ φ ↔ ∀ V : FMT.Valuation F, (⟨F, V⟩ : FMT.Model) ⊧ φ := iff_of_eq rfl

@[grind .] protected lemma def_verum : F ⊧ ⊤ := by simp;
@[grind .] protected lemma def_bot : F ⊭ ⊥ := by simp [Semantics.NotModels];

instance : Semantics.Top (FMT.Frame) := ⟨by grind⟩
instance : Semantics.Bot (FMT.Frame) := ⟨by grind⟩


lemma iff_not_exists_valuation : (F ⊭ φ) ↔ (∃ V : FMT.Valuation F, ¬(⟨F, V⟩ : FMT.Model) ⊧ φ) := by grind;
alias ⟨exists_valuation_of_not, not_of_exists_valuation⟩ := iff_not_exists_valuation


lemma iff_not_exists_valuation_world : (F ⊭ φ) ↔ (∃ V : FMT.Valuation F, ∃ x : (⟨F, V⟩ : FMT.Model).World, ¬Satisfies _ x φ) := by
  simp [ValidOnFrame, ValidOnModel, Semantics.Models, Semantics.NotModels];
alias ⟨exists_valuation_world_of_not, not_of_exists_valuation_world⟩ := iff_not_exists_valuation_world

/-
@[grind =>]
protected lemma subst (s : Substitution ℕ) (h : F ⊧ φ) : F ⊧ φ⟦s⟧ := by
  by_contra hC;
  obtain ⟨V, ⟨x, hx⟩⟩ := exists_valuation_world_of_not hC;
  apply Satisfies.iff_subst_self s |>.not.mpr hx;
  apply h;
-/

end ValidOnFrame

end Formula.FMT


namespace FMT


open Formula.FMT


section

variable {C : Set Frame} {φ ψ χ : Formula ℕ}

lemma iff_not_validOnFrameClass_exists_frame : C ⊭ φ ↔ ∃ F ∈ C, ¬F ⊧ φ := by
  apply not_iff_not.mp;
  push_neg;
  tauto;
alias ⟨exists_frame_of_not_validOnFrameClass, not_validOnFrameClass_of_exists_frame⟩ := iff_not_validOnFrameClass_exists_frame

lemma iff_not_validOnFrameClass_exists_model : C ⊭ φ ↔ ∃ M : FMT.Model, M.toFrame ∈ C ∧ M ⊭ φ := by
  apply not_iff_not.mp;
  push_neg;
  tauto;
alias ⟨exists_model_of_not_validOnFrameClass, not_validOnFrameClass_of_exists_model⟩ := iff_not_validOnFrameClass_exists_model

lemma iff_not_validOnFrameClass_exists_model_world : C ⊭ φ ↔ ∃ M : FMT.Model, ∃ x : M, M.toFrame ∈ C ∧ x ⊭ φ := by
  apply not_iff_not.mp;
  push_neg;
  tauto;
alias ⟨exists_model_world_of_not_validOnFrameClass, not_validOnFrameClass_of_exists_model_world⟩ := iff_not_validOnFrameClass_exists_model_world

end


section

variable {F : Frame} {φ ψ χ : Formula ℕ}

open Formula (atom)

lemma valid_andElim₁ : F ⊧ Axioms.AndElim₁ φ ψ := by rintro V x y Rxy ⟨_, _⟩; assumption;
lemma valid_andElim₂ : F ⊧ Axioms.AndElim₂ φ ψ := by rintro V x y Rxy ⟨_, _⟩; assumption;
lemma valid_axiomC : F ⊧ Axioms.C φ ψ χ := by
  rintro V x y Rxy ⟨h₁, h₂⟩ z Ryz h₃;
  constructor;
  . apply h₁ <;> assumption;
  . apply h₂;
    . assumption;
    . assumption;

lemma valid_orIntro₁ : F ⊧ Axioms.OrInst₁ φ ψ := by rintro V x y Rxy hφ; left; assumption;
lemma valid_orIntro₂ : F ⊧ Axioms.OrInst₂ φ ψ := by rintro V x y Rxy hψ; right; assumption;

lemma valid_distributeAndOr : F ⊧ Axioms.DistributeAndOr φ ψ χ := by
  rintro V x y Rxy ⟨hφ, (hψ | hχ)⟩
  . left; constructor <;> assumption;
  . right; constructor <;> assumption;
lemma valid_impId : F ⊧ Axioms.ImpId φ := by rintro V x y Rxy hφ; assumption;

lemma valid_efq : F ⊧ Axioms.EFQ φ := by
  rintro V x y Rxy;
  simp [Satisfies];

attribute [simp high, grind .]
  valid_andElim₁ valid_andElim₂
  valid_axiomC
  valid_orIntro₁ valid_orIntro₂
  valid_distributeAndOr
  valid_impId
  valid_efq

@[grind <=]
lemma valid_afortiori (h : F ⊧ φ) : F ⊧ ψ ➝ φ := by
  rintro V x y Rxy _;
  apply h;

@[grind <=]
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

@[grind <=]
lemma valid_dilemma (h₁ : F ⊧ φ ➝ χ) (h₂ : F ⊧ ψ ➝ χ) : F ⊧ φ ⋎ ψ ➝ χ := by
  rintro V x y Rxy (hφ | hψ);
  . apply h₁ _ F.root <;> grind;
  . apply h₂ _ F.root <;> grind;

@[grind <=]
lemma valid_greedy (h₁ : F ⊧ φ ➝ ψ) (h₂ : F ⊧ φ ➝ χ) : F ⊧ φ ➝ ψ ⋏ χ := by
  rintro V x y Rxy hφ;
  constructor;
  . apply h₁ _ x <;> grind;
  . apply h₂ _ x <;> grind;

@[grind <=]
lemma valid_CTrans (h₁ : F ⊧ φ ➝ ψ) (h₂ : F ⊧ ψ ➝ χ) : F ⊧ φ ➝ χ := by
  intro V x y Rxy hyφ;
  apply h₂ _ F.root;
  . apply F.rooted;
  . apply h₁ _ F.root;
    . apply F.rooted;
    . assumption;

example :
  let F : Frame := {
    World := Fin 3,
    Rel := λ φ x y =>
      match φ, x, y with
      | _, 0, _ => True
      | #1, 1, 2 => True
      | _, _, _ => False
    ,
    root := 0,
    rooted := by simp
  };
  F ⊧ #0 ⭤ #1 → F ⊧ #2 ⭤ #3 → F ⊭ (#0 ➝ #2) ⭤ (#1 ➝ #3) := by
  rintro F h₁ h₂;
  apply ValidOnFrame.not_of_exists_valuation_world;
  use λ w a =>
    match w, a with
    | 2, 3 => False
    | _, _ => True;
  use 0;
  apply Satisfies.not_def_and.mpr;
  apply or_not_of_imp;
  intro h₃;
  apply Satisfies.not_def_imp.mpr;
  use 1;
  refine ⟨?_, ?_, ?_⟩;
  . tauto;
  . intro z R1z;
    match z with
    | 0 => tauto;
    | 1 => tauto;
    | 2 => tauto;
  . apply Satisfies.not_def_imp.mpr;
    use 2;
    tauto;

end

end FMT


end LO.Propositional
