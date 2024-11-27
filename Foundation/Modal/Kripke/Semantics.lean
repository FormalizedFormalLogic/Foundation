import Foundation.Vorspiel.RelItr
import Foundation.Logic.System
import Foundation.Modal.Formula
import Foundation.Modal.Hilbert.Strength

namespace LO.Modal

open System


namespace Kripke

structure Frame where
  World : Type
  Rel : Rel World World
  [world_nonempty : Nonempty World]

instance : CoeSort Frame (Type) := ⟨Frame.World⟩
instance : CoeFun Frame (λ F => F.World → F.World → Prop) := ⟨Frame.Rel⟩
instance {F : Frame} : Nonempty F.World := F.world_nonempty

abbrev Frame.Rel' {F : Frame} (x y : F.World) := F.Rel x y
infix:45 " ≺ " => Frame.Rel'

protected abbrev Frame.RelItr' {F : Frame} (n : ℕ) := F.Rel.iterate n
notation x:45 " ≺^[" n "] " y:46 => Frame.RelItr' n x y


structure FiniteFrame extends Frame where
  [world_finite : Finite toFrame.World]
instance {F : FiniteFrame} : Finite F.World := F.world_finite

def Frame.toFinite (F : Frame) [Finite F.World] : FiniteFrame where
  toFrame := F


abbrev reflexivePointFrame : FiniteFrame where
  World := Unit
  Rel := fun _ _ => True

abbrev irreflexivePointFrame : FiniteFrame where
  World := Unit
  Rel := fun _ _ => False


abbrev FrameClass := Set Frame

abbrev FiniteFrameClass := Set FiniteFrame

def FrameClass.restrictFinite (C : FrameClass) : FiniteFrameClass := { F : FiniteFrame | F.toFrame ∈ C }

def FiniteFrameClass.toFrameClass (C : FiniteFrameClass) : FrameClass := C.image (·.toFrame)

instance : Coe (FiniteFrameClass) (FrameClass) := ⟨FiniteFrameClass.toFrameClass⟩


section

abbrev AllFrameClass : FrameClass := Set.univ

abbrev AllFiniteFrameClass : FiniteFrameClass := Set.univ

end


abbrev Valuation (F : Frame) := F.World → ℕ → Prop

structure Model extends Frame where
  Val : Valuation toFrame
instance : CoeFun (Model) (λ M => M.World → ℕ → Prop) := ⟨fun m => m.Val⟩

end Kripke



namespace Formula.Kripke

def Satisfies (M : Kripke.Model) (x : M.World) : Formula ℕ → Prop
  | atom a  => M x a
  | ⊥  => False
  | φ ➝ ψ => (Satisfies M x φ) ➝ (Satisfies M x ψ)
  | □φ   => ∀ y, x ≺ y → (Satisfies M y φ)

namespace Satisfies

protected instance semantics {M : Kripke.Model} : Semantics (Formula ℕ) (M.World) := ⟨fun x ↦ Formula.Kripke.Satisfies M x⟩

variable {M : Kripke.Model} {x : M.World} {φ ψ : Formula ℕ}

@[simp] protected lemma iff_models : x ⊧ φ ↔ Kripke.Satisfies M x φ := iff_of_eq rfl

@[simp] lemma atom_def : x ⊧ atom a ↔ M x a := by simp [Satisfies];

lemma box_def : x ⊧ □φ ↔ ∀ y, x ≺ y → y ⊧ φ := by simp [Kripke.Satisfies];

lemma dia_def : x ⊧ ◇φ ↔ ∃ y, x ≺ y ∧ y ⊧ φ := by simp [Kripke.Satisfies];

lemma not_def : x ⊧ ∼φ ↔ ¬(x ⊧ φ) := by
  induction φ using Formula.rec' generalizing x with
  | _ => simp_all [Satisfies];

lemma imp_def : x ⊧ φ ➝ ψ ↔ (x ⊧ φ) → (x ⊧ ψ) := by tauto;

lemma or_def : x ⊧ φ ⋎ ψ ↔ x ⊧ φ ∨ x ⊧ ψ := by simp [Satisfies]; tauto;

lemma and_def : x ⊧ φ ⋏ ψ ↔ x ⊧ φ ∧ x ⊧ ψ := by simp [Satisfies];

lemma top_def : x ⊧ ⊤ := by simp [Satisfies];

lemma bot_def : ¬x ⊧ ⊥ := by simp [Satisfies];

protected instance : Semantics.Tarski (M.World) where
  realize_top := λ _ => top_def;
  realize_bot := λ _ => bot_def;
  realize_imp := imp_def;
  realize_not := not_def;
  realize_or := or_def;
  realize_and := and_def;

lemma negneg_def : x ⊧ ∼∼φ ↔ x ⊧ φ := by simp [Satisfies];

lemma multibox_def : x ⊧ □^[n]φ ↔ ∀ {y}, x ≺^[n] y → y ⊧ φ := by
  induction n generalizing x with
  | zero => aesop;
  | succ n ih =>
    constructor;
    . rintro h y ⟨z, Rxz, Rzy⟩;
      replace h : ∀ y, x ≺ y → y ⊧ □^[n]φ := box_def.mp $ by simpa using h;
      exact (ih.mp $ h _ Rxz) Rzy;
    . suffices (∀ {y z}, x ≺ z → z ≺^[n] y → Satisfies M y φ) → x ⊧ (□□^[n]φ) by simpa;
      intro h y Rxy;
      apply ih.mpr;
      intro z Ryz;
      exact h Rxy Ryz;

lemma multidia_def : x ⊧ ◇^[n]φ ↔ ∃ y, x ≺^[n] y ∧ y ⊧ φ := by
  induction n generalizing x with
  | zero => simp;
  | succ n ih =>
    constructor;
    . intro h;
      replace h : x ⊧ (◇◇^[n]φ) := by simpa using h;
      obtain ⟨y, Rxy, hv⟩ := dia_def.mp h;
      obtain ⟨x, Ryx, hx⟩ := ih.mp hv;
      use x;
      constructor;
      . use y;
      . assumption;
    . rintro ⟨y, ⟨z, Rxz, Rzy⟩, hy⟩;
      suffices x ⊧ ◇◇^[n]φ by simpa;
      apply dia_def.mpr;
      use z;
      constructor;
      . assumption;
      . apply ih.mpr;
        use y;

lemma trans (hpq : x ⊧ φ ➝ ψ) (hqr : x ⊧ ψ ➝ χ) : x ⊧ φ ➝ χ := by simp_all;

lemma mdp (hpq : x ⊧ φ ➝ ψ) (hp : x ⊧ φ) : x ⊧ ψ := by simp_all;

lemma dia_dual : x ⊧ ◇φ ↔ x ⊧ ∼□(∼φ) := by simp [Satisfies];

lemma box_dual : x ⊧ □φ ↔ x ⊧ ∼◇(∼φ) := by simp [Satisfies];

lemma not_imp : ¬(x ⊧ φ ➝ ψ) ↔ x ⊧ φ ⋏ ∼ψ := by simp [Satisfies];

end Satisfies


def ValidOnModel (M : Kripke.Model) (φ : Formula ℕ) := ∀ x : M.World, x ⊧ φ

namespace ValidOnModel

instance semantics : Semantics (Formula ℕ) (Kripke.Model) := ⟨fun M ↦ Formula.Kripke.ValidOnModel M⟩

@[simp] protected lemma iff_models {M : Kripke.Model} : M ⊧ f ↔ Kripke.ValidOnModel M f := iff_of_eq rfl

instance : Semantics.Bot (Kripke.Model) where
  realize_bot M := by simp [Kripke.ValidOnModel, Kripke.Satisfies];

variable {M : Kripke.Model} {φ ψ χ : Formula ℕ}

protected lemma mdp (hpq : M ⊧ φ ➝ ψ) (hp : M ⊧ φ) : M ⊧ ψ := by
  intro x;
  exact (Satisfies.imp_def.mp $ hpq x) (hp x);

protected lemma nec (h : M ⊧ φ) : M ⊧ □φ := by
  intro x y _;
  exact h y;

protected lemma verum : M ⊧ ⊤ := by intro; tauto;

protected lemma imply₁ : M ⊧ (Axioms.Imply₁ φ ψ) := by simp [ValidOnModel]; tauto;

protected lemma imply₂ : M ⊧ (Axioms.Imply₂ φ ψ χ) := by simp [ValidOnModel]; tauto;

protected lemma elimContra : M ⊧ (Axioms.ElimContra φ ψ) := by simp [ValidOnModel, Satisfies]; tauto;

protected lemma axiomK : M ⊧ (Axioms.K φ ψ)  := by
  intro V;
  apply Satisfies.imp_def.mpr;
  intro hpq;
  apply Satisfies.imp_def.mpr;
  intro hp x Rxy;
  replace hpq := Satisfies.imp_def.mp $ hpq x Rxy;
  replace hp := hp x Rxy;
  exact hpq hp;

end ValidOnModel


def ValidOnFrame (F : Kripke.Frame) (φ : Formula ℕ) := ∀ V, (⟨F, V⟩ : Kripke.Model) ⊧ φ

namespace ValidOnFrame

instance semantics : Semantics (Formula ℕ) (Kripke.Frame) := ⟨fun F ↦ Formula.Kripke.ValidOnFrame F⟩

variable {F : Kripke.Frame}

@[simp] protected lemma models_iff : F ⊧ φ ↔ Kripke.ValidOnFrame F φ := iff_of_eq rfl

lemma models_set_iff : F ⊧* Φ ↔ ∀ φ ∈ Φ, F ⊧ φ := by simp [Semantics.realizeSet_iff];

lemma not_valid_iff_exists_valuation_world : ¬F ⊧ φ ↔ ∃ V : Kripke.Valuation F, ∃ x : F.World, ¬Satisfies ⟨F, V⟩ x φ := by
  simp [ValidOnFrame, Satisfies, ValidOnModel, Semantics.Realize];


instance : Semantics.Bot (Kripke.Frame) where
  realize_bot _ := by simp [Kripke.ValidOnFrame];

protected lemma nec (h : F ⊧ φ) : F ⊧ □φ := by
  intro V x y _;
  exact h V y;

protected lemma mdp (hpq : F ⊧ φ ➝ ψ) (hp : F ⊧ φ) : F ⊧ ψ := by
  intro V x;
  exact (hpq V x) (hp V x);

protected lemma verum : F ⊧ ⊤ := by intros _; tauto;

protected lemma imply₁ : F ⊧ (Axioms.Imply₁ φ ψ) := by intro V; exact ValidOnModel.imply₁ (M := ⟨F, V⟩);

protected lemma imply₂ : F ⊧ (Axioms.Imply₂ φ ψ χ) := by intro V; exact ValidOnModel.imply₂ (M := ⟨F, V⟩);

protected lemma elimContra : F ⊧ (Axioms.ElimContra φ ψ) := by intro V; exact ValidOnModel.elimContra (M := ⟨F, V⟩);

protected lemma axiomK : F ⊧ (Axioms.K φ ψ) := by intro V; exact ValidOnModel.axiomK (M := ⟨F, V⟩);

protected lemma axiomK_set : F ⊧* 𝗞 := by
  simp [Semantics.realizeSet_iff];
  rintro f x y rfl;
  exact ValidOnFrame.axiomK;


end ValidOnFrame



@[simp] def ValidOnFrameClass (C : Kripke.FrameClass) (φ : Formula ℕ) := ∀ {F}, F ∈ C → F ⊧ φ

namespace ValidOnFrameClass

protected instance semantics : Semantics (Formula ℕ) (Kripke.FrameClass) := ⟨fun C ↦ Kripke.ValidOnFrameClass C⟩

variable {C : Kripke.FrameClass}

@[simp] protected lemma models_iff : C ⊧ φ ↔ Formula.Kripke.ValidOnFrameClass C φ := iff_of_eq rfl

end ValidOnFrameClass


@[simp] def ValidOnFiniteFrameClass (FC : Kripke.FiniteFrameClass) (φ : Formula ℕ) := ∀ {F}, F ∈ FC → F.toFrame ⊧ φ

namespace ValidOnFiniteFrameClass

protected instance semantics : Semantics (Formula ℕ) (Kripke.FiniteFrameClass) := ⟨fun C ↦ Kripke.ValidOnFrameClass C⟩

variable {FC : Kripke.FiniteFrameClass}

@[simp] protected lemma models_iff : FC ⊧ φ ↔ Formula.Kripke.ValidOnFrameClass FC φ := iff_of_eq rfl

end ValidOnFiniteFrameClass


lemma notValidOnFiniteFrameClass_of_exists_finite_frame {FC : Kripke.FiniteFrameClass} (h : ∃ F ∈ FC, ¬F.toFrame ⊧ φ) : ¬FC ⊧ φ := by
  simp only [ValidOnFiniteFrameClass.models_iff, ValidOnFrameClass];
  push_neg;
  obtain ⟨F, hF, h⟩ := h;
  use F.toFrame;
  constructor;
  . use F;
  . assumption;

end Formula.Kripke


namespace Kripke

def Frame.theorems (F : Kripke.Frame) : Theory ℕ := { φ | F ⊧ φ }


def FrameClass.DefinedBy (C : Kripke.FrameClass) (T : Theory ℕ) := ∀ F, F ∈ C ↔ F ⊧* T

def FiniteFrameClass.DefinedBy (C : Kripke.FiniteFrameClass) (T : Theory ℕ) := ∀ F : FiniteFrame, F ∈ C ↔ F.toFrame ⊧* T


section definability

variable {C : Kripke.FrameClass} {FC : Kripke.FiniteFrameClass} {Ax : Theory ℕ}

lemma FiniteFrameClass.definedBy_of_definedBy_frameclass_aux (h : C.DefinedBy Ax) : (C.restrictFinite).DefinedBy Ax := by
  intro F;
  constructor;
  . intro hF;
    apply h F.toFrame |>.mp hF;
  . intro hF;
    apply h F.toFrame |>.mpr hF;

lemma FiniteFrameClass.definedBy_of_definedBy_frameclass (h : C.DefinedBy Ax) (e : FC = C.restrictFinite) : FC.DefinedBy Ax := by
  rw [e];
  exact FiniteFrameClass.definedBy_of_definedBy_frameclass_aux h;


lemma AllFrameClass.isDefinedBy : AllFrameClass.DefinedBy 𝗞 := by
  intro F;
  simp;
  rintro _ φ ψ rfl;
  exact Formula.Kripke.ValidOnFrame.axiomK;

lemma AllFiniteFrameClass.isDefinedBy : AllFiniteFrameClass.DefinedBy 𝗞 := FiniteFrameClass.definedBy_of_definedBy_frameclass AllFrameClass.isDefinedBy $ by rfl

end definability


end Kripke


namespace Hilbert

open Kripke

namespace Kripke

variable {H : Hilbert ℕ} {φ : Formula ℕ}
variable {T : Theory ℕ}

open Formula.Kripke

section

variable {C : FrameClass}

lemma instSound_of_frameClass_definedBy_aux (definedBy : C.DefinedBy T) : (Hilbert.ExtK T : Hilbert ℕ) ⊢! φ → C ⊧ φ := by
  intro hφ F hF;
  induction hφ using Hilbert.Deduction.inducition_with_necOnly! with
  | hImply₁ => apply ValidOnFrame.imply₁;
  | hImply₂ => apply ValidOnFrame.imply₂;
  | hElimContra => apply ValidOnFrame.elimContra;
  | hMdp ihpq ihp => exact ValidOnFrame.mdp ihpq ihp;
  | hNec ih => exact ValidOnFrame.nec ih;
  | hMaxm h =>
    simp at h;
    rcases h with (⟨_, _, rfl⟩ | hR);
    . exact Formula.Kripke.ValidOnFrame.axiomK;
    . apply Semantics.realizeSet_iff.mp (definedBy F |>.mp hF);
      assumption;

lemma instSound_of_frameClass_definedBy (definedBy : C.DefinedBy T) (heq : H =ₛ (Hilbert.ExtK T)) : Sound H C := ⟨by
  intro φ hφ;
  apply instSound_of_frameClass_definedBy_aux definedBy;
  exact Equiv.iff.mp heq φ |>.mp hφ;
⟩

lemma instConsistent_of_nonempty_frameclass_aux [sound : Sound H C] (hNonempty : C.Nonempty) : H ⊬ ⊥ := by
  apply not_imp_not.mpr sound.sound;
  simp [Semantics.Realize];
  obtain ⟨F, hF⟩ := hNonempty;
  use F;
  constructor;
  . exact hF;
  . exact Semantics.Bot.realize_bot (F := Formula ℕ) (M := Kripke.Frame) F;

lemma instConsistent_of_nonempty_frameclass [Sound H C] (h_nonempty : C.Nonempty) : H.Consistent := System.Consistent.of_unprovable $ instConsistent_of_nonempty_frameclass_aux h_nonempty

end


section

variable {FC : FiniteFrameClass}

lemma instSound_of_finiteFrameClass_definedBy_aux (definedBy : FC.DefinedBy T) : (Hilbert.ExtK T : Hilbert ℕ) ⊢! φ → FC ⊧ φ := by
  intro hφ F hF;
  obtain ⟨F, hF, rfl⟩ := hF;
  induction hφ using Hilbert.Deduction.inducition_with_necOnly! with
  | hImply₁ => apply ValidOnFrame.imply₁;
  | hImply₂ => apply ValidOnFrame.imply₂;
  | hElimContra => apply ValidOnFrame.elimContra;
  | hMdp ihpq ihp => exact ValidOnFrame.mdp ihpq ihp;
  | hNec ih => exact ValidOnFrame.nec ih;
  | hMaxm h =>
    simp at h;
    rcases h with (⟨_, _, rfl⟩ | hR);
    . exact Formula.Kripke.ValidOnFrame.axiomK;
    . apply Semantics.realizeSet_iff.mp (definedBy F |>.mp hF);
      assumption;

lemma instSound_of_finiteFrameClass_definedBy (definedBy : FC.DefinedBy T) (heq : H =ₛ (Hilbert.ExtK T)) : Sound H FC := ⟨by
  intro φ hφ;
  apply instSound_of_finiteFrameClass_definedBy_aux definedBy;
  exact Equiv.iff.mp heq φ |>.mp hφ;
⟩

lemma instConsistent_of_nonempty_finiteFrameclass_aux [sound : Sound H FC] (hNonempty : FC.Nonempty) : H ⊬ ⊥ := by
  apply not_imp_not.mpr sound.sound;
  simp [Semantics.Realize];
  obtain ⟨F, hF⟩ := hNonempty;
  use F.toFrame;
  constructor;
  . use F;
  . exact Semantics.Bot.realize_bot (F := Formula ℕ) (M := Kripke.Frame) F.toFrame;

lemma instConsistent_of_nonempty_finiteFrameclass [Sound H FC] (h_nonempty : FC.Nonempty) : H.Consistent :=
  System.Consistent.of_unprovable $ instConsistent_of_nonempty_finiteFrameclass_aux h_nonempty

end

lemma instFiniteSound_of_instSound {C : FrameClass} {FC : FiniteFrameClass} (heq : C.restrictFinite = FC) [sound : Sound H C] : Sound H FC := ⟨by
  intro φ hφ F hF;
  apply sound.sound (f := φ) hφ;
  rw [←heq] at hF;
  simp [FrameClass.restrictFinite, FiniteFrameClass.toFrameClass] at hF;
  obtain ⟨F, hF, rfl⟩ := hF;
  exact hF;
⟩

class FiniteFrameProperty (H : Hilbert ℕ) (FC : FiniteFrameClass) where
  sound : Sound H FC
  complete : Complete H FC

end Kripke


namespace K

instance Kripke.sound : Sound (Hilbert.K ℕ) (AllFrameClass) := Kripke.instSound_of_frameClass_definedBy (definedBy := Kripke.AllFrameClass.isDefinedBy) (heq := by simp [ExtK.K_is_extK_of_AxiomK])

instance consistent : System.Consistent (Hilbert.K ℕ) := Kripke.instConsistent_of_nonempty_frameclass (C := AllFrameClass) $ by
  use reflexivePointFrame.toFrame;
  tauto;

end K


section

open Formula (atom)
open Formula.Kripke

lemma K_strictlyWeakerThan_KD : (Hilbert.K ℕ) <ₛ (Hilbert.KD ℕ) := by
  constructor;
  . simp;
  . simp [weakerThan_iff];
    use (□(atom 0) ➝ ◇(atom 0));
    constructor;
    . exact axiomD!;
    . apply K.Kripke.sound.not_provable_of_countermodel;
      simp [ValidOnModel, ValidOnFrame, Satisfies];
      use ⟨Fin 1, λ _ _ => False⟩, (λ w _ => w = 0), 0;
      simp [Semantics.Realize, Satisfies];

theorem K_strictlyWeakerThan_KB : (Hilbert.K ℕ) <ₛ (Hilbert.KB ℕ) := by
  constructor;
  . simp;
  . simp [weakerThan_iff];
    use ((atom 0) ➝ □◇(atom 0));
    constructor;
    . exact axiomB!;
    . apply K.Kripke.sound.not_provable_of_countermodel;
      simp [ValidOnModel, ValidOnFrame, Satisfies];
      use ⟨Fin 2, λ x y => x = 0 ∧ y = 1⟩, (λ w _ => w = 0), 0;
      simp [Semantics.Realize, Satisfies];
      use 1;
      tauto;

theorem K_strictlyWeakerThan_K4 : (Hilbert.K ℕ) <ₛ (Hilbert.K4 ℕ) := by
  constructor;
  . simp;
  . simp [weakerThan_iff];
    use (□(atom 0) ➝ □□(atom 0));
    constructor;
    . exact axiomFour!;
    . apply K.Kripke.sound.not_provable_of_countermodel;
      simp [ValidOnModel, ValidOnFrame, Satisfies];
      use ⟨Fin 2, λ x y => x ≠ y⟩, (λ w _ => w = 1), 0;
      simp [Semantics.Realize, Satisfies];
      constructor;
      . intro x;
        match x with
        | 0 => tauto;
        | 1 => tauto;
      . use 1;
        constructor;
        . tauto;
        . use 0; tauto;

theorem K_strictlyWeakerThan_K5 : (Hilbert.K ℕ) <ₛ (Hilbert.K5 ℕ) := by
  constructor;
  . simp;
  . simp [weakerThan_iff];
    use (◇(atom default) ➝ □◇(atom default));
    constructor;
    . exact axiomFive!;
    . apply K.Kripke.sound.not_provable_of_countermodel;
      simp [ValidOnModel, ValidOnFrame, Satisfies];
      use ⟨Fin 2, λ x _ => x = 0⟩, (λ w _ => w = 0), 0;
      simp [Semantics.Realize, Satisfies];
      use 1;
      tauto;

end


section

variable {Ax₁ Ax₂ : Theory ℕ} (C₁ C₂ : FrameClass)

lemma Kripke.weakerThan_of_subset_FrameClass
  [sound₁ : Sound (Hilbert.ExtK Ax₁) C₁] [complete₂ : Complete (Hilbert.ExtK Ax₂) C₂]
  (h𝔽 : C₂ ⊆ C₁)
  : (Hilbert.ExtK Ax₁) ≤ₛ (Hilbert.ExtK Ax₂) := by
  apply System.weakerThan_iff.mpr;
  intro φ hp;
  apply complete₂.complete;
  intro F hF;
  exact sound₁.sound hp $ h𝔽 hF;

lemma Kripke.equiv_of_eq_FrameClass
  [sound₁ : Sound (Hilbert.ExtK Ax₁) C₁] [sound₂ : Sound (Hilbert.ExtK Ax₂) C₂]
  [complete₁ : Complete (Hilbert.ExtK Ax₁) C₁] [complete₂ : Complete (Hilbert.ExtK Ax₂) C₂]
  (hC : C₁ = C₂) : (Hilbert.ExtK Ax₁) =ₛ (Hilbert.ExtK Ax₂) := by
  apply System.Equiv.antisymm_iff.mpr;
  constructor;
  . apply weakerThan_of_subset_FrameClass C₁ C₂; subst_vars; rfl;
  . apply weakerThan_of_subset_FrameClass C₂ C₁; subst_vars; rfl;

end

end Hilbert

end LO.Modal
