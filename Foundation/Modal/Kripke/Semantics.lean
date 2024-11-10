import Foundation.Vorspiel.BinaryRelations
import Foundation.Vorspiel.RelItr
import Foundation.Logic.System
import Foundation.Modal.Formula
import Foundation.Modal.Hilbert

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

def Frame.isFinite (F : Frame) := Finite F.World

abbrev reflexivePointFrame : Frame where
  World := Unit
  Rel := fun _ _ => True

abbrev irreflexivePointFrame : Frame where
  World := Unit
  Rel := fun _ _ => False


abbrev FrameClass := Set Frame

section

abbrev AllFrameClass : FrameClass := Set.univ

abbrev SymmetricFrameClass : FrameClass := { F : Kripke.Frame | Symmetric F }

abbrev ConfluentFrameClass : FrameClass := { F : Kripke.Frame | Confluent F }

abbrev ConnectedFrameClass : FrameClass := { F : Kripke.Frame | Connected F }

abbrev EuclideanFrameClass : FrameClass := { F : Kripke.Frame | Euclidean F }

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

@[simp]
protected lemma iff_models : x ⊧ φ ↔ Kripke.Satisfies M x φ := iff_of_eq rfl

lemma box_def : x ⊧ □φ ↔ ∀ y, x ≺ y → y ⊧ φ := by simp [Kripke.Satisfies];

lemma dia_def : x ⊧ ◇φ ↔ ∃ y, x ≺ y ∧ y ⊧ φ := by simp [Kripke.Satisfies];

lemma not_def : x ⊧ ∼φ ↔ ¬(x ⊧ φ) := by
  induction φ using Formula.rec' generalizing x with
  | _ => simp_all [Satisfies];
instance : Semantics.Not (M.World) := ⟨not_def⟩

lemma imp_def : x ⊧ φ ➝ ψ ↔ (x ⊧ φ) → (x ⊧ ψ) := by tauto;
instance : Semantics.Imp (M.World) := ⟨imp_def⟩

lemma or_def : x ⊧ φ ⋎ ψ ↔ x ⊧ φ ∨ x ⊧ ψ := by simp [Satisfies]; tauto;
instance : Semantics.Or (M.World) := ⟨or_def⟩

lemma and_def : x ⊧ φ ⋏ ψ ↔ x ⊧ φ ∧ x ⊧ ψ := by simp [Satisfies];
instance : Semantics.And (M.World) := ⟨and_def⟩

protected instance : Semantics.Tarski (M.World) where
  realize_top := by tauto;
  realize_bot := by tauto;

lemma negneg_def : x ⊧ ∼∼φ ↔ x ⊧ φ := by simp [Satisfies];

lemma multibox_def : x ⊧ □^[n]φ ↔ ∀ {y}, x ≺^[n] y → y ⊧ φ := by
  induction n generalizing x with
  | zero => aesop;
  | succ n ih =>
    constructor;
    . intro h y Rxy;
      simp [Kripke.Satisfies] at h;
      obtain ⟨u, Rxu, Ruy⟩ := Rxy;
      exact (ih.mp $ h _ Rxu) Ruy;
    . simp;
      intro h y Rxy;
      apply ih.mpr;
      intro u Ryu;
      exact h _ Rxy Ryu;

lemma multidia_def : x ⊧ ◇^[n]φ ↔ ∃ y, x ≺^[n] y ∧ y ⊧ φ := by
  induction n generalizing x with
  | zero => simp;
  | succ n ih =>
    constructor;
    . intro h;
      replace h : x ⊧ (◇◇^[n]φ) := by simpa using h;
      obtain ⟨v, hwv, hv⟩ := dia_def.mp h;
      obtain ⟨x, hvx, hx⟩ := ih.mp hv;
      use x;
      constructor;
      . use v;
      . assumption;
    . intro h;
      obtain ⟨y, Rxy, hy⟩ := h;
      obtain ⟨u, Rxu, Ruy⟩ := Rxy;
      simp;
      apply dia_def.mpr;
      use u;
      constructor;
      . exact Rxu;
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

protected lemma nec (h : C ⊧ φ) : C ⊧ □φ := by
  intro _ hF;
  apply Kripke.ValidOnFrame.nec;
  exact h hF;

protected lemma mdp (hpq : C ⊧ φ ➝ ψ) (hp : C ⊧ φ) : C ⊧ ψ := by
  intro _ hF;
  exact Kripke.ValidOnFrame.mdp (hpq hF) (hp hF)

end ValidOnFrameClass

end Formula.Kripke


namespace Kripke

def Frame.theorems (F : Kripke.Frame) : Theory ℕ := { φ | F ⊧ φ }

def FrameClass.DefinedBy (C : Kripke.FrameClass) (T : Theory ℕ) := ∀ F, F ∈ C ↔ F ⊧* T

section definability

variable {F : Kripke.Frame}

instance AllFrameClass.isDefinedBy : AllFrameClass.DefinedBy 𝗞 := by
  intro φ;
  simp [Frame.theorems];
  rintro _ φ ψ rfl;
  exact Formula.Kripke.ValidOnFrame.axiomK;

end definability

end Kripke


namespace Hilbert

open Kripke

namespace Kripke

variable {H : Hilbert ℕ} {φ : Formula ℕ}
variable {C : FrameClass} {T : Theory ℕ}

open Formula.Kripke

lemma sound_hilbert_of_frameclass (definedBy : C.DefinedBy T) : (Hilbert.ExtK T : Hilbert ℕ) ⊢! φ → C ⊧ φ := by
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

lemma sound_of_equiv_frameclass_hilbert (definedBy : C.DefinedBy T) (heq : H =ₛ (Hilbert.ExtK T)) : H ⊢! φ → C ⊧ φ := by
  intro hφ;
  apply sound_hilbert_of_frameclass (T := T) (definedBy);
  exact Equiv.iff.mp heq φ |>.mp hφ;

lemma instSound (definedBy : C.DefinedBy T) (heq : H =ₛ (Hilbert.ExtK T)) : Sound H C := ⟨sound_of_equiv_frameclass_hilbert definedBy heq⟩

lemma unprovable_bot [sound : Sound H C] (hNonempty : C.Nonempty) : H ⊬ ⊥ := by
  apply not_imp_not.mpr sound.sound;
  simp [Semantics.Realize];
  obtain ⟨F, hF⟩ := hNonempty;
  use F;
  constructor;
  . exact hF;
  . exact Semantics.Bot.realize_bot (F := Formula ℕ) (M := Kripke.Frame) F;

lemma instConsistent [Sound H C] (h_nonempty : C.Nonempty) : H.Consistent := System.Consistent.of_unprovable $ unprovable_bot h_nonempty

end Kripke


namespace K

instance Kripke.sound : Sound (Hilbert.K ℕ) (AllFrameClass) := Kripke.instSound (definedBy := Kripke.AllFrameClass.isDefinedBy) (heq := by simp [ExtK.K_is_extK_of_AxiomK])

instance consistent : System.Consistent (Hilbert.K ℕ) := Kripke.instConsistent (C := AllFrameClass) $ by
  use reflexivePointFrame;
  tauto;

end K


section

open Formula (atom)
open Formula.Kripke

lemma K_strictlyWeakerThan_KD : (Hilbert.K ℕ) <ₛ (Hilbert.KD ℕ) := by
  constructor;
  . apply K_weakerThan_KD;
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
  . apply K_weakerThan_KB;
  . simp [weakerThan_iff];
    use ((atom 0) ➝ □◇(atom 0));
    constructor;
    . exact axiomB!;
    . apply K.Kripke.sound.not_provable_of_countermodel;
      simp [ValidOnModel, ValidOnFrame, Satisfies];
      use ⟨Fin 2, λ x y => x = 0 ∧ y = 1⟩, (λ w _ => w = 0), 0;
      simp [Semantics.Realize, Satisfies];
      use 1;

theorem K_strictlyWeakerThan_K4 : (Hilbert.K ℕ) <ₛ (Hilbert.K4 ℕ) := by
  constructor;
  . apply K_weakerThan_K4;
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
  . apply K_weakerThan_K5;
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


/-
namespace Kripke

open Formula.Kripke (ValidOnFrame ValidOnModel Satisfies)

variable {C : Kripke.FrameClass} {F : Kripke.Frame}
         {φ ψ : Formula ℕ}

protected lemma axiomK : C ⊧* 𝗞 := by
  simp only [Semantics.RealizeSet.setOf_iff];
  rintro f ⟨φ, ψ, _⟩ F _;
  apply (Semantics.RealizeSet.setOf_iff.mp $ ValidOnFrame.axiomK_set) f;
  use φ, ψ;

protected lemma nec (h : C ⊧ φ) : C ⊧ □φ := by
  intro _ hF;
  apply ValidOnFrame.nec;
  exact h hF;

protected lemma mdp (hpq : C ⊧ φ ➝ ψ) (hp : C ⊧ φ) : C ⊧ ψ := by
  intro _ hF;
  exact Formula.Kripke.ValidOnFrame.mdp (hpq hF) (hp hF)

lemma iff_not_validOnFrameClass : ¬(C ⊧ φ) ↔ ∃ F ∈ C, ∃ V x, ¬Satisfies ⟨F, V⟩ x φ := by
  simp [ValidOnFrame, ValidOnModel, Satisfies];
  tauto;

lemma iff_not_set_validOnFrameClass : ¬(C ⊧* T) ↔ ∃ φ ∈ T, ∃ F ∈ C, ∃ V x, ¬Satisfies ⟨F, V⟩ x φ := by
  simp [Semantics.realizeSet_iff, ValidOnFrame, ValidOnModel, Satisfies];
  tauto;

lemma iff_not_validOnFrame : ¬(F ⊧* T) ↔ ∃ φ ∈ T, ∃ V x, ¬Satisfies ⟨F, V⟩ x φ := by
  simp [Semantics.realizeSet_iff, ValidOnFrame, ValidOnModel, Satisfies];
  tauto;



abbrev FrameClassOfTheory (T : Theory ℕ) : FrameClass := { F | F ⊧* T }
notation "𝔽(" T ")"  => FrameClassOfTheory T

abbrev FiniteFrameClassOfTheory (T : Theory ℕ) : FiniteFrameClass := { FF | FF.toFrame ⊧* T }
notation "𝔽ꟳ(" T ")"  => FiniteFrameClassOfTheory T

def definability_union_frameclass_of_theory {T₁ T₂ : Theory ℕ}
  (defi₁ : 𝔽(T₁).DefinedBy 𝔽₁) (defi₂ : 𝔽(T₂).DefinedBy 𝔽₂) (nonempty : (𝔽₁ ∩ 𝔽₂).Nonempty)
  : 𝔽(T₁ ∪ T₂).DefinedBy (𝔽₁ ∩ 𝔽₂) where
  define := by
    simp;
    intro F;
    constructor;
    . rintro ⟨hF₁, hF₂⟩;
      constructor;
      . simpa using defi₁.define.mp hF₁;
      . simpa using defi₂.define.mp hF₂;
    . rintro ⟨hF₁, hF₂⟩;
      constructor;
      . exact defi₁.define.mpr hF₁;
      . exact defi₂.define.mpr hF₂;
  nonempty := nonempty

def characterizability_union_frameclass_of_theory {T₁ T₂ : Theory ℕ}
  (char₁ : 𝔽(T₁).Characteraizable 𝔽₁) (char₂ : 𝔽(T₂).Characteraizable 𝔽₂)
  (nonempty : (𝔽₁ ∩ 𝔽₂).Nonempty)
  : 𝔽(T₁ ∪ T₂).Characteraizable (𝔽₁ ∩ 𝔽₂) where
  characterize := by
    simp;
    intro F hF₁ hF₂;
    constructor;
    . simpa using char₁.characterize hF₁;
    . simpa using char₂.characterize hF₂;
  nonempty := nonempty

abbrev FrameClassOfHilbert (H : Hilbert ℕ) : FrameClass.Dep ℕ := 𝔽(H.theorems)
notation "𝔽(" H ")"  => FrameClassOfHilbert H

open Hilbert.Deduction

instance {Ax : Theory ℕ} {𝔽 : FrameClass} [defi : 𝔽(Ax).DefinedBy 𝔽] : 𝔽(Hilbert.ExtK Ax).DefinedBy 𝔽 where
  define := by
    simp only [Hilbert.theorems, System.theory, Semantics.RealizeSet.setOf_iff, ValidOnFrame.models_iff, Set.mem_setOf_eq];
    intro F;
    constructor;
    . intro h;
      apply defi.define.mp;
      constructor;
      intro φ hp;
      exact h φ $ maxm! $ by right; exact hp;
    . intro hF φ hp;
      induction hp using inducition_with_necOnly! with
      | hMaxm h =>
        simp at h;
        rcases h with (⟨_, _, rfl⟩ | hR);
        . simp_all [ValidOnFrame, ValidOnModel, Satisfies];
        . have := defi.define.mpr hF
          simp at this;
          exact this.RealizeSet hR;
      | hMdp ihpq ihp => exact Formula.Kripke.ValidOnFrame.mdp ihpq ihp;
      | hNec ih => exact Formula.Kripke.ValidOnFrame.nec ih;
      | _ => first
        | exact Formula.Kripke.ValidOnFrame.imply₁;
        | exact Formula.Kripke.ValidOnFrame.imply₂;
        | exact Formula.Kripke.ValidOnFrame.elimContra;
  nonempty := defi.nonempty

instance {Ax : Theory ℕ} {𝔽 : FrameClass} [char : 𝔽(Ax).Characteraizable 𝔽] : 𝔽(Hilbert.ExtK Ax).Characteraizable 𝔽 where
  characterize := by
    simp only [Hilbert.theorems, System.theory, Semantics.RealizeSet.setOf_iff, ValidOnFrame.models_iff, Set.mem_setOf_eq];
    intro F hF φ hp;
    induction hp using inducition_with_necOnly! with
    | hMaxm h =>
      simp at h;
      rcases h with (⟨_, _, rfl⟩ | hR);
      . simp_all [ValidOnFrame, ValidOnModel, Satisfies];
      . have := char.characterize hF
        simp at this;
        exact this.RealizeSet hR;
    | hMdp ihpq ihp => exact Formula.Kripke.ValidOnFrame.mdp ihpq ihp;
    | hNec ih => exact Formula.Kripke.ValidOnFrame.nec ih;
    | _ => first
      | exact Formula.Kripke.ValidOnFrame.imply₁;
      | exact Formula.Kripke.ValidOnFrame.imply₂;
      | exact Formula.Kripke.ValidOnFrame.elimContra;
  nonempty := char.nonempty


abbrev FiniteFrameClassOfHilbert (H : Hilbert ℕ) : FiniteFrameClass.Dep ℕ := 𝔽(H)ꟳ
notation "𝔽ꟳ(" H ")"  => FiniteFrameClassOfHilbert H

instance {Ax : Set (Formula ℕ)} {𝔽 : FiniteFrameClass}  [defi : 𝔽ꟳ(Ax).DefinedBy 𝔽] : 𝔽ꟳ(Hilbert.ExtK Ax).DefinedBy 𝔽 where
  define := by
    simp only [Hilbert.theorems, System.theory, Semantics.RealizeSet.setOf_iff, ValidOnFrame.models_iff, Set.mem_setOf_eq];
    intro F;
    constructor;
    . intro h;
      apply defi.define.mp;
      constructor;
      intro φ hp;
      exact h φ $ maxm! $ by right; exact hp;
    . intro hF φ hp;
      induction hp using inducition_with_necOnly! with
      | hMaxm h =>
        simp at h;
        rcases h with (⟨_, _, rfl⟩ | hR);
        . simp_all [ValidOnFrame, ValidOnModel, Satisfies];
        . have := defi.define.mpr hF
          simp at this;
          exact this.RealizeSet hR;
      | hMdp ihpq ihp => exact Formula.Kripke.ValidOnFrame.mdp ihpq ihp;
      | hNec ih => exact Formula.Kripke.ValidOnFrame.nec ih;
      | _ => first
        | exact Formula.Kripke.ValidOnFrame.imply₁;
        | exact Formula.Kripke.ValidOnFrame.imply₂;
        | exact Formula.Kripke.ValidOnFrame.elimContra;
  nonempty := defi.nonempty

instance {Ax : Set (Formula ℕ)} {𝔽 : FiniteFrameClass} [char : 𝔽ꟳ(Ax).Characteraizable 𝔽] : 𝔽ꟳ(Hilbert.ExtK Ax).Characteraizable 𝔽 where
  characterize := by
    simp only [Hilbert.theorems, System.theory, Semantics.RealizeSet.setOf_iff, ValidOnFrame.models_iff, Set.mem_setOf_eq];
    intro F hF φ hp;
    induction hp using inducition_with_necOnly! with
    | hMaxm h =>
      simp at h;
      rcases h with (⟨_, _, rfl⟩ | hR);
      . simp_all [ValidOnFrame, ValidOnModel, Satisfies];
      . have := char.characterize hF
        simp at this;
        exact this.RealizeSet hR;
    | hMdp ihpq ihp => exact Formula.Kripke.ValidOnFrame.mdp ihpq ihp;
    | hNec ih => exact Formula.Kripke.ValidOnFrame.nec ih;
    | _ => first
      | exact Formula.Kripke.ValidOnFrame.imply₁;
      | exact Formula.Kripke.ValidOnFrame.imply₂;
      | exact Formula.Kripke.ValidOnFrame.elimContra;
  nonempty := char.nonempty

section sound

variable {ℕ : Type u}
variable {H : Hilbert ℕ} {φ : Formula ℕ}

lemma sound : H ⊢! φ → 𝔽(H) ⊧ φ := by
  intro hp F hF;
  simp [Hilbert.theorems, System.theory] at hF;
  exact hF φ hp;
instance : Sound H 𝔽(H) := ⟨sound⟩

lemma sound_finite : H ⊢! φ → 𝔽ꟳ(H) ⊧ φ := by
  intro hp F hF;
  simp [Hilbert.theorems, System.theory] at hF;
  obtain ⟨FF, hFF₁, rfl⟩ := hF;
  exact hFF₁ φ hp;
instance : Sound H 𝔽ꟳ(H) := ⟨sound_finite⟩

lemma unprovable_bot (hc : 𝔽(H).Nonempty) : H ⊬ ⊥ := by
  apply (not_imp_not.mpr (sound (ℕ := ℕ)));
  simp [Semantics.Realize];
  obtain ⟨F, hF⟩ := hc;
  use F;
  constructor;
  . exact hF;
  . exact Semantics.Bot.realize_bot (F := Formula ℕ) (M := Kripke.Frame) F;
instance (hc : 𝔽(H).Nonempty) : System.Consistent H := System.Consistent.of_unprovable $ unprovable_bot hc

lemma unprovable_bot_finite (hc : 𝔽ꟳ(H).Nonempty) : H ⊬ ⊥ := by
  apply (not_imp_not.mpr (sound_finite (ℕ := ℕ)));
  simp [Semantics.Realize];
  obtain ⟨F, hF⟩ := hc;
  use F;
  constructor;
  . exact hF;
  . exact Semantics.Bot.realize_bot (F := Formula ℕ) (M := Kripke.Frame) F;
instance (hc : 𝔽ꟳ(H).Nonempty) : System.Consistent H := System.Consistent.of_unprovable $ unprovable_bot_finite hc

lemma sound_of_characterizability {𝔽 : FrameClass} [char : 𝔽(H).Characteraizable 𝔽]
  : H ⊢! φ → 𝔽 ⊧ φ := by
  intro h F hF;
  apply sound h;
  apply char.characterize hF;
instance {𝔽 : FrameClass} [𝔽(H).Characteraizable 𝔽] : Sound H 𝔽 := ⟨sound_of_characterizability⟩

lemma sound_of_finite_characterizability {𝔽 : FiniteFrameClass} [char : 𝔽ꟳ(H).Characteraizable 𝔽]
  : H ⊢! φ → 𝔽 ⊧ φ := by
  intro h F hF;
  apply sound_finite h;
  obtain ⟨FF, hFF, rfl⟩ := hF;
  use FF;
  constructor;
  . exact char.characterize hFF;
  . rfl;
instance {𝔽 : FiniteFrameClass} [𝔽ꟳ(H).Characteraizable 𝔽] : Sound H 𝔽 := ⟨sound_of_finite_characterizability⟩

lemma unprovable_bot_of_characterizability {𝔽 : FrameClass} [char : 𝔽(H).Characteraizable 𝔽] : H ⊬ ⊥ := by
  apply unprovable_bot;
  obtain ⟨F, hF⟩ := char.nonempty;
  use F;
  apply char.characterize hF;
instance [FrameClass.Characteraizable.{u} 𝔽(H) 𝔽] : System.Consistent H
  := System.Consistent.of_unprovable $ unprovable_bot_of_characterizability

lemma unprovable_bot_of_finite_characterizability {𝔽 : FiniteFrameClass}  [char : 𝔽ꟳ(H).Characteraizable 𝔽] : H ⊬ ⊥ := by
  apply unprovable_bot_finite;
  obtain ⟨F, hF⟩ := char.nonempty;
  use F;
  apply char.characterize hF;
instance {𝔽 : FiniteFrameClass} [FiniteFrameClass.Characteraizable.{u} 𝔽ꟳ(H) 𝔽] : System.Consistent H
  := System.Consistent.of_unprovable $ unprovable_bot_of_finite_characterizability

end sound

instance empty_axiom_definability : 𝔽((∅ : Theory ℕ)).DefinedBy AllFrameClass where
  define := by simp;
  nonempty :=  ⟨⟨PUnit,  λ _ _ => True⟩, trivial⟩

private instance K_definability' : 𝔽(((Hilbert.ExtK ∅) : Hilbert ℕ)).DefinedBy AllFrameClass := inferInstance

instance K_definability : 𝔽(Hilbert.K ℕ).DefinedBy AllFrameClass := by
  convert K_definability';
  exact Hilbert.ExtK.K_is_extK_of_empty;

instance K_sound : Sound (Hilbert.K ℕ) (AllFrameClass) := inferInstance

instance K_consistent : System.Consistent (Hilbert.K ℕ) := inferInstance


lemma restrict_finite : C ⊧ φ → Cꟳ ⊧ φ := by
  intro h F hF;
  obtain ⟨FF, hFF₁, rfl⟩ := hF;
  exact h (by simpa)

instance {H : Hilbert ℕ} [sound : Sound H C] : Sound H Cꟳ := ⟨by
  intro φ h;
  exact restrict_finite $ sound.sound h;
⟩

instance : Sound (Hilbert.K ℕ) (AllFrameClassꟳ) := inferInstance

lemma exists_finite_frame : ¬Cꟳ ⊧ φ ↔ ∃ F ∈ 𝔽ꟳ, ¬F ⊧ φ := by simp;

class FiniteFrameProperty (H : Hilbert ℕ) (𝔽 : FrameClass) where
  [complete : Complete H 𝔽ꟳ]
  [sound : Sound H 𝔽ꟳ]

end Kripke



namespace Hilbert

section

open Formula (atom)
open Formula.Kripke
open Kripke (K_sound)

theorem K_strictlyWeakerThan_KD [DecidableEq ℕ] [Inhabited ℕ] : (Hilbert.K ℕ) <ₛ (Hilbert.KD ℕ) := by
  constructor;
  . apply K_weakerThan_KD;
  . simp [weakerThan_iff];
    use (□(atom default) ➝ ◇(atom default));
    constructor;
    . exact Deduction.maxm! (by simp);
    . apply K_sound.not_provable_of_countermodel;
      simp [ValidOnFrame, ValidOnModel];
      use ⟨Fin 1, λ _ _ => False⟩, (λ w _ => w = 0), 0;
      simp [Satisfies];

theorem K_strictlyWeakerThan_KB [DecidableEq ℕ] [Inhabited ℕ] : (Hilbert.K ℕ) <ₛ (Hilbert.KB ℕ) := by
  constructor;
  . apply K_weakerThan_KB;
  . simp [weakerThan_iff];
    use ((atom default) ➝ □◇(atom default));
    constructor;
    . exact Deduction.maxm! (by simp);
    . apply K_sound.not_provable_of_countermodel;
      simp [ValidOnFrame, ValidOnModel];
      use ⟨Fin 2, λ x y => x = 0 ∧ y = 1⟩, (λ w _ => w = 0), 0;
      simp [Satisfies];
      use 1;

theorem K_strictlyWeakerThan_K4 [DecidableEq ℕ] [Inhabited ℕ] : (Hilbert.K ℕ) <ₛ (Hilbert.K4 ℕ) := by
  constructor;
  . apply K_weakerThan_K4;
  . simp [weakerThan_iff];
    use (□(atom default) ➝ □□(atom default));
    constructor;
    . exact Deduction.maxm! (by simp);
    . apply K_sound.not_provable_of_countermodel;
      simp [ValidOnFrame, ValidOnModel];
      use ⟨Fin 2, λ x y => x ≠ y⟩, (λ w _ => w = 1), 0;
      simp [Satisfies];
      constructor;
      . intro y;
        match y with
        | 0 => aesop;
        | 1 => simp;
      . use 1;
        constructor;
        . aesop;
        . use 0; aesop;

theorem K_strictlyWeakerThan_K5 [DecidableEq ℕ] [Inhabited ℕ] : (Hilbert.K ℕ) <ₛ (Hilbert.K5 ℕ)  := by
  constructor;
  . apply K_weakerThan_K5;
  . simp [weakerThan_iff];
    use (◇(atom default) ➝ □◇(atom default));
    constructor;
    . exact Deduction.maxm! (by simp);
    . apply K_sound.not_provable_of_countermodel;
      simp [ValidOnFrame, ValidOnModel];
      use ⟨Fin 2, λ x _ => x = 0⟩, (λ w _ => w = 0), 0;
      simp [Satisfies];
      use 1;
      simp;

end


section

variable {Ax₁ Ax₂ : Theory ℕ} (𝔽₁ 𝔽₂ : FrameClass)

lemma weakerThan_of_subset_FrameClass
  [sound₁ : Sound (Hilbert.ExtK Ax₁) 𝔽₁] [complete₂ : Complete (Hilbert.ExtK Ax₂) 𝔽₂]
  (h𝔽 : 𝔽₂ ⊆ 𝔽₁)
  : (Hilbert.ExtK Ax₁) ≤ₛ (Hilbert.ExtK Ax₂) := by
  apply System.weakerThan_iff.mpr;
  intro φ hp;
  apply complete₂.complete;
  intro F hF;
  exact sound₁.sound hp $ h𝔽 hF;

lemma equiv_of_eq_FrameClass
  [sound₁ : Sound (Hilbert.ExtK Ax₁) 𝔽₁] [sound₂ : Sound (Hilbert.ExtK Ax₂) 𝔽₂]
  [complete₁ : Complete (Hilbert.ExtK Ax₁) 𝔽₁] [complete₂ : Complete (Hilbert.ExtK Ax₂) 𝔽₂]
  (h𝔽 : 𝔽₁ = 𝔽₂) : (Hilbert.ExtK Ax₁) =ₛ (Hilbert.ExtK Ax₂) := by
  apply System.Equiv.antisymm_iff.mpr;
  constructor;
  . apply weakerThan_of_subset_FrameClass 𝔽₁ 𝔽₂; subst_vars; rfl;
  . apply weakerThan_of_subset_FrameClass 𝔽₂ 𝔽₁; subst_vars; rfl;

end

end Hilbert
-/

end LO.Modal
