import Foundation.Logic.Kripke.Basic
import Foundation.Logic.System
import Foundation.Modal.Formula
import Foundation.Modal.Hilbert

namespace LO.Modal

open System
open Kripke

namespace Formula.Kripke

def Satisfies (M : Kripke.Model α) (x : M.World) : Formula α → Prop
  | atom a  => M.Valuation x a
  | ⊥  => False
  | φ ➝ ψ => (Satisfies M x φ) ➝ (Satisfies M x ψ)
  | □φ   => ∀ y, x ≺ y → (Satisfies M y φ)

namespace Satisfies

protected instance semantics {M : Kripke.Model α} : Semantics (Formula α) (M.World) := ⟨fun x ↦ Formula.Kripke.Satisfies M x⟩

variable {M : Kripke.Model α} {x : M.World} {φ ψ : Formula α}

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

lemma trans (hpq : x ⊧ φ ➝ ψ) (hqr : x ⊧ ψ ➝ r) : x ⊧ φ ➝ r := by simp_all;

lemma mdp (hpq : x ⊧ φ ➝ ψ) (hp : x ⊧ φ) : x ⊧ ψ := by simp_all;

lemma dia_dual : x ⊧ ◇φ ↔ x ⊧ ∼□(∼φ) := by simp [Satisfies];

lemma box_dual : x ⊧ □φ ↔ x ⊧ ∼◇(∼φ) := by simp [Satisfies];

lemma not_imp : ¬(x ⊧ φ ➝ ψ) ↔ x ⊧ φ ⋏ ∼ψ := by simp [Satisfies];

end Satisfies


def ValidOnModel (M : Kripke.Model α) (φ : Formula α) := ∀ x : M.World, x ⊧ φ

namespace ValidOnModel

instance semantics : Semantics (Formula α) (Kripke.Model α) := ⟨fun M ↦ Formula.Kripke.ValidOnModel M⟩

@[simp] protected lemma iff_models {M : Kripke.Model α} : M ⊧ f ↔ Kripke.ValidOnModel M f := iff_of_eq rfl

instance : Semantics.Bot (Kripke.Model α) where
  realize_bot M := by simp [Kripke.ValidOnModel, Kripke.Satisfies];

variable {M : Model α} {φ ψ r : Formula α}

protected lemma mdp (hpq : M ⊧ φ ➝ ψ) (hp : M ⊧ φ) : M ⊧ ψ := by
  intro x;
  exact (Satisfies.imp_def.mp $ hpq x) (hp x);

protected lemma nec (h : M ⊧ φ) : M ⊧ □φ := by
  intro x y _;
  exact h y;

protected lemma verum : M ⊧ ⊤ := by intro; tauto;

protected lemma imply₁ : M ⊧ (Axioms.Imply₁ φ ψ) := by simp [ValidOnModel]; tauto;

protected lemma imply₂ : M ⊧ (Axioms.Imply₂ φ ψ r) := by simp [ValidOnModel]; tauto;

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


def ValidOnFrame (F : Frame) (φ : Formula α) := ∀ V, (⟨F, V⟩ : Kripke.Model α) ⊧ φ

namespace ValidOnFrame

instance semantics : Semantics (Formula α) (Frame.Dep α) := ⟨fun F ↦ Formula.Kripke.ValidOnFrame F⟩

variable {F : Frame.Dep α}

@[simp] protected lemma models_iff : F ⊧ φ ↔ Kripke.ValidOnFrame F φ := iff_of_eq rfl

instance : Semantics.Bot (Frame.Dep α) where
  realize_bot _ := by simp [Kripke.ValidOnFrame];

protected lemma nec (h : F ⊧ φ) : F ⊧ □φ := by
  intro V x y _;
  exact h V y;

protected lemma mdp (hpq : F ⊧ φ ➝ ψ) (hp : F ⊧ φ) : F ⊧ ψ := by
  intro V x;
  exact (hpq V x) (hp V x);

protected lemma verum : F ⊧ ⊤ := by intros _; tauto;

protected lemma imply₁ : F ⊧ (Axioms.Imply₁ φ ψ) := by intro V; exact ValidOnModel.imply₁ (M := ⟨F, V⟩);

protected lemma imply₂ : F ⊧ (Axioms.Imply₂ φ ψ r) := by intro V; exact ValidOnModel.imply₂ (M := ⟨F, V⟩);

protected lemma elimContra : F ⊧ (Axioms.ElimContra φ ψ) := by intro V; exact ValidOnModel.elimContra (M := ⟨F, V⟩);

protected lemma axiomK : F ⊧ (Axioms.K φ ψ) := by intro V; exact ValidOnModel.axiomK (M := ⟨F, V⟩);

protected lemma axiomK_set : F ⊧* 𝗞 := by
  simp [Semantics.realizeSet_iff];
  rintro f x y rfl;
  exact ValidOnFrame.axiomK;

end ValidOnFrame



@[simp] def ValidOnFrameClass (𝔽 : FrameClass) (φ : Formula α) := ∀ {F : Frame}, F ∈ 𝔽 → F#α ⊧ φ

namespace ValidOnFrameClass

protected instance semantics : Semantics (Formula α) (FrameClass.Dep α) := ⟨fun 𝔽 ↦ Kripke.ValidOnFrameClass 𝔽⟩

variable {𝔽 : FrameClass.Dep α}

@[simp] protected lemma models_iff : 𝔽 ⊧ φ ↔ Formula.Kripke.ValidOnFrameClass 𝔽 φ := iff_of_eq rfl

protected lemma nec (h : 𝔽 ⊧ φ) : 𝔽 ⊧ □φ := by
  intro _ hF;
  apply Kripke.ValidOnFrame.nec;
  exact h hF;

protected lemma mdp (hpq : 𝔽 ⊧ φ ➝ ψ) (hp : 𝔽 ⊧ φ) : 𝔽 ⊧ ψ := by
  intro _ hF;
  exact Kripke.ValidOnFrame.mdp (hpq hF) (hp hF)

end ValidOnFrameClass


abbrev ValidOnFiniteFrameClass (𝔽 : FiniteFrameClass) (φ : Formula α) := 𝔽.toFrameClass#α ⊧ φ

namespace ValidOnFiniteFrameClass

protected instance semantics : Semantics (Formula α) (FiniteFrameClass.Dep α) := ⟨fun 𝔽 ↦ Kripke.ValidOnFiniteFrameClass 𝔽⟩

variable {𝔽 : FiniteFrameClass.Dep α}

@[simp] protected lemma models_iff : 𝔽 ⊧ φ ↔ Kripke.ValidOnFiniteFrameClass 𝔽 φ := iff_of_eq rfl

end ValidOnFiniteFrameClass


end Formula.Kripke


namespace Kripke

open Formula.Kripke (ValidOnFrame ValidOnModel Satisfies)

variable {𝔽 : Kripke.FrameClass} {F : Kripke.Frame}
         {φ ψ : Formula α}

protected lemma axiomK : 𝔽#α ⊧* 𝗞 := by
  simp only [Semantics.RealizeSet.setOf_iff];
  rintro f ⟨φ, ψ, _⟩ F _;
  apply (Semantics.RealizeSet.setOf_iff.mp $ ValidOnFrame.axiomK_set) f;
  use φ, ψ;

protected lemma nec (h : 𝔽#α ⊧ φ) : 𝔽#α ⊧ □φ := by
  intro _ hF;
  apply ValidOnFrame.nec;
  exact h hF;

protected lemma mdp (hpq : 𝔽#α ⊧ φ ➝ ψ) (hp : 𝔽#α ⊧ φ) : 𝔽#α ⊧ ψ := by
  intro _ hF;
  exact Formula.Kripke.ValidOnFrame.mdp (hpq hF) (hp hF)

lemma iff_not_validOnFrameClass : ¬(𝔽#α ⊧ φ) ↔ ∃ F ∈ 𝔽, ∃ V x, ¬Satisfies ⟨F, V⟩ x φ := by
  simp [ValidOnFrame, ValidOnModel, Satisfies];

lemma iff_not_set_validOnFrameClass : ¬(𝔽#α ⊧* T) ↔ ∃ φ ∈ T, ∃ F ∈ 𝔽, ∃ V x, ¬Satisfies ⟨F, V⟩ x φ  := by
  simp [Semantics.realizeSet_iff, ValidOnFrame, ValidOnModel, Satisfies];

lemma iff_not_validOnFrame : ¬(F#α ⊧* T) ↔ ∃ φ ∈ T, ∃ V x, ¬Satisfies ⟨F, V⟩ x φ := by
  simp [Semantics.realizeSet_iff, ValidOnFrame, ValidOnModel, Satisfies];



abbrev FrameClassOfTheory (T : Theory α) : FrameClass := { F | F#α ⊧* T }
notation "𝔽(" T ")"  => FrameClassOfTheory T

abbrev FiniteFrameClassOfTheory (T : Theory α) : FiniteFrameClass := { FF | FF.toFrame#α ⊧* T }
notation "𝔽ꟳ(" T ")"  => FiniteFrameClassOfTheory T

def definability_union_frameclass_of_theory {T₁ T₂ : Theory α}
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

def characterizability_union_frameclass_of_theory {T₁ T₂ : Theory α}
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

abbrev FrameClassOfHilbert (Λ : Hilbert α) : FrameClass.Dep α := 𝔽(Λ.theorems)
notation "𝔽(" Λ ")"  => FrameClassOfHilbert Λ

instance {Ax : Theory α} {𝔽 : FrameClass} [defi : 𝔽(Ax).DefinedBy 𝔽] : 𝔽(𝜿(Ax)).DefinedBy 𝔽 where
  define := by
    simp only [Hilbert.theorems, System.theory, Semantics.RealizeSet.setOf_iff, ValidOnFrame.models_iff, Set.mem_setOf_eq];
    intro F;
    constructor;
    . intro h;
      apply defi.define.mp;
      constructor;
      intro φ hp;
      exact h φ $ Deduction.maxm! $ by right; exact hp;
    . intro hF φ hp;
      induction hp using Deduction.inducition_with_necOnly! with
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

instance {Ax : Theory α} {𝔽 : FrameClass} [char : 𝔽(Ax).Characteraizable 𝔽] : 𝔽(𝜿(Ax)).Characteraizable 𝔽 where
  characterize := by
    simp only [Hilbert.theorems, System.theory, Semantics.RealizeSet.setOf_iff, ValidOnFrame.models_iff, Set.mem_setOf_eq];
    intro F hF φ hp;
    induction hp using Deduction.inducition_with_necOnly! with
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


abbrev FiniteFrameClassOfHilbert (Λ : Hilbert α) : FiniteFrameClass.Dep α := 𝔽(Λ)ꟳ
notation "𝔽ꟳ(" Λ ")"  => FiniteFrameClassOfHilbert Λ

instance {Ax : Set (Formula α)} {𝔽 : FiniteFrameClass}  [defi : 𝔽ꟳ(Ax).DefinedBy 𝔽] : 𝔽ꟳ(𝜿(Ax)).DefinedBy 𝔽 where
  define := by
    simp only [Hilbert.theorems, System.theory, Semantics.RealizeSet.setOf_iff, ValidOnFrame.models_iff, Set.mem_setOf_eq];
    intro F;
    constructor;
    . intro h;
      apply defi.define.mp;
      constructor;
      intro φ hp;
      exact h φ $ Deduction.maxm! $ by right; exact hp;
    . intro hF φ hp;
      induction hp using Deduction.inducition_with_necOnly! with
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

instance {Ax : Set (Formula α)} {𝔽 : FiniteFrameClass} [char : 𝔽ꟳ(Ax).Characteraizable 𝔽] : 𝔽ꟳ(𝜿(Ax)).Characteraizable 𝔽 where
  characterize := by
    simp only [Hilbert.theorems, System.theory, Semantics.RealizeSet.setOf_iff, ValidOnFrame.models_iff, Set.mem_setOf_eq];
    intro F hF φ hp;
    induction hp using Deduction.inducition_with_necOnly! with
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

variable {α : Type u}
variable {Λ : Hilbert α} {φ : Formula α}

lemma sound : Λ ⊢! φ → 𝔽(Λ) ⊧ φ := by
  intro hp F hF;
  simp [Hilbert.theorems, System.theory] at hF;
  exact hF φ hp;
instance : Sound Λ 𝔽(Λ) := ⟨sound⟩

lemma sound_finite : Λ ⊢! φ → 𝔽ꟳ(Λ) ⊧ φ := by
  intro hp F hF;
  simp [Hilbert.theorems, System.theory] at hF;
  obtain ⟨FF, hFF₁, rfl⟩ := hF;
  exact hFF₁ φ hp;
instance : Sound Λ 𝔽ꟳ(Λ) := ⟨sound_finite⟩

lemma unprovable_bot (hc : 𝔽(Λ).Nonempty) : Λ ⊬ ⊥ := by
  apply (not_imp_not.mpr (sound (α := α)));
  simp [Semantics.Realize];
  obtain ⟨F, hF⟩ := hc;
  use F;
  constructor;
  . exact hF;
  . exact Semantics.Bot.realize_bot (F := Formula α) (M := Frame.Dep α) F;
instance (hc : 𝔽(Λ).Nonempty) : System.Consistent Λ := System.Consistent.of_unprovable $ unprovable_bot hc

lemma unprovable_bot_finite (hc : 𝔽ꟳ(Λ).Nonempty) : Λ ⊬ ⊥ := by
  apply (not_imp_not.mpr (sound_finite (α := α)));
  simp [Semantics.Realize];
  obtain ⟨F, hF⟩ := hc;
  use F;
  constructor;
  . exact hF;
  . exact Semantics.Bot.realize_bot (F := Formula α) (M := Frame.Dep α) F;
instance (hc : 𝔽ꟳ(Λ).Nonempty) : System.Consistent Λ := System.Consistent.of_unprovable $ unprovable_bot_finite hc

lemma sound_of_characterizability {𝔽 : FrameClass} [char : 𝔽(Λ).Characteraizable 𝔽]
  : Λ ⊢! φ → 𝔽#α ⊧ φ := by
  intro h F hF;
  apply sound h;
  apply char.characterize hF;
instance {𝔽 : FrameClass} [𝔽(Λ).Characteraizable 𝔽] : Sound Λ 𝔽#α := ⟨sound_of_characterizability⟩

lemma sound_of_finite_characterizability {𝔽 : FiniteFrameClass} [char : 𝔽ꟳ(Λ).Characteraizable 𝔽]
  : Λ ⊢! φ → 𝔽#α ⊧ φ := by
  intro h F hF;
  apply sound_finite h;
  obtain ⟨FF, hFF, rfl⟩ := hF;
  use FF;
  constructor;
  . exact char.characterize hFF;
  . rfl;
instance {𝔽 : FiniteFrameClass} [𝔽ꟳ(Λ).Characteraizable 𝔽] : Sound Λ 𝔽#α := ⟨sound_of_finite_characterizability⟩

lemma unprovable_bot_of_characterizability {𝔽 : FrameClass} [char : 𝔽(Λ).Characteraizable 𝔽] : Λ ⊬ ⊥ := by
  apply unprovable_bot;
  obtain ⟨F, hF⟩ := char.nonempty;
  use F;
  apply char.characterize hF;
instance [FrameClass.Characteraizable.{u} 𝔽(Λ) 𝔽] : System.Consistent Λ
  := System.Consistent.of_unprovable $ unprovable_bot_of_characterizability

lemma unprovable_bot_of_finite_characterizability {𝔽 : FiniteFrameClass}  [char : 𝔽ꟳ(Λ).Characteraizable 𝔽] : Λ ⊬ ⊥ := by
  apply unprovable_bot_finite;
  obtain ⟨F, hF⟩ := char.nonempty;
  use F;
  apply char.characterize hF;
instance {𝔽 : FiniteFrameClass} [FiniteFrameClass.Characteraizable.{u} 𝔽ꟳ(Λ) 𝔽] : System.Consistent Λ
  := System.Consistent.of_unprovable $ unprovable_bot_of_finite_characterizability

end sound

instance empty_axiom_definability : 𝔽((∅ : Theory α)).DefinedBy AllFrameClass where
  define := by simp;
  nonempty :=  ⟨⟨PUnit,  λ _ _ => True⟩, trivial⟩

private instance K_definability' : 𝔽((𝜿(∅) : Hilbert α)).DefinedBy AllFrameClass := inferInstance

instance K_definability : 𝔽((𝐊 : Hilbert α)).DefinedBy AllFrameClass := by
  convert K_definability';
  exact K_is_extK_of_empty;

instance K_sound : Sound 𝐊 (AllFrameClass#α) := inferInstance

instance K_consistent : System.Consistent (𝐊 : Hilbert α) := inferInstance


lemma restrict_finite : 𝔽#α ⊧ φ → 𝔽ꟳ#α ⊧ φ := by
  intro h F hF;
  obtain ⟨FF, hFF₁, rfl⟩ := hF;
  exact h (by simpa)

instance {Λ : Hilbert α} [sound : Sound Λ 𝔽#α] : Sound Λ 𝔽ꟳ#α := ⟨by
  intro φ h;
  exact restrict_finite $ sound.sound h;
⟩

instance : Sound 𝐊 (AllFrameClassꟳ#α) := inferInstance

lemma exists_finite_frame : ¬𝔽ꟳ#α ⊧ φ ↔ ∃ F ∈ 𝔽ꟳ, ¬F#α ⊧ φ := by simp;

class FiniteFrameProperty (Λ : Hilbert α) (𝔽 : FrameClass) where
  [complete : Complete Λ 𝔽ꟳ#α]
  [sound : Sound Λ 𝔽ꟳ#α]

end Kripke


section

open Formula (atom)
open Formula.Kripke
open Kripke (K_sound)


theorem K_strictlyWeakerThan_KD [DecidableEq α] [Inhabited α] : (𝐊 : Hilbert α) <ₛ 𝐊𝐃 := by
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

theorem K_strictlyWeakerThan_KB [DecidableEq α] [Inhabited α] : (𝐊 : Hilbert α) <ₛ 𝐊𝐁 := by
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

theorem K_strictlyWeakerThan_K4 [DecidableEq α] [Inhabited α] : (𝐊 : Hilbert α) <ₛ 𝐊𝟒 := by
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

theorem K_strictlyWeakerThan_K5 [DecidableEq α] [Inhabited α] : (𝐊 : Hilbert α) <ₛ 𝐊𝟓 := by
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


section

variable {Ax₁ Ax₂ : Theory α} (𝔽₁ 𝔽₂ : FrameClass)

lemma weakerThan_of_subset_FrameClass
  [sound₁ : Sound 𝜿Ax₁ 𝔽₁#α] [complete₂ : Complete 𝜿Ax₂ 𝔽₂#α]
  (h𝔽 : 𝔽₂ ⊆ 𝔽₁) : 𝜿Ax₁ ≤ₛ 𝜿Ax₂ := by
  apply System.weakerThan_iff.mpr;
  intro φ hp;
  apply complete₂.complete;
  intro F hF;
  exact sound₁.sound hp $ h𝔽 hF;

lemma equiv_of_eq_FrameClass
  [sound₁ : Sound 𝜿Ax₁ 𝔽₁#α] [sound₂ : Sound 𝜿Ax₂ 𝔽₂#α]
  [complete₁ : Complete 𝜿Ax₁ 𝔽₁#α] [complete₂ : Complete 𝜿Ax₂ 𝔽₂#α]
  (h𝔽 : 𝔽₁ = 𝔽₂) : 𝜿Ax₁ =ₛ 𝜿Ax₂ := by
  apply System.Equiv.antisymm_iff.mpr;
  constructor;
  . apply weakerThan_of_subset_FrameClass 𝔽₁ 𝔽₂; subst_vars; rfl;
  . apply weakerThan_of_subset_FrameClass 𝔽₂ 𝔽₁; subst_vars; rfl;

end


end

end Modal

end LO
