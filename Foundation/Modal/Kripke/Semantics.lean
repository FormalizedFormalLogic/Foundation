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
  | p ➝ q => (Satisfies M x p) ➝ (Satisfies M x q)
  | □p   => ∀ y, x ≺ y → (Satisfies M y p)

namespace Satisfies

protected instance semantics {M : Kripke.Model α} : Semantics (Formula α) (M.World) := ⟨fun x ↦ Formula.Kripke.Satisfies M x⟩

variable {M : Kripke.Model α} {x : M.World} {p q : Formula α}

@[simp]
protected lemma iff_models : x ⊧ p ↔ Kripke.Satisfies M x p := iff_of_eq rfl

lemma box_def : x ⊧ □p ↔ ∀ y, x ≺ y → y ⊧ p := by simp [Kripke.Satisfies];

lemma dia_def : x ⊧ ◇p ↔ ∃ y, x ≺ y ∧ y ⊧ p := by simp [Kripke.Satisfies];

lemma not_def : x ⊧ ∼p ↔ ¬(x ⊧ p) := by
  induction p using Formula.rec' generalizing x with
  | _ => simp_all [Satisfies];
instance : Semantics.Not (M.World) := ⟨not_def⟩

lemma imp_def : x ⊧ p ➝ q ↔ (x ⊧ p) → (x ⊧ q) := by tauto;
instance : Semantics.Imp (M.World) := ⟨imp_def⟩

lemma or_def : x ⊧ p ⋎ q ↔ x ⊧ p ∨ x ⊧ q := by simp [Satisfies]; tauto;
instance : Semantics.Or (M.World) := ⟨or_def⟩

lemma and_def : x ⊧ p ⋏ q ↔ x ⊧ p ∧ x ⊧ q := by simp [Satisfies];
instance : Semantics.And (M.World) := ⟨and_def⟩

protected instance : Semantics.Tarski (M.World) where
  realize_top := by tauto;
  realize_bot := by tauto;

lemma negneg_def : x ⊧ ∼∼p ↔ x ⊧ p := by simp [Satisfies];

lemma multibox_def : x ⊧ □^[n]p ↔ ∀ {y}, x ≺^[n] y → y ⊧ p := by
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

lemma multidia_def : x ⊧ ◇^[n]p ↔ ∃ y, x ≺^[n] y ∧ y ⊧ p := by
  induction n generalizing x with
  | zero => simp;
  | succ n ih =>
    constructor;
    . intro h;
      replace h : x ⊧ (◇◇^[n]p) := by simpa using h;
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

lemma trans (hpq : x ⊧ p ➝ q) (hqr : x ⊧ q ➝ r) : x ⊧ p ➝ r := by simp_all;

lemma mdp (hpq : x ⊧ p ➝ q) (hp : x ⊧ p) : x ⊧ q := by simp_all;

lemma dia_dual : x ⊧ ◇p ↔ x ⊧ ∼□(∼p) := by simp [Satisfies];

lemma box_dual : x ⊧ □p ↔ x ⊧ ∼◇(∼p) := by simp [Satisfies];

lemma not_imp : ¬(x ⊧ p ➝ q) ↔ x ⊧ p ⋏ ∼q := by simp [Satisfies];

end Satisfies


def ValidOnModel (M : Kripke.Model α) (p : Formula α) := ∀ x : M.World, x ⊧ p

namespace ValidOnModel

instance semantics : Semantics (Formula α) (Kripke.Model α) := ⟨fun M ↦ Formula.Kripke.ValidOnModel M⟩

@[simp] protected lemma iff_models {M : Kripke.Model α} : M ⊧ f ↔ Kripke.ValidOnModel M f := iff_of_eq rfl

instance : Semantics.Bot (Kripke.Model α) where
  realize_bot M := by simp [Kripke.ValidOnModel, Kripke.Satisfies];

variable {M : Model α} {p q r : Formula α}

protected lemma mdp (hpq : M ⊧ p ➝ q) (hp : M ⊧ p) : M ⊧ q := by
  intro x;
  exact (Satisfies.imp_def.mp $ hpq x) (hp x);

protected lemma nec (h : M ⊧ p) : M ⊧ □p := by
  intro x y _;
  exact h y;

protected lemma verum : M ⊧ ⊤ := by intro; tauto;

protected lemma imply₁ : M ⊧ (Axioms.Imply₁ p q) := by simp [ValidOnModel]; tauto;

protected lemma imply₂ : M ⊧ (Axioms.Imply₂ p q r) := by simp [ValidOnModel]; tauto;

protected lemma elimContra : M ⊧ (Axioms.ElimContra p q) := by simp [ValidOnModel, Satisfies]; tauto;

protected lemma axiomK : M ⊧ (Axioms.K p q)  := by
  intro V;
  apply Satisfies.imp_def.mpr;
  intro hpq;
  apply Satisfies.imp_def.mpr;
  intro hp x Rxy;
  replace hpq := Satisfies.imp_def.mp $ hpq x Rxy;
  replace hp := hp x Rxy;
  exact hpq hp;

end ValidOnModel


def ValidOnFrame (F : Frame) (p : Formula α) := ∀ V, (⟨F, V⟩ : Kripke.Model α) ⊧ p

namespace ValidOnFrame

instance semantics : Semantics (Formula α) (Frame.Dep α) := ⟨fun F ↦ Formula.Kripke.ValidOnFrame F⟩

variable {F : Frame.Dep α}

@[simp] protected lemma models_iff : F ⊧ p ↔ Kripke.ValidOnFrame F p := iff_of_eq rfl

instance : Semantics.Bot (Frame.Dep α) where
  realize_bot _ := by simp [Kripke.ValidOnFrame];

protected lemma nec (h : F ⊧ p) : F ⊧ □p := by
  intro V x y _;
  exact h V y;

protected lemma mdp (hpq : F ⊧ p ➝ q) (hp : F ⊧ p) : F ⊧ q := by
  intro V x;
  exact (hpq V x) (hp V x);

protected lemma verum : F ⊧ ⊤ := by intros _; tauto;

protected lemma imply₁ : F ⊧ (Axioms.Imply₁ p q) := by intro V; exact ValidOnModel.imply₁ (M := ⟨F, V⟩);

protected lemma imply₂ : F ⊧ (Axioms.Imply₂ p q r) := by intro V; exact ValidOnModel.imply₂ (M := ⟨F, V⟩);

protected lemma elimContra : F ⊧ (Axioms.ElimContra p q) := by intro V; exact ValidOnModel.elimContra (M := ⟨F, V⟩);

protected lemma axiomK : F ⊧ (Axioms.K p q) := by intro V; exact ValidOnModel.axiomK (M := ⟨F, V⟩);

protected lemma axiomK_set : F ⊧* 𝗞 := by
  simp [Semantics.realizeSet_iff];
  rintro f x y rfl;
  exact ValidOnFrame.axiomK;

end ValidOnFrame



@[simp] def ValidOnFrameClass (𝔽 : FrameClass) (p : Formula α) := ∀ {F : Frame}, F ∈ 𝔽 → F#α ⊧ p

namespace ValidOnFrameClass

protected instance semantics : Semantics (Formula α) (FrameClass.Dep α) := ⟨fun 𝔽 ↦ Kripke.ValidOnFrameClass 𝔽⟩

variable {𝔽 : FrameClass.Dep α}

@[simp] protected lemma models_iff : 𝔽 ⊧ p ↔ Formula.Kripke.ValidOnFrameClass 𝔽 p := iff_of_eq rfl

protected lemma nec (h : 𝔽 ⊧ p) : 𝔽 ⊧ □p := by
  intro _ hF;
  apply Kripke.ValidOnFrame.nec;
  exact h hF;

protected lemma mdp (hpq : 𝔽 ⊧ p ➝ q) (hp : 𝔽 ⊧ p) : 𝔽 ⊧ q := by
  intro _ hF;
  exact Kripke.ValidOnFrame.mdp (hpq hF) (hp hF)

end ValidOnFrameClass


abbrev ValidOnFiniteFrameClass (𝔽 : FiniteFrameClass) (p : Formula α) := 𝔽.toFrameClass#α ⊧ p

namespace ValidOnFiniteFrameClass

protected instance semantics : Semantics (Formula α) (FiniteFrameClass.Dep α) := ⟨fun 𝔽 ↦ Kripke.ValidOnFiniteFrameClass 𝔽⟩

variable {𝔽 : FiniteFrameClass.Dep α}

@[simp] protected lemma models_iff : 𝔽 ⊧ p ↔ Kripke.ValidOnFiniteFrameClass 𝔽 p := iff_of_eq rfl

end ValidOnFiniteFrameClass


end Formula.Kripke


namespace Kripke

open Formula.Kripke (ValidOnFrame ValidOnModel Satisfies)

variable {𝔽 : Kripke.FrameClass} {F : Kripke.Frame}
         {p q : Formula α}

protected lemma axiomK : 𝔽#α ⊧* 𝗞 := by
  simp only [Semantics.RealizeSet.setOf_iff];
  rintro f ⟨p, q, _⟩ F _;
  apply (Semantics.RealizeSet.setOf_iff.mp $ ValidOnFrame.axiomK_set) f;
  use p, q;

protected lemma nec (h : 𝔽#α ⊧ p) : 𝔽#α ⊧ □p := by
  intro _ hF;
  apply ValidOnFrame.nec;
  exact h hF;

protected lemma mdp (hpq : 𝔽#α ⊧ p ➝ q) (hp : 𝔽#α ⊧ p) : 𝔽#α ⊧ q := by
  intro _ hF;
  exact Formula.Kripke.ValidOnFrame.mdp (hpq hF) (hp hF)

lemma iff_not_validOnFrameClass : ¬(𝔽#α ⊧ p) ↔ ∃ F ∈ 𝔽, ∃ V x, ¬Satisfies ⟨F, V⟩ x p := by
  simp [ValidOnFrame, ValidOnModel, Satisfies];

lemma iff_not_set_validOnFrameClass : ¬(𝔽#α ⊧* T) ↔ ∃ p ∈ T, ∃ F ∈ 𝔽, ∃ V x, ¬Satisfies ⟨F, V⟩ x p  := by
  simp [Semantics.realizeSet_iff, ValidOnFrame, ValidOnModel, Satisfies];

lemma iff_not_validOnFrame : ¬(F#α ⊧* T) ↔ ∃ p ∈ T, ∃ V x, ¬Satisfies ⟨F, V⟩ x p := by
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
      intro p hp;
      exact h p $ Deduction.maxm! $ by right; exact hp;
    . intro hF p hp;
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
    intro F hF p hp;
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
      intro p hp;
      exact h p $ Deduction.maxm! $ by right; exact hp;
    . intro hF p hp;
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
    intro F hF p hp;
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
variable {Λ : Hilbert α} {p : Formula α}

lemma sound : Λ ⊢! p → 𝔽(Λ) ⊧ p := by
  intro hp F hF;
  simp [Hilbert.theorems, System.theory] at hF;
  exact hF p hp;
instance : Sound Λ 𝔽(Λ) := ⟨sound⟩

lemma sound_finite : Λ ⊢! p → 𝔽ꟳ(Λ) ⊧ p := by
  intro hp F hF;
  simp [Hilbert.theorems, System.theory] at hF;
  obtain ⟨FF, hFF₁, rfl⟩ := hF;
  exact hFF₁ p hp;
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
  : Λ ⊢! p → 𝔽#α ⊧ p := by
  intro h F hF;
  apply sound h;
  apply char.characterize hF;
instance {𝔽 : FrameClass} [𝔽(Λ).Characteraizable 𝔽] : Sound Λ 𝔽#α := ⟨sound_of_characterizability⟩

lemma sound_of_finite_characterizability {𝔽 : FiniteFrameClass} [char : 𝔽ꟳ(Λ).Characteraizable 𝔽]
  : Λ ⊢! p → 𝔽#α ⊧ p := by
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


lemma restrict_finite : 𝔽#α ⊧ p → 𝔽ꟳ#α ⊧ p := by
  intro h F hF;
  obtain ⟨FF, hFF₁, rfl⟩ := hF;
  exact h (by simpa)

instance {Λ : Hilbert α} [sound : Sound Λ 𝔽#α] : Sound Λ 𝔽ꟳ#α := ⟨by
  intro p h;
  exact restrict_finite $ sound.sound h;
⟩

instance : Sound 𝐊 (AllFrameClassꟳ#α) := inferInstance

lemma exists_finite_frame : ¬𝔽ꟳ#α ⊧ p ↔ ∃ F ∈ 𝔽ꟳ, ¬F#α ⊧ p := by simp;

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
  intro p hp;
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
