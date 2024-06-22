import Logic.Logic.System
import Logic.Modal.Standard.Formula
import Logic.Modal.Standard.Deduction

universe u v

namespace LO.Modal.Standard

def RelItr (R : α → α → Prop) : ℕ → α → α → Prop
  | 0 => (· = ·)
  | n + 1 => fun x y ↦ ∃ z, R x z ∧ RelItr R n z y

namespace RelItr

@[simp]
lemma iff_zero {R : α → α → Prop} {x y : α} : RelItr R 0 x y ↔ x = y := iff_of_eq rfl

@[simp]
lemma iff_succ {R : α → α → Prop} {x y : α} : RelItr R (n + 1) x y ↔ ∃ z, R x z ∧ RelItr R n z y := iff_of_eq rfl

@[simp]
lemma eq : RelItr (α := α) (· = ·) n = (· = ·) := by
  induction n with
  | zero => rfl;
  | succ n ih => aesop

end RelItr

namespace Kripke


structure Frame (α : Type*) where
  World : Type*
  [World_nonempty : Nonempty World]
  Rel : World → World → Prop

structure FiniteFrame (α) extends Frame α where
  [World_finite : Finite World]

instance (F : Frame α) : Nonempty F.World := F.World_nonempty

instance : CoeSort (Frame α) (Type*) := ⟨Frame.World⟩

instance : CoeFun (Frame α) (λ F => F.World → F.World → Prop) := ⟨Frame.Rel⟩

instance : Coe (FiniteFrame α) (Frame α) := ⟨λ F ↦ F.toFrame⟩

abbrev Frame.Rel' {F : Frame α} (w w' : F.World) := F.Rel w w'
scoped infix:45 " ≺ " => Frame.Rel'

protected abbrev Frame.RelItr' (n : ℕ) {F : Frame α} (w w' : F.World) : Prop := RelItr (· ≺ ·) n w w'
scoped notation w:45 " ≺^[" n "] " w':46 => Frame.RelItr' n w w'


protected def Frame.finite (F : Frame α) := Finite F.World


/-- Frame with single world and identiy relation -/
abbrev TerminalFrame (α) : FiniteFrame α := { World := PUnit, Rel := (· = ·) }

@[simp]
lemma TerminalFrame.iff_rel' : Frame.Rel' (F := (TerminalFrame α).toFrame) x y ↔ x = y := by aesop;

@[simp]
lemma TerminalFrame.iff_relItr' : Frame.RelItr' n (F := (TerminalFrame α).toFrame) x y ↔ x = y := by
  induction n with
  | zero => simp;
  | succ n ih => simp_all; use x;


abbrev PointFrame (α) : FiniteFrame α := { World := PUnit, Rel := (· ≠ ·) }



abbrev FrameClass (α) := Set (Frame α)

abbrev FiniteFrameClass (α) := Set (FiniteFrame α)

def FrameClass.toFinite (𝔽 : FrameClass α) : FrameClass α := { F ∈ 𝔽 | F.finite }
postfix:max "ᶠ" => FrameClass.toFinite

abbrev Valuation (W : Type u) (α : Type u) := W → α → Prop

structure Model (α) where
  Frame : Frame α
  Valuation : Valuation Frame.World α

abbrev Model.World (M : Model α) := M.Frame.World
instance : CoeSort (Model α) (Type _) where coe := Model.World


end Kripke


variable {α : Type*}

open Standard.Kripke

def Formula.kripke_satisfies (M : Kripke.Model α) (w : M.World) : Formula α → Prop
  | atom a  => M.Valuation w a
  | verum   => True
  | falsum  => False
  | and p q => (kripke_satisfies M w p) ∧ (kripke_satisfies M w q)
  | or p q  => (kripke_satisfies M w p) ∨ (kripke_satisfies M w q)
  | imp p q => (kripke_satisfies M w p) → (kripke_satisfies M w q)
  | box p   => ∀ {x}, w ≺ x → (kripke_satisfies M x p)

namespace Formula.kripke_satisfies

protected instance semantics (M : Model α) : Semantics (Formula α) (M.World) := ⟨fun w ↦ Formula.kripke_satisfies M w⟩

variable {M : Model α} {w : M.World} {p q : Formula α}

@[simp] protected lemma iff_models : w ⊧ f ↔ kripke_satisfies M w f := iff_of_eq rfl

lemma dia_def  : w ⊧ ◇p ↔ ∃ w', w ≺ w' ∧ w' ⊧ p := by simp [kripke_satisfies];

lemma multibox_def : w ⊧ □^[n]p ↔ ∀ v, w ≺^[n] v → v ⊧ p := by
  induction n generalizing w with
  | zero => simp;
  | succ n ih =>
    constructor;
    . intro h w' hww';
      simp at h;
      obtain ⟨v, hwv, hvw'⟩ := hww';
      exact (ih.mp $ h hwv) w' hvw';
    . simp;
      intro h w' hww';
      apply ih.mpr;
      intro v hwv;
      exact h v w' hww' hwv;

lemma multidia_def : w ⊧ ◇^[n]p ↔ ∃ v, w ≺^[n] v ∧ v ⊧ p := by
  induction n generalizing w with
  | zero => simp;
  | succ n ih =>
    constructor;
    . intro h;
      replace h : kripke_satisfies M w (◇◇^[n]p) := by simpa using h;
      obtain ⟨v, hwv, hv⟩ := dia_def.mp h;
      obtain ⟨x, hvx, hx⟩ := ih.mp hv;
      use x;
      constructor;
      . use v;
      . assumption;
    . simp [dia_def];
      intro x y hwy hyx hx;
      simp [kripke_satisfies];
      use y;
      constructor;
      . assumption;
      . apply ih.mpr;
        existsi x;
        simp_all;

instance : Semantics.Tarski M.World where
  realize_top := by simp [kripke_satisfies];
  realize_bot := by simp [kripke_satisfies];
  realize_not := by simp [kripke_satisfies];
  realize_and := by simp [kripke_satisfies];
  realize_or  := by simp [kripke_satisfies];
  realize_imp := by simp [kripke_satisfies];

end Formula.kripke_satisfies


def Formula.valid_on_KripkeModel (M : Model α) (f : Formula α) := ∀ w : M.World, w ⊧ f

namespace Formula.valid_on_KripkeModel

protected instance : Semantics (Formula α) (Model α) := ⟨fun M ↦ Formula.valid_on_KripkeModel M⟩

@[simp] protected lemma iff_models {M : Model α} : M ⊧ f ↔ valid_on_KripkeModel M f := iff_of_eq rfl

instance : Semantics.Bot (Model α) where
  realize_bot _ := by simp [valid_on_KripkeModel];

end Formula.valid_on_KripkeModel


def Formula.valid_on_KripkeFrame (F : Frame α) (f : Formula α) := ∀ V, (Model.mk F V) ⊧ f

namespace Formula.valid_on_KripkeFrame

protected instance semantics : Semantics (Formula α) (Frame α) := ⟨fun F ↦ Formula.valid_on_KripkeFrame F⟩

@[simp] protected lemma models_iff {F : Frame α} : F ⊧ f ↔ valid_on_KripkeFrame F f := iff_of_eq rfl

instance : Semantics.Bot (Frame α) where
  realize_bot _ := by simp [valid_on_KripkeFrame];

protected lemma axiomK {F : Frame α} : F ⊧* 𝗞 := by
  simp [valid_on_KripkeFrame, valid_on_KripkeModel, System.Axioms.K];
  intro f p q ef V x; subst ef;
  intro h₁ h₂ y rxy;
  exact h₁ rxy (h₂ rxy);

protected lemma nec {F : Frame α} (h : F ⊧ p) : F ⊧ □p := by
  intro V x y _;
  exact h V y;

protected lemma mdp {F : Frame α} (hpq : F ⊧ p ⟶ q) (hp : F ⊧ p) : F ⊧ q := by
  intro V x;
  exact (hpq V x) (hp V x);

end Formula.valid_on_KripkeFrame


@[simp] def Formula.valid_on_KripkeFrameClass (𝔽 : FrameClass α) (p : Formula α) := ∀ F ∈ 𝔽, F ⊧ p

namespace Formula.valid_on_KripkeFrameClass

protected instance semantics : Semantics (Formula α) (FrameClass α) := ⟨fun 𝔽 ↦ Formula.valid_on_KripkeFrameClass 𝔽⟩

variable {𝔽 : FrameClass α}

@[simp] protected lemma models_iff : 𝔽 ⊧ f ↔ Formula.valid_on_KripkeFrameClass 𝔽 f := iff_of_eq rfl

protected lemma axiomK : 𝔽 ⊧* 𝗞 := by
  simp only [Semantics.RealizeSet.setOf_iff];
  rintro f ⟨p, q, _⟩ F _;
  apply (Semantics.RealizeSet.setOf_iff.mp $ valid_on_KripkeFrame.axiomK) f;
  use p, q;

protected lemma nec (h : 𝔽 ⊧ p) : 𝔽 ⊧ □p := by
  intro F hF;
  apply valid_on_KripkeFrame.nec;
  exact h F hF;

protected lemma mdp (hpq : 𝔽 ⊧ p ⟶ q) (hp : 𝔽 ⊧ p) : 𝔽 ⊧ q := by
  intro F hF;
  exact valid_on_KripkeFrame.mdp (hpq F hF) (hp F hF)

end Formula.valid_on_KripkeFrameClass


namespace AxiomSet

variable {Ax Ax₁ Ax₂ : AxiomSet α}

def DefinesKripkeFrameClass (Ax : AxiomSet α) (𝔽 : FrameClass α) := ∀ {F}, F ⊧* Ax ↔ F ∈ 𝔽

lemma DefinesKripkeFrameClass.union (defines₁ : Ax₁.DefinesKripkeFrameClass 𝔽₁) (defines₂ : Ax₂.DefinesKripkeFrameClass 𝔽₂)
  : (Ax₁ ∪ Ax₂).DefinesKripkeFrameClass (𝔽₁ ∩ 𝔽₂) := by
  intro F;
  simp only [Semantics.RealizeSet.union_iff];
  constructor;
  . intro ⟨h₁, h₂⟩;
    constructor;
    . exact defines₁.mp h₁;
    . exact defines₂.mp h₂;
  . intro ⟨h₁, h₂⟩;
    constructor;
    . apply defines₁.mpr h₁;
    . apply defines₂.mpr h₂;


def FinitelyDefinesKripkeFrameClass (Ax : AxiomSet α) (𝔽 : FrameClass α) := ∀ {F}, F.finite → (F ⊧* Ax ↔ F ∈ 𝔽)

def FinitelyDefinesKripkeFrameClass.union (defines₁ : Ax₁.FinitelyDefinesKripkeFrameClass 𝔽₁) (defines₂ : Ax₂.FinitelyDefinesKripkeFrameClass 𝔽₂)
  : (Ax₁ ∪ Ax₂).FinitelyDefinesKripkeFrameClass (𝔽₁ ∩ 𝔽₂) := by
  intro F hF;
  simp [Semantics.RealizeSet.union_iff];
  constructor;
  . rintro ⟨h₁, h₂⟩;
    constructor;
    . simpa [hF] using defines₁ hF |>.mp h₁;
    . simpa [hF] using defines₂ hF |>.mp h₂;
  . intro ⟨h₁, h₂⟩;
    constructor;
    . simpa [hF] using defines₁ hF |>.mpr h₁;
    . simpa [hF] using defines₂ hF |>.mpr h₂;


lemma DefinesKripkeFrameClass.toFinitely (defines : Ax.DefinesKripkeFrameClass 𝔽) : Ax.FinitelyDefinesKripkeFrameClass 𝔽 := by
  intro F _;
  constructor;
  . intro h;
    exact defines.mp h
  . rintro h₁;
    exact defines.mpr (by simpa);

instance {𝔽 : FrameClass α} (ne : 𝔽ᶠ.Nonempty) : 𝔽.Nonempty := by
  obtain ⟨F, hF⟩ := ne;
  simp [FrameClass.toFinite] at hF;
  use F;
  exact hF.1;

end AxiomSet


namespace Kripke

open Formula
open AxiomSet (DefinesKripkeFrameClass)

abbrev AllFrameClass (α) : FrameClass α := Set.univ

lemma AllFrameClass.nonempty : (AllFrameClass α).Nonempty := by
  use TerminalFrame α; trivial;

lemma axiomK_defines : 𝗞.DefinesKripkeFrameClass (AllFrameClass α) := by
  intro F;
  simp only [Set.mem_univ, iff_true];
  exact valid_on_KripkeFrame.axiomK;

lemma axiomK_union_definability {Ax : AxiomSet α} {𝔽 : FrameClass α} : (Ax.DefinesKripkeFrameClass 𝔽) ↔ (𝗞 ∪ Ax).DefinesKripkeFrameClass 𝔽 := by
  constructor;
  . intro defines F;
    simp [DefinesKripkeFrameClass] at defines;
    constructor;
    . intro h;
      simp only [Semantics.RealizeSet.union_iff] at h;
      exact defines.mp h.2;
    . intro h;
      simp only [Semantics.RealizeSet.union_iff];
      constructor;
      . apply valid_on_KripkeFrame.axiomK;
      . exact defines.mpr h;
  . intro defines F;
    simp only [DefinesKripkeFrameClass] at defines;
    constructor;
    . intro h;
      apply defines.mp;
      simp only [Semantics.RealizeSet.union_iff];
      constructor;
      . apply valid_on_KripkeFrame.axiomK;
      . exact h;
    . intro h;
      simp only [Semantics.RealizeSet.union_iff] at defines;
      exact defines.mpr h |>.2;


def nonempty_of_exist_finiteFrame {𝔽 : FrameClass α} (h : ∃ (F : FiniteFrame α), F.toFrame ∈ 𝔽) : 𝔽ᶠ.Nonempty := by
  obtain ⟨F, hF⟩ := h;
  use F.toFrame;
  constructor;
  . assumption;
  . exact F.World_finite;

end Kripke


namespace DeductionParameter

open Kripke
variable {Λ Λ₁ Λ₂ : DeductionParameter α} [Λ.IsNormal]
variable {Ax : AxiomSet α}

abbrev DefinesKripkeFrameClass (Λ : DeductionParameter α) [Λ.IsNormal] (𝔽 : FrameClass α) := AxiomSet.DefinesKripkeFrameClass (Ax(Λ)) 𝔽

lemma DefinesKripkeFrameClass.toAx (defines : Λ.DefinesKripkeFrameClass 𝔽) : Ax(Λ).DefinesKripkeFrameClass 𝔽 := by
  simp [DefinesKripkeFrameClass] at defines;
  exact defines;

lemma DefinesKripkeFrameClass.toAx' (defines : Axᴺ.DefinesKripkeFrameClass 𝔽) : Ax.DefinesKripkeFrameClass 𝔽 := by
  simp [DefinesKripkeFrameClass] at defines;
  exact axiomK_union_definability.mpr defines;

lemma DefinesKripkeFrameClass.ofAx (defines : Ax.DefinesKripkeFrameClass 𝔽) [Axᴺ.IsNormal] : (Ax)ᴺ.DefinesKripkeFrameClass 𝔽 := by
  apply axiomK_union_definability.mp;
  assumption;


abbrev FinitelyDefinesKripkeFrameClass (Λ : DeductionParameter α) [Λ.IsNormal] (𝔽 : FrameClass α) := AxiomSet.FinitelyDefinesKripkeFrameClass (Ax(Λ)) 𝔽

end DeductionParameter



end LO.Modal.Standard
