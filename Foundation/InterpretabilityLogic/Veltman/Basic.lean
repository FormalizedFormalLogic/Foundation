import Foundation.InterpretabilityLogic.Formula.Substitution
import Foundation.InterpretabilityLogic.Axioms
import Foundation.Modal.Kripke.Logic.GL.Completeness

namespace LO.InterpretabilityLogic

open Entailment

namespace Veltman

structure Frame extends toKripkeFrame : Modal.Kripke.Frame where
  [F_GL : toKripkeFrame.IsInfiniteGL]
  S : (w : World) → (HRel { v // Rel w v })
  S_refl  : ∀ w, IsRefl _ (S w)
  S_trans : ∀ w, IsTrans _ (S w)

instance {F :  Frame} : F.IsInfiniteGL := F.F_GL

class Frame.IsIL (F : Frame) where
  S_IL : ∀ w : F.World, ∀ x y : { v // w ≺ v }, (x.1 ≺ y.1) → (F.S w x y)

abbrev FrameClass := Set (Frame)

abbrev Valuation (F : Frame) := F.World → ℕ → Prop

structure Model extends toVeltmanFrame : Veltman.Frame where
  Val : Valuation toVeltmanFrame
instance : CoeSort Model Type := ⟨λ M => M.toKripkeFrame.World⟩
instance : CoeFun (Model) (λ M => M.World → ℕ → Prop) := ⟨fun m => m.Val⟩

end Veltman


open Veltman

namespace Formula.Veltman

def Satisfies (M : Veltman.Model) (x : M.World) : Formula ℕ → Prop
  | atom a  => M x a
  | ⊥  => False
  | φ ➝ ψ => (Satisfies M x φ) ➝ (Satisfies M x ψ)
  | □φ   => ∀ y, x ≺ y → (Satisfies M y φ)
  | φ ▷ ψ => ∀ y, (Rxy : (x ≺ y)) → Satisfies M y φ → (∃ z : { v // x ≺ v }, M.S x ⟨y, Rxy⟩ z ∧ Satisfies M z ψ)


namespace Satisfies

protected instance semantics {M : Veltman.Model} : Semantics M (Formula ℕ) := ⟨fun x ↦ Formula.Veltman.Satisfies M x⟩

variable {M : Veltman.Model} {x : M.World} {φ ψ : Formula ℕ}

@[simp] protected lemma iff_models : x ⊧ φ ↔ Veltman.Satisfies M x φ := iff_of_eq rfl

@[simp] lemma atom_def : x ⊧ atom a ↔ M x a := by simp [Satisfies];

protected lemma bot_def : ¬x ⊧ ⊥ := by simp [Satisfies];

protected lemma imp_def : x ⊧ φ ➝ ψ ↔ (x ⊧ φ) → (x ⊧ ψ) := by tauto;
protected lemma not_imp_def : ¬(x ⊧ φ ➝ ψ) ↔ (x ⊧ φ) ∧ ¬(x ⊧ ψ) := by constructor <;> . contrapose!; tauto;

protected lemma imp_def₂ : x ⊧ φ ➝ ψ ↔ ¬x ⊧ φ ∨ x ⊧ ψ := by tauto;

protected lemma or_def : x ⊧ φ ⋎ ψ ↔ x ⊧ φ ∨ x ⊧ ψ := by simp [Satisfies]; tauto;

protected lemma and_def : x ⊧ φ ⋏ ψ ↔ x ⊧ φ ∧ x ⊧ ψ := by simp [Satisfies];

protected lemma not_def : x ⊧ ∼φ ↔ ¬(x ⊧ φ) := by simp [Satisfies];

protected lemma top_def : x ⊧ ⊤ := by simp [Satisfies];

protected lemma box_def : x ⊧ □φ ↔ ∀ y, x ≺ y → y ⊧ φ := by simp [Satisfies];
protected lemma not_box_def : ¬x ⊧ □φ ↔ (∃ y, x ≺ y ∧ ¬y ⊧ φ) := by simp [Satisfies];

protected lemma dia_def : x ⊧ ◇φ ↔ ∃ y, x ≺ y ∧ y ⊧ φ := by simp [Satisfies];
protected lemma not_dia_def : ¬x ⊧ ◇φ ↔ ∀ y, x ≺ y → ¬(y ⊧ φ) := by simp [Satisfies];

protected lemma rhd_def : x ⊧ φ ▷ ψ ↔ ∀ y, (Rxy : (x ≺ y)) → (y ⊧ φ) → (∃ z : { v // x ≺ v }, M.S x ⟨y, Rxy⟩ z ∧ z.1 ⊧ ψ) := by simp [Satisfies];

protected instance : Semantics.Tarski (M.World) where
  models_verum := λ _ => Satisfies.top_def;
  models_falsum := λ _ => Satisfies.bot_def;
  models_imply := Satisfies.imp_def;
  models_not := Satisfies.not_def;
  models_or := Satisfies.or_def;
  models_and := Satisfies.and_def;

lemma iff_def : x ⊧ φ ⭤ ψ ↔ (x ⊧ φ ↔ x ⊧ ψ) := by simp;

lemma trans (hpq : x ⊧ φ ➝ ψ) (hqr : x ⊧ ψ ➝ χ) : x ⊧ φ ➝ χ := by simp_all;

lemma mdp (hpq : x ⊧ φ ➝ ψ) (hp : x ⊧ φ) : x ⊧ ψ := by simp_all;

lemma iff_subst_self {x : F.World} (s : Substitution ℕ) :
  letI U : Veltman.Valuation F := λ w a => Satisfies ⟨F, V⟩ w ((atom a)⟦s⟧);
  Satisfies ⟨F, U⟩ x φ ↔ Satisfies ⟨F, V⟩ x (φ⟦s⟧) := by
  induction φ generalizing x with
  | hatom a => simp [Satisfies];
  | hfalsum => simp [Satisfies];
  | hbox φ ih =>
    constructor;
    . intro hbφ y Rxy;
      apply ih.mp;
      exact hbφ y Rxy;
    . intro hbφ y Rxy;
      apply ih.mpr;
      exact hbφ y Rxy;
  | himp φ ψ ihφ ihψ =>
    constructor;
    . intro hφψ hφ;
      apply ihψ.mp;
      apply hφψ;
      apply ihφ.mpr;
      exact hφ;
    . intro hφψs hφ;
      apply ihψ.mpr;
      apply hφψs;
      apply ihφ.mp;
      exact hφ;
  | hrhd φ ψ ihφ ihψ =>
    constructor;
    . intro h y Rxy hy;
      obtain ⟨⟨z, Rxz⟩, hz₁, hz₂⟩ := h _ Rxy $ by
        sorry;
      use ⟨z, Rxz⟩;
      constructor;
      . sorry;
      . sorry;
    . sorry;

end Satisfies


def ValidOnModel (M : Veltman.Model) (φ : Formula ℕ) := ∀ x : M.World, x ⊧ φ

namespace ValidOnModel

instance semantics : Semantics Veltman.Model (Formula ℕ) := ⟨fun M ↦ Formula.Veltman.ValidOnModel M⟩

variable {M : Veltman.Model} {φ ψ χ : Formula ℕ}

@[simp] protected lemma iff_models : M ⊧ φ ↔ Veltman.ValidOnModel M φ := iff_of_eq rfl

protected lemma bot_def : ¬M ⊧ ⊥ := by simp [Veltman.ValidOnModel];

protected lemma top_def : M ⊧ ⊤ := by simp [Veltman.ValidOnModel];

instance : Semantics.Bot (Veltman.Model) where
  models_falsum := λ _ => ValidOnModel.bot_def;

instance : Semantics.Top (Veltman.Model) where
  models_verum := λ _ => ValidOnModel.top_def;


lemma iff_not_exists_world {M : Veltman.Model} : (¬M ⊧ φ) ↔ (∃ x : M.World, ¬x ⊧ φ) := by
  apply not_iff_not.mp;
  push_neg;
  tauto;

alias ⟨exists_world_of_not, not_of_exists_world⟩ := iff_not_exists_world


protected lemma mdp (hpq : M ⊧ φ ➝ ψ) (hp : M ⊧ φ) : M ⊧ ψ := by
  intro x;
  exact (Satisfies.imp_def.mp $ hpq x) (hp x);

protected lemma nec (h : M ⊧ φ) : M ⊧ □φ := by
  intro x y _;
  exact h y;

lemma multinec (n) (h : M ⊧ φ) : M ⊧ □^[n]φ := by
  induction n with
  | zero => tauto;
  | succ n ih => simpa using ValidOnModel.nec ih;

protected lemma imply₁ : M ⊧ (Axioms.Imply₁ φ ψ) := by simp [ValidOnModel]; tauto;

protected lemma imply₂ : M ⊧ (Axioms.Imply₂ φ ψ χ) := by simp [ValidOnModel]; tauto;

protected lemma elimContra : M ⊧ (Axioms.ElimContra φ ψ) := by simp [ValidOnModel]; tauto;

protected lemma axiomK : M ⊧ (Modal.Axioms.K φ ψ)  := by
  intro V;
  apply Satisfies.imp_def.mpr;
  intro hpq;
  apply Satisfies.imp_def.mpr;
  intro hp x Rxy;
  replace hpq := Satisfies.imp_def.mp $ hpq x Rxy;
  replace hp := hp x Rxy;
  exact hpq hp;

protected lemma axiomL : M ⊧ (Modal.Axioms.L φ) := by
  rintro w;
  apply Satisfies.imp_def.mpr;
  contrapose;
  intro h;
  obtain ⟨x, Rwx, h⟩ := by simpa using Satisfies.box_def.not.mp h;
  obtain ⟨m, ⟨⟨Rwm, hm⟩, hm₂⟩⟩ := M.toKripkeFrame.cwf.has_min ({ x | w ≺ x ∧ ¬(Satisfies M x φ) }) $ by
    use x;
    tauto;
  replace hm₂ : ∀ x, w ≺ x → ¬Satisfies M x φ → ¬m ≺ x := by simpa using hm₂;
  apply Satisfies.not_box_def.mpr;
  use m;
  constructor;
  . assumption;
  . apply Satisfies.not_imp_def.mpr;
    constructor;
    . intro n rmn;
      apply not_imp_not.mp $ hm₂ n (IsTrans.trans _ _ _ Rwm rmn);
      exact rmn;
    . assumption;

protected lemma axiomJ1 : M ⊧ Axioms.J1 φ ψ := by
  intro x h y Rxy hy;
  use ⟨y, Rxy⟩;
  constructor;
  . apply M.toVeltmanFrame.S_refl x |>.refl;
  . exact h y Rxy hy;

protected lemma axiomJ2 : M ⊧ Axioms.J2 φ ψ χ := by
  intro x h₁ h₂ y Rxy hy;
  obtain ⟨⟨u, Rxu⟩, Sxyu, hu⟩ := h₁ _ Rxy hy;
  obtain ⟨⟨v, Ruv⟩, Sxuv, hv⟩ := h₂ u Rxu hu;
  use ⟨v, Ruv⟩;
  constructor;
  . apply M.toVeltmanFrame.S_trans x |>.trans;
    . exact Sxyu;
    . exact Sxuv;
  . assumption;

protected lemma axiomJ3 : M ⊧ Axioms.J3 φ ψ χ := by
  intro x h₁ h₂ y Rxy h₃;
  rcases Veltman.Satisfies.or_def.mp h₃ with (h₃ | h₃);
  . obtain ⟨⟨u, Rxu⟩, Sxyu, hu⟩ := h₁ _ Rxy h₃; use ⟨u, Rxu⟩;
  . obtain ⟨⟨u, Rxu⟩, Sxyu, hu⟩ := h₂ _ Rxy h₃; use ⟨u, Rxu⟩;

protected lemma axiomJ4 : M ⊧ Axioms.J4 φ ψ := by
  intro x h₁ h₂;
  obtain ⟨y, Rxy, hy⟩ := Satisfies.dia_def.mp h₂;
  obtain ⟨⟨z, Rxz⟩, Sxyz, hz⟩ := h₁ _ Rxy hy;
  apply Satisfies.dia_def.mpr;
  use z;
  tauto;

protected lemma axiomJ5 [M.toVeltmanFrame.IsIL] : M ⊧ Axioms.J5 φ := by
  intro x y Rxy h;
  obtain ⟨z, Ryz, hz⟩ := Satisfies.dia_def.mp h;
  use ⟨z, M.toKripkeFrame.trans Rxy Ryz⟩;
  constructor;
  . apply Veltman.Frame.IsIL.S_IL; simpa;
  . assumption;

end ValidOnModel


def ValidOnFrame (F : Veltman.Frame) (φ : Formula ℕ) := ∀ V, (⟨F, V⟩ : Veltman.Model) ⊧ φ

namespace ValidOnFrame

instance semantics : Semantics Veltman.Frame (Formula ℕ) := ⟨fun F ↦ Formula.Veltman.ValidOnFrame F⟩

variable {F : Veltman.Frame} {φ ψ χ : Formula ℕ}

@[simp] protected lemma models_iff : F ⊧ φ ↔ Veltman.ValidOnFrame F φ := iff_of_eq rfl

lemma models_set_iff : F ⊧* Φ ↔ ∀ φ ∈ Φ, F ⊧ φ := by simp [Semantics.modelsSet_iff];

protected lemma top_def : F ⊧ ⊤ := by simp [ValidOnFrame];

protected lemma bot_def : ¬F ⊧ ⊥ := by simp [ValidOnFrame];

instance : Semantics.Top (Veltman.Frame) where
  models_verum _ := ValidOnFrame.top_def;

instance : Semantics.Bot (Veltman.Frame) where
  models_falsum _ := ValidOnFrame.bot_def

lemma iff_not_exists_valuation : (¬F ⊧ φ) ↔ (∃ V : Veltman.Valuation F, ¬(⟨F, V⟩ : Veltman.Model) ⊧ φ) := by
  simp [ValidOnFrame];

alias ⟨exists_valuation_of_not, not_of_exists_valuation⟩ := iff_not_exists_valuation

lemma iff_not_exists_valuation_world : (¬F ⊧ φ) ↔ (∃ V : Veltman.Valuation F, ∃ x : (⟨F, V⟩ : Veltman.Model).World, ¬Satisfies _ x φ) := by
  simp [ValidOnFrame, ValidOnModel, Semantics.Models];

alias ⟨exists_valuation_world_of_not, not_of_exists_valuation_world⟩ := iff_not_exists_valuation_world

lemma iff_not_exists_model_world :  (¬F ⊧ φ) ↔ (∃ M : Veltman.Model, ∃ x : M.World, M.toVeltmanFrame = F ∧ ¬(x ⊧ φ)) := by
  constructor;
  . intro h;
    obtain ⟨V, x, h⟩ := iff_not_exists_valuation_world.mp h;
    use ⟨F, V⟩, x;
    tauto;
  . rintro ⟨M, x, rfl, h⟩;
    exact iff_not_exists_valuation_world.mpr ⟨M.Val, x, h⟩;

alias ⟨exists_model_world_of_not, not_of_exists_model_world⟩ := iff_not_exists_model_world


protected lemma mdp (hpq : F ⊧ φ ➝ ψ) (hp : F ⊧ φ) : F ⊧ ψ := by
  intro V x;
  exact (hpq V x) (hp V x);

protected lemma nec (h : F ⊧ φ) : F ⊧ □φ := by
  intro V x y _;
  exact h V y;

protected lemma subst (h : F ⊧ φ) : F ⊧ φ⟦s⟧ := by
  by_contra hC;
  replace hC := iff_not_exists_valuation_world.mp hC;
  obtain ⟨V, ⟨x, hx⟩⟩ := hC;
  apply Satisfies.iff_subst_self s |>.not.mpr hx;
  exact h (λ w a => Satisfies ⟨F, V⟩ w (atom a⟦s⟧)) x;

protected lemma imply₁ : F ⊧ (Axioms.Imply₁ φ ψ) := fun _ ↦ ValidOnModel.imply₁

protected lemma imply₂ : F ⊧ (Axioms.Imply₂ φ ψ χ) := fun _ ↦ ValidOnModel.imply₂

protected lemma elimContra : F ⊧ (Axioms.ElimContra φ ψ) := fun _ ↦ ValidOnModel.elimContra

@[simp] protected lemma axiomK : F ⊧ (Modal.Axioms.K φ ψ) := fun _ ↦ ValidOnModel.axiomK

@[simp] protected lemma axiomL : F ⊧ (Modal.Axioms.L φ) := fun _ ↦ ValidOnModel.axiomL

@[simp] protected lemma axiomJ1 : F ⊧ Axioms.J1 φ ψ := fun _ ↦ ValidOnModel.axiomJ1

@[simp] protected lemma axiomJ2 : F ⊧ Axioms.J2 φ ψ χ := fun _ ↦ ValidOnModel.axiomJ2

@[simp] protected lemma axiomJ3 : F ⊧ Axioms.J3 φ ψ χ := fun _ ↦ ValidOnModel.axiomJ3

@[simp] protected lemma axiomJ4 : F ⊧ Axioms.J4 φ ψ := fun _ ↦ ValidOnModel.axiomJ4

@[simp] protected lemma axiomJ5 [F.IsIL] : F ⊧ Axioms.J5 φ := fun _ ↦ ValidOnModel.axiomJ5

end ValidOnFrame

end Formula.Veltman


namespace Veltman

section

variable {C : Veltman.FrameClass} {φ ψ χ : Formula ℕ}

lemma iff_not_validOnFrameClass_exists_frame : (¬C ⊧ φ) ↔ (∃ F ∈ C, ¬F ⊧ φ) := by
  apply not_iff_not.mp;
  push_neg;
  tauto;
alias ⟨exists_frame_of_not_validOnFrameClass, not_validOnFrameClass_of_exists_frame⟩ := iff_not_validOnFrameClass_exists_frame

lemma iff_not_validOnFrameClass_exists_model : (¬C ⊧ φ) ↔ (∃ M : Veltman.Model, M.toVeltmanFrame ∈ C ∧ ¬M ⊧ φ) := by
  apply not_iff_not.mp;
  push_neg;
  tauto;
alias ⟨exists_model_of_not_validOnFrameClass, not_validOnFrameClass_of_exists_model⟩ := iff_not_validOnFrameClass_exists_model

lemma iff_not_validOnFrameClass_exists_model_world : (¬C ⊧ φ) ↔ (∃ M : Veltman.Model, ∃ x : M.World, M.toVeltmanFrame ∈ C ∧ ¬(x ⊧ φ)) := by
  apply not_iff_not.mp;
  push_neg;
  tauto;
alias ⟨exists_model_world_of_not_validOnFrameClass, not_validOnFrameClass_of_exists_model_world⟩ := iff_not_validOnFrameClass_exists_model_world

lemma iff_not_validOnFrameClass_exists_valuation_world : (¬C ⊧ φ) ↔ (∃ F ∈ C, ∃ V, ∃ x, ¬(Formula.Veltman.Satisfies ⟨F, V⟩ x φ)) := by
  apply not_iff_not.mp;
  push_neg;
  tauto;
alias ⟨exists_valuation_world_of_not_validOnFrameClass, not_validOnFrameClass_of_exists_valuation_world⟩ := iff_not_validOnFrameClass_exists_valuation_world

end

end Veltman

end LO.InterpretabilityLogic
