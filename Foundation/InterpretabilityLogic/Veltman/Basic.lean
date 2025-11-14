import Foundation.InterpretabilityLogic.Formula.Substitution
import Foundation.InterpretabilityLogic.Axioms
import Foundation.InterpretabilityLogic.Logic.Basic
import Foundation.InterpretabilityLogic.Formula.OfModal
import Foundation.Modal.Kripke.Logic.GL.Completeness

namespace LO.InterpretabilityLogic

open Entailment

namespace Veltman

/--
  **Note**:

  To be precise, we call _Veltman frame_ when `S` has reflexive, transitive and satisfies `S_IL` conditions,
  i.e. satisfies `IsIL`.
  Frames that impose none of these conditions are called _Veltman prestructures_ or _ILMinus frames_.
  However, since making such distinctions is cumbersome in formalizing,
  we will refer to frames where only `S` is defined as Veltman frames in this project.
-/
structure Frame extends toKripkeFrame : Modal.Kripke.Frame where
  [isGL : toKripkeFrame.IsGL]
  S : (w : World) → HRel World
  S_cond {w x y} : S w x y → w ≺ x

namespace Frame

instance {F : Veltman.Frame} : F.IsGL := F.isGL

abbrev SRel' {F : Veltman.Frame} (w : outParam F.World) (x y : F.World) := F.S w x y
notation:45 x:max " ≺[" w "] " y:max => SRel' w x y

abbrev SInvRel {F : Veltman.Frame} (w : outParam F.World) (x y : F.World) := F.S w y x
notation:45 x:max " ≻[" w "] " y:max => SInvRel w x y

end Frame

abbrev FrameClass := Set (Frame)

abbrev Valuation (F : Frame) := F.World → ℕ → Prop

structure Model extends toVeltmanFrame : Veltman.Frame where
  Val : Valuation toVeltmanFrame
instance : CoeSort Model Type := ⟨λ M => M.toKripkeFrame.World⟩
instance : CoeFun (Model) (λ M => M.World → ℕ → Prop) := ⟨fun m => m.Val⟩

def Model.toKripkeModel (M : Veltman.Model) : Modal.Kripke.Model := ⟨M.toKripkeFrame, M.Val⟩

end Veltman


open Veltman

namespace Formula.Veltman

def Satisfies (M : Veltman.Model) (x : M.World) : Formula ℕ → Prop
  | atom a  => M x a
  | ⊥  => False
  | φ ➝ ψ => (Satisfies M x φ) ➝ (Satisfies M x ψ)
  | □φ   => ∀ y, x ≺ y → (Satisfies M y φ)
  | φ ▷ ψ => ∀ y, x ≺ y → Satisfies M y φ → (∃ z, y ≺[x] z ∧ Satisfies M z ψ)


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

protected lemma neg_def : x ⊧ ∼φ ↔ ¬(x ⊧ φ) := by simp [Satisfies];
protected lemma not_neg_def : ¬(x ⊧ ∼φ) ↔ x ⊧ φ := by simp [Satisfies];

protected lemma top_def : x ⊧ ⊤ := by simp [Satisfies];

protected lemma box_def : x ⊧ □φ ↔ ∀ y, x ≺ y → y ⊧ φ := by simp [Satisfies];
protected lemma not_box_def : ¬x ⊧ □φ ↔ (∃ y, x ≺ y ∧ ¬y ⊧ φ) := by simp [Satisfies];

protected lemma dia_def : x ⊧ ◇φ ↔ ∃ y, x ≺ y ∧ y ⊧ φ := by simp [Satisfies];
protected lemma not_dia_def : ¬x ⊧ ◇φ ↔ ∀ y, x ≺ y → ¬(y ⊧ φ) := by simp [Satisfies];

protected lemma rhd_def : x ⊧ φ ▷ ψ ↔ ∀ y, x ≺ y → Satisfies M y φ → (∃ z, y ≺[x] z ∧ Satisfies M z ψ) := by simp [Satisfies];
protected lemma not_rhd_def : ¬x ⊧ φ ▷ ψ ↔ ∃ y, x ≺ y ∧ Satisfies M y φ ∧ ∀ z, y ≺[x] z → ¬(Satisfies M z ψ) := by simp [Satisfies];

protected instance : Semantics.Tarski (M.World) where
  models_verum := λ _ => Satisfies.top_def;
  models_falsum := λ _ => Satisfies.bot_def;
  models_imply := Satisfies.imp_def;
  models_not := Satisfies.neg_def;
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
      obtain ⟨z, Sxyz, hz⟩ := h y Rxy $ ihφ.mpr hy;
      use z;
      constructor;
      . assumption;
      . apply ihψ.mp;
        assumption;
    . intro h y Rxy hy;
      obtain ⟨z, Sxyz, hz₂⟩ := h y Rxy $ ihφ.mp hy;
      use z;
      constructor;
      . assumption;
      . apply ihψ.mpr;
        assumption;

/-- For **modal** formula `φ`, Veltman model `M` and `x` in `M`. `M, x ⊧ φ` if and only if `M.toKripkeModel x ⊧ φ` -/
lemma kripkeLift {φ : Modal.Formula _} : x ⊧ ↑φ ↔ Modal.Formula.Kripke.Satisfies M.toKripkeModel x φ := by
  induction φ generalizing x with
  | hatom a =>
    simp [Modal.Formula.toInterpretabilityLogicFormula, Semantics.Models, Formula.Veltman.Satisfies, Modal.Formula.Kripke.Satisfies];
    tauto;
  | hfalsum =>
    simp [Modal.Formula.toInterpretabilityLogicFormula, Semantics.Models, Formula.Veltman.Satisfies, Modal.Formula.Kripke.Satisfies];
  | himp φ ψ ihφ ihψ =>
    constructor;
    . intro h hφ;
      apply ihψ.mp;
      apply h;
      apply ihφ.mpr;
      exact hφ;
    . intro h hφ;
      apply ihψ.mpr;
      apply h;
      apply ihφ.mp;
      exact hφ;
  | hbox φ ih =>
    constructor;
    . intro h y Rxy;
      apply ih.mp;
      apply h;
      exact Rxy;
    . intro h y Rxy;
      apply ih.mpr;
      apply h;
      exact Rxy;

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

/-- For **modal** formula `φ`, Veltman model `M`. `M ⊧ φ` if and only if `M.toKripkeModel ⊧ φ` -/
lemma kripkeLift {φ : Modal.Formula _} : M ⊧ ↑φ ↔ M.toKripkeModel ⊧ φ := by
  constructor;
  . intro h x; apply Satisfies.kripkeLift.mp; apply h;
  . intro h x; exact (Satisfies.kripkeLift.mpr $ h x);

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

protected lemma implyK : M ⊧ (Axioms.ImplyK φ ψ) := by simp [ValidOnModel]; tauto;

protected lemma implyS : M ⊧ (Axioms.ImplyS φ ψ χ) := by simp [ValidOnModel]; tauto;

protected lemma elimContra : M ⊧ (Axioms.ElimContra φ ψ) := by simp [ValidOnModel]; tauto;

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

protected lemma subst (h : F ⊧ φ) : F ⊧ φ⟦s⟧ := by
  by_contra hC;
  replace hC := iff_not_exists_valuation_world.mp hC;
  obtain ⟨V, ⟨x, hx⟩⟩ := hC;
  apply Satisfies.iff_subst_self s |>.not.mpr hx;
  exact h (λ w a => Satisfies ⟨F, V⟩ w (atom a⟦s⟧)) x;

/-- For **modal** formula `φ`, Veltman frame `F`. `F ⊧ φ` if and only if `F.toKripkeFrame ⊧ φ` -/
lemma kripkeLift {φ : Modal.Formula _} : F ⊧ ↑φ ↔ F.toKripkeFrame ⊧ φ := by
  constructor;
  . intro h V;
    apply ValidOnModel.kripkeLift.mp $ h V;
  . intro h K;
    apply ValidOnModel.kripkeLift.mpr;
    apply h;


end ValidOnFrame

end Formula.Veltman


namespace Veltman

lemma validate_of_logic_provable {F : Veltman.Frame} {L : Logic ℕ} (h : F ⊧* L) (hL : L ⊢ φ) : F ⊧ φ := by
  apply h.models;
  rwa [Logic.iff_provable] at hL;

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


section

open Formula.Veltman
variable {F : Veltman.Frame} {φ ψ χ : Formula ℕ}

@[simp high, grind .]
lemma validate_implyK : F ⊧ (Axioms.ImplyK φ ψ) := by tauto;

@[simp high, grind .]
lemma validate_implyS : F ⊧ (Axioms.ImplyS φ ψ χ) := by tauto;

@[simp high, grind .]
lemma validate_elimContra : F ⊧ (Axioms.ElimContra φ ψ) := by
  intro V x;
  simp [Semantics.Models, Satisfies];
  tauto;

@[grind ⇒]
lemma validate_mdp (hpq : F ⊧ φ ➝ ψ) (hp : F ⊧ φ) : F ⊧ ψ := by
  intro V x;
  exact (hpq V x) (hp V x);

@[grind ⇒]
lemma validate_nec (h : F ⊧ φ) : F ⊧ □φ := by
  intro V x y _;
  exact h V y;

@[simp high, grind .]
lemma validate_axiomK : F ⊧ (Modal.Axioms.K φ ψ) := by
  intro V x;
  apply Satisfies.imp_def.mpr;
  intro hpq;
  apply Satisfies.imp_def.mpr;
  intro hp x Rxy;
  replace hpq := Satisfies.imp_def.mp $ hpq x Rxy;
  replace hp := hp x Rxy;
  exact hpq hp;

@[simp high, grind .]
lemma validate_axiomL : F ⊧ (Modal.Axioms.L φ) :=
  ValidOnFrame.subst (s := λ _ => φ) $ ValidOnFrame.kripkeLift.mpr $ Modal.Kripke.validate_AxiomL_of_trans_cwf (φ := (.atom 0))

@[grind ⇒]
lemma validate_R1 (h : F ⊧ φ ➝ ψ) : F ⊧ χ ▷ φ ➝ χ ▷ ψ := by
  rintro V x h₁ y Rxy h₂;
  obtain ⟨z, _, _⟩ := h₁ y Rxy h₂;
  use z;
  constructor;
  . assumption;
  . apply h;
    assumption;

@[grind ⇒]
lemma validate_R2 (h : F ⊧ φ ➝ ψ) : F ⊧ ψ ▷ χ ➝ φ ▷ χ := by
  rintro V x h₁ y Rxy h₂;
  obtain ⟨z, Sxyz, hzχ⟩ := h₁ y Rxy $ by
    apply h;
    assumption;
  use z;

@[simp high, grind .]
lemma validate_axiomJ3 : F ⊧ Axioms.J3 φ ψ χ := by
  intro V x h₁ h₂ y Rxy h₃;
  rcases Satisfies.or_def.mp h₃ with (h₃ | h₃);
  . obtain ⟨u, Sxyu, hu⟩ := h₁ y Rxy h₃; use u;
  . obtain ⟨u, Sxyu, hu⟩ := h₂ y Rxy h₃; use u;

@[simp high, grind .]
lemma validate_axiomJ6 : F ⊧ Axioms.J6 φ := by
  intro V x;
  apply Satisfies.iff_def.mpr
  constructor;
  . rintro h y Rxy hy;
    have := h y Rxy;
    contradiction;
  . intro h y Rxy;
    by_contra hy;
    obtain ⟨z, _, _⟩ := h y Rxy hy;
    contradiction;

end

end Veltman

end LO.InterpretabilityLogic
