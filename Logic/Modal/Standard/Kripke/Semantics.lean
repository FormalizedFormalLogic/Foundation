import Logic.Logic.System
import Logic.Modal.Standard.Formula

universe u v

namespace LO.Modal.Standard

namespace Kripke

structure Frame where
  World : Type u
  World_nonempty : Nonempty World := by infer_instance
  Rel : World → World → Prop

structure FiniteFrame extends Frame where
  World_finite : Finite World := by infer_instance

instance (F : Frame) : Nonempty F.World := F.World_nonempty

set_option linter.unusedVariables false in
abbrev Frame' (α : Type*) := Frame

set_option linter.unusedVariables false in
abbrev FiniteFrame' (α : Type*) := FiniteFrame

def FiniteFrame.toFrame' {α : Type*} (F : FiniteFrame) : Frame' α := F.toFrame

abbrev Frame.Rel' {F : Frame} (w w' : F.World) := F.Rel w w'
scoped infix:45 " ≺ " => Frame.Rel'

-- MEMO: 様相論理の文脈において`n = 0`のケースの2項関係の合成が`=`として要請されるが一般にはそうではないはず: (`n ≥ 1`で定義するため)
def RelItr {α : Type*} (R : α → α → Prop) : ℕ → α → α → Prop
  | 0 => (· = ·)
  | n + 1 => fun x y ↦ ∃ z, R x z ∧ RelItr R n z y

@[simp] lemma relItr_zero {α : Type*} (R : α → α → Prop) (x y : α) : RelItr R 0 x y ↔ x = y := iff_of_eq rfl

@[simp] lemma relItr_succ {α : Type*} (R : α → α → Prop) (x y : α) :
    RelItr R (n + 1) x y ↔ ∃ z, R x z ∧ RelItr R n z y := iff_of_eq rfl

protected abbrev Frame.RelItr (n : ℕ) {F : Frame} (w w' : F.World) : Prop := RelItr (· ≺ ·) n w w'

scoped notation w:45 " ≺^[" n "] " w':46 => Frame.RelItr n w w'


abbrev FrameClass := Set Frame

set_option linter.unusedVariables false in
abbrev FrameClass' (α : Type*) := FrameClass

class FrameClass.IsNonempty (𝔽 : FrameClass) where
  nonempty : ∃ F, 𝔽 F



abbrev FiniteFrameClass := Set FiniteFrame

set_option linter.unusedVariables false in
abbrev FiniteFrameClass' (α : Type*) := FiniteFrameClass

class FiniteFrameClass.IsNonempty (𝔽 : FiniteFrameClass) where
  nonempty : ∃ F, 𝔽 F


def FrameClass.toFinite (𝔽 : FrameClass) : FiniteFrameClass := { F | F.toFrame ∈ 𝔽 }

postfix:max "ꟳ" => FrameClass.toFinite
instance : Coe FrameClass FiniteFrameClass := ⟨λ 𝔽 ↦ 𝔽ꟳ⟩

instance : Coe (FrameClass' α) (FiniteFrameClass' α) := ⟨λ 𝔽 ↦ 𝔽ꟳ⟩

abbrev FrameProperty := Frame → Prop

abbrev FiniteFrameProperty := FiniteFrame → Prop

-- TODO: 型を上手く合わせられず両方とも`u`に属しているが別にする必要があるだろう
abbrev Valuation (W : Type u) (α : Type u) := W → α → Prop

structure Model (α) where
  Frame : Frame' α
  Valuation : Valuation Frame.World α

abbrev Model.World (M : Model α) := M.Frame.World


end Kripke


variable {α : Type*}

open Standard.Kripke

def Formula.Kripke.Satisfies (M : Kripke.Model α) (w : M.World) : Formula α → Prop
  | atom a  => M.Valuation w a
  | falsum  => False
  | and p q => (Kripke.Satisfies M w p) ∧ (Kripke.Satisfies M w q)
  | or p q  => (Kripke.Satisfies M w p) ∨ (Kripke.Satisfies M w q)
  | imp p q => ¬(Kripke.Satisfies M w p) ∨ (Kripke.Satisfies M w q)
  | box p   => ∀ w', w ≺ w' → (Kripke.Satisfies M w' p)

namespace Formula.Kripke.Satisfies

instance (M : Model α) : Semantics (Formula α) (M.World) := ⟨fun w ↦ Formula.Kripke.Satisfies M w⟩

variable {M : Model α} {w : M.World} {p q : Formula α}

@[simp] protected lemma iff_models : w ⊧ f ↔ Kripke.Satisfies M w f := iff_of_eq rfl

local infix:45 " ⊩ " => Formula.Kripke.Satisfies M

@[simp] lemma atom_def : w ⊩ atom a ↔ M.Valuation w a := by simp [Satisfies];
@[simp] lemma top_def  : w ⊩ ⊤ ↔ True := by simp [Satisfies];
@[simp] lemma bot_def  : w ⊩ ⊥ ↔ False := by simp [Satisfies];
@[simp] lemma and_def  : w ⊩ p ⋏ q ↔ w ⊩ p ∧ w ⊩ q := by simp [Satisfies];
@[simp] lemma or_def   : w ⊩ p ⋎ q ↔ w ⊩ p ∨ w ⊩ q := by simp [Satisfies];
@[simp] lemma imp_def  : w ⊩ p ⟶ q ↔ w ⊩ p → w ⊩ q := by simp [Satisfies, imp_iff_not_or];
@[simp] lemma not_def  : w ⊩ ~p ↔ ¬w ⊩ p := by simp [Satisfies];
@[simp] lemma box_def  : w ⊩ □p ↔ ∀ w', w ≺ w' → w' ⊩ p := by simp [Satisfies];
@[simp] lemma dia_def  : w ⊩ ◇p ↔ ∃ w', w ≺ w' ∧ w' ⊩ p := by simp [Satisfies];

@[simp]
lemma multibox_def : w ⊩ □^[n]p ↔ ∀ v, w ≺^[n] v → v ⊩ p := by
  induction n generalizing w with
  | zero => simp;
  | succ n ih =>
    constructor;
    . intro h w' hww';
      simp at h;
      obtain ⟨v, hwv, hvw'⟩ := hww';
      exact (ih.mp $ h _ hwv) w' hvw';
    . simp;
      intro h w' hww';
      apply ih.mpr;
      intro v hwv;
      exact h v w' hww' hwv;

@[simp]
lemma multidia_def : w ⊩ ◇^[n]p ↔ ∃ v, w ≺^[n] v ∧ v ⊩ p := by
  induction n generalizing w with
  | zero => simp;
  | succ n ih =>
    constructor;
    . intro h;
      obtain ⟨v, hwv, hv⟩ := by simpa using h;
      obtain ⟨x, hvx, hx⟩ := ih.mp hv;
      existsi x;
      constructor;
      . existsi v; simp_all;
      . simpa;
    . simp;
      intro x y hwy hyx hx;
      existsi y;
      constructor;
      . simpa;
      . apply ih.mpr;
        existsi x;
        simp_all;

instance : Semantics.Tarski M.World where
  realize_top := by simp [top_def];
  realize_bot := by simp [bot_def];
  realize_not := by simp [not_def];
  realize_and := by simp [and_def];
  realize_or  := by simp [or_def];
  realize_imp := by simp [imp_def];

lemma mdp (hpq : w ⊧ p ⟶ q) (hp : w ⊧ p) : w ⊧ q := imp_def.mp hpq hp

end Formula.Kripke.Satisfies


def Formula.Kripke.ValidOnModel (M : Model α) (f : Formula α) := ∀ w : M.World, w ⊧ f

instance : Semantics (Formula α) (Model α) := ⟨fun M ↦ Formula.Kripke.ValidOnModel M⟩

namespace Formula.Kripke.ValidOnModel

@[simp] protected lemma iff_models {M : Model α} : M ⊧ f ↔ ValidOnModel M f := iff_of_eq rfl

instance : Semantics.Bot (Model α) where
  realize_bot _ := by simp [ValidOnModel];

end Formula.Kripke.ValidOnModel


def Formula.Kripke.ValidOnFrame (F : Frame) (f : Formula α) := ∀ V, (Model.mk F V) ⊧ f

instance : Semantics (Formula α) (Frame' α) := ⟨fun F ↦ Formula.Kripke.ValidOnFrame F⟩

namespace Formula.Kripke.ValidOnFrame

@[simp] protected lemma models_iff {F : Frame' α} : F ⊧ f ↔ ValidOnFrame F f := iff_of_eq rfl

instance : Semantics.Bot (Frame' α) where
  realize_bot _ := by simp [ValidOnFrame];

end Formula.Kripke.ValidOnFrame


@[simp] def Formula.Kripke.ValidOnFrameClass (𝔽 : FrameClass) (f : Formula α) := ∀ (F : Frame' α), F ∈ 𝔽 → F ⊧ f

instance : Semantics (Formula α) (FrameClass' α) := ⟨fun 𝔽 ↦ Formula.Kripke.ValidOnFrameClass 𝔽⟩

namespace Formula.Kripke.ValidOnFrameClass

@[simp] protected lemma models_iff {𝔽 : FrameClass' α} : 𝔽 ⊧ f ↔ Formula.Kripke.ValidOnFrameClass 𝔽 f := iff_of_eq rfl

end Formula.Kripke.ValidOnFrameClass

def Kripke.AxiomSetFrameClass (Ax : AxiomSet α) : FrameClass' α := { (F : Frame' α) | F ⊧* Ax }
notation "𝔽(" Ax ")" => Kripke.AxiomSetFrameClass Ax


@[simp] def Formula.Kripke.ValidOnFiniteFrameClass (𝔽 : FiniteFrameClass) (f : Formula α) := ∀ (F : FiniteFrame' α), 𝔽 F → F.toFrame' ⊧ f

instance : Semantics (Formula α) (FiniteFrameClass' α) := ⟨fun 𝔽 ↦ Formula.Kripke.ValidOnFiniteFrameClass 𝔽⟩

namespace Formula.Kripke.ValidOnFiniteFrameClass

@[simp] protected lemma models_iff {𝔽 : FiniteFrameClass' α} : 𝔽 ⊧ f ↔ Formula.Kripke.ValidOnFiniteFrameClass 𝔽 f := iff_of_eq rfl

end Formula.Kripke.ValidOnFiniteFrameClass

def Kripke.AxiomSetFiniteFrameClass (Ax : AxiomSet α) : FiniteFrameClass' α := { (F : FiniteFrame' α) | F.toFrame' ⊧* Ax }
notation "𝔽ꟳ(" Ax ")" => Kripke.AxiomSetFiniteFrameClass Ax


open Formula.Kripke

variable {Ax : AxiomSet α}

namespace Kripke

lemma validOnAxiomSetFrameClass_axiom (h : p ∈ Ax) : 𝔽(Ax) ⊧ p := by intro F hF; exact hF.realize h;

/-- Every frame that valid all axioms in `Ax` satisfy frame property `P` -/
class Definability (Ax : AxiomSet α) (P : FrameProperty) where
  defines : ∀ (F : Frame' α), F ⊧* Ax ↔ P F

instance Definability.union (definability₁ : Definability Ax₁ P₁) (definability₂ : Definability Ax₂ P₂) : Definability (Ax₁ ∪ Ax₂) (λ F => P₁ F ∧ P₂ F) where
  defines F := by
    constructor;
    . intro h;
      simp only [Semantics.RealizeSet.union_iff] at h;
      constructor;
      . exact Definability.defines F |>.mp h.1;
      . exact Definability.defines F |>.mp h.2;
    . intro h;
      simp only [Semantics.RealizeSet.union_iff];
      constructor;
      . apply Definability.defines F |>.mpr h.1;
      . apply Definability.defines F |>.mpr h.2;

lemma iff_definability_memAxiomSetFrameClass (definability : Definability Ax P) : ∀ {F : Frame' α}, 𝔽(Ax) F ↔ P F := by
  apply definability.defines;


/-- Every **finite** frame that valid all axioms in `Ax` satisfy **finite** frame property `P` -/
class FiniteDefinability (Ax : AxiomSet α) (P : FiniteFrameProperty) where
  fin_defines : ∀ (F : FiniteFrame' α), F.toFrame' ⊧* Ax ↔ P F

instance FiniteDefinability.union (definability₁ : FiniteDefinability Ax₁ P₁) (definability₂ : FiniteDefinability Ax₂ P₂) : FiniteDefinability (Ax₁ ∪ Ax₂) (λ F => P₁ F ∧ P₂ F) where
  fin_defines F := by
    constructor;
    . intro h;
      simp only [Semantics.RealizeSet.union_iff] at h;
      constructor;
      . exact FiniteDefinability.fin_defines F |>.mp h.1;
      . exact FiniteDefinability.fin_defines F |>.mp h.2;
    . intro h;
      simp only [Semantics.RealizeSet.union_iff];
      constructor;
      . apply FiniteDefinability.fin_defines F |>.mpr h.1;
      . apply FiniteDefinability.fin_defines F |>.mpr h.2;

lemma iff_finiteDefinability_memFiniteFrameClass (definability : FiniteDefinability Ax P) : ∀ {F : FiniteFrame' α}, 𝔽ꟳ(Ax) F ↔ P F := by
  apply definability.fin_defines;

instance [definability : Definability Ax P] : FiniteDefinability Ax (λ F => P F.toFrame) where
  fin_defines F := by
    constructor;
    . exact iff_definability_memAxiomSetFrameClass definability |>.mp;
    . exact iff_definability_memAxiomSetFrameClass definability |>.mpr;

instance {𝔽 : FrameClass' α} [ne : FiniteFrameClass.IsNonempty 𝔽ꟳ] : FrameClass.IsNonempty 𝔽  where
  nonempty := by
    obtain ⟨F, hF⟩ := ne;
    existsi F.toFrame;
    exact hF;

instance [ne : FiniteFrameClass.IsNonempty 𝔽ꟳ(Ax)] : FrameClass.IsNonempty 𝔽(Ax) where
  nonempty := by obtain ⟨F, hF⟩ := ne; existsi F.toFrame; exact hF;

end Kripke

section K

instance AxiomSet.K.definability : Definability (α := α) 𝗞 (λ _ => True) where
  defines := by
    simp [ValidOnFrame, ValidOnModel, System.Axioms.K];
    intros; subst_vars;
    simp_all;

instance AxiomSet.K.finiteDefinability : FiniteDefinability (α := α) 𝗞 (λ _ => True) where
  fin_defines := by
    simp [ValidOnFrame, ValidOnModel, System.Axioms.K];
    intros; subst_vars;
    simp_all;

instance [definability : Definability Ax P] : Definability (𝗞 ∪ Ax) P := by simpa using Definability.union AxiomSet.K.definability definability;

instance [definability : FiniteDefinability Ax P] : FiniteDefinability (𝗞 ∪ Ax) P := by simpa using FiniteDefinability.union AxiomSet.K.finiteDefinability definability;

instance : FiniteFrameClass.IsNonempty (𝔽ꟳ(𝗞) : FiniteFrameClass' α) where
  nonempty := by
    existsi { World := PUnit, Rel := λ _ _ => True };
    apply iff_finiteDefinability_memFiniteFrameClass AxiomSet.K.finiteDefinability |>.mpr;
    trivial;

instance : FrameClass.IsNonempty (𝔽(𝗞) : FrameClass' α) := inferInstance

end K

end LO.Modal.Standard
