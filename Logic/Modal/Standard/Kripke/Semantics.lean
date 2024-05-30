import Logic.Logic.System
import Logic.Modal.Standard.Formula

universe u

namespace LO.Modal.Standard

namespace Kripke

-- variable (W α : Type*) [Inhabited W]

set_option linter.unusedVariables false in
abbrev Frame (W) (α : Type*) [Inhabited W] := W → W → Prop

@[simp]
def Multiframe {W α} [Inhabited W] (F : Frame W α) : ℕ → W → W → Prop
| 0 => (· = ·)
| n + 1 => λ x y => ∃ z, (F x z ∧ Multiframe F n z y)

notation:max F "^[" n "]" => Multiframe F n

abbrev Valuation (W α) := W → α → Prop

structure Model (W α) [Inhabited W] where
  frame : Frame W α
  valuation : Valuation W α

abbrev FrameClass (α) := ∀ (W : Type*), [Inhabited W] → Frame W α → Prop

abbrev FiniteFrameClass (α) := ∀ (W : Type*), [Inhabited W] → [Finite W] → Frame W α → Prop

def FrameClass.toFinite (𝔽 : FrameClass α) : FiniteFrameClass α := λ _ _ _ F => 𝔽 _ F
postfix:max "ꟳ" => FrameClass.toFinite
instance : Coe (FrameClass α) (FiniteFrameClass α) := ⟨λ 𝔽 ↦ 𝔽ꟳ⟩

class FrameClass.Nonempty (𝔽 : FrameClass α) where
  W : Type*
  W_inhabited : Inhabited W
  existsi : ∃ F, 𝔽 W F

class FiniteFrameClass.Nonempty (𝔽 : FiniteFrameClass α) where
  W : Type*
  W_inhabited : Inhabited W := by infer_instance
  W_finite : Finite W := by infer_instance
  existsi : ∃ F, 𝔽 W F

abbrev FrameProperty (α : Type u) := ∀ {W : Type u}, [Inhabited W] → Frame W α → Prop

abbrev FiniteFrameProperty (α : Type u) := ∀ {W : Type u}, [Inhabited W] → [Finite W] → Frame W α → Prop

end Kripke


variable {W α : Type*} [Inhabited W]

open Standard.Kripke

def Formula.Kripke.Satisfies (M : Kripke.Model W α) (w : W) : Formula α → Prop
  | atom a  => M.valuation w a
  | falsum  => False
  | and p q => (Satisfies M w p) ∧ (Satisfies M w q)
  | or p q  => (Satisfies M w p) ∨ (Satisfies M w q)
  | imp p q => ¬(Satisfies M w p) ∨ (Satisfies M w q)
  | box p   => ∀ w', M.frame w w' → (Satisfies M w' p)

instance : Semantics (Formula α) ((Model W α) × W) := ⟨fun ⟨M, w⟩ ↦ Formula.Kripke.Satisfies M w⟩

open Formula.Kripke

namespace Formula.Kripke.Satisfies

lemma iff_models {M : Model W α} : (M, w) ⊧ f ↔ Formula.Kripke.Satisfies M w f := iff_of_eq rfl

instance : Semantics.Tarski ((Model W α) × W) where
  realize_top := by simp [iff_models, Satisfies]
  realize_bot := by simp [iff_models, Satisfies]
  realize_not := by simp [iff_models, Satisfies]
  realize_and := by simp [iff_models, Satisfies]
  realize_or := by simp [iff_models, Satisfies]
  realize_imp := by simp [iff_models, Satisfies, imp_iff_not_or]

variable {M : Model W α} {w : W} {p q : Formula α}

@[simp] lemma atom_def : (M, w) ⊧ atom a ↔ M.valuation w a := by simp [iff_models, Satisfies];

@[simp] lemma box_def : (M, w) ⊧ □p ↔ ∀ w', M.frame w w' → (M, w') ⊧ p := by simp [iff_models, Satisfies];
@[simp] lemma dia_def : (M, w) ⊧ ◇p ↔ ∃ w', M.frame w w' ∧ (M, w') ⊧ p := by simp [iff_models, Satisfies];

@[simp]
lemma multibox_def : ((M, w) ⊧ □^[n]p) ↔ (∀ v, M.frame^[n] w v → ((M, v) ⊧ p)) := by
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
lemma multidia_def : ((M, w) ⊧ ◇^[n]p) ↔ ∃ v, M.frame^[n] w v ∧ ((M, v) ⊧ p) := by
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

end Formula.Kripke.Satisfies


def Formula.Kripke.ValidOnModel (M : Model W α) (f : Formula α) := ∀ w : W, (M, w) ⊧ f

instance : Semantics (Formula α) (Model W α) := ⟨fun M ↦ Formula.Kripke.ValidOnModel M⟩

namespace Formula.Kripke.ValidOnModel

@[simp] protected lemma iff_models {M : Model W α} : M ⊧ f ↔ Formula.Kripke.ValidOnModel M f := iff_of_eq rfl

instance [Inhabited W] : Semantics.Bot (Model W α) where
  realize_bot _ := by simp [ValidOnModel];

end Formula.Kripke.ValidOnModel


def Formula.Kripke.ValidOnFrame (F : Frame W α) (f : Formula α) := ∀ V, (Model.mk F V) ⊧ f

instance : Semantics (Formula α) (Frame W α) := ⟨fun F ↦ Formula.Kripke.ValidOnFrame F⟩

namespace Formula.Kripke.ValidOnFrame

@[simp] protected lemma models_iff {F : Frame W α} : F ⊧ f ↔ Formula.Kripke.ValidOnFrame F f := iff_of_eq rfl

instance [Inhabited W] : Semantics.Bot (Frame W α) where
  realize_bot _ := by simp [ValidOnFrame];

end Formula.Kripke.ValidOnFrame


@[simp] def Formula.Kripke.ValidOnFrameClass (𝔽 : FrameClass α) (f : Formula α) := ∀ W, [Inhabited W] → ∀ F, 𝔽 W F → F ⊧ f

instance : Semantics (Formula α) (FrameClass α) := ⟨fun 𝔽 ↦ Formula.Kripke.ValidOnFrameClass 𝔽⟩

namespace Formula.Kripke.ValidOnFrameClass

@[simp] protected lemma models_iff {𝔽 : FrameClass α} : 𝔽 ⊧ f ↔ Formula.Kripke.ValidOnFrameClass 𝔽 f := iff_of_eq rfl

end Formula.Kripke.ValidOnFrameClass

def Kripke.AxiomSetFrameClass (Ax : AxiomSet α) : FrameClass α := λ _ _ F => F ⊧* Ax
notation "𝔽(" Ax ")" => Kripke.AxiomSetFrameClass Ax


@[simp] def Formula.Kripke.ValidOnFiniteFrameClass (𝔽 : FiniteFrameClass α) (f : Formula α) := ∀ W, [Inhabited W] → [Finite W] → ∀ F, 𝔽 W F → F ⊧ f

instance : Semantics (Formula α) (FiniteFrameClass α) := ⟨fun 𝔽 ↦ Formula.Kripke.ValidOnFiniteFrameClass 𝔽⟩

namespace Formula.Kripke.ValidOnFiniteFrameClass

@[simp] protected lemma models_iff {𝔽 : FiniteFrameClass α} : 𝔽 ⊧ f ↔ Formula.Kripke.ValidOnFiniteFrameClass 𝔽 f := iff_of_eq rfl

end Formula.Kripke.ValidOnFiniteFrameClass

def Kripke.AxiomSetFiniteFrameClass (Ax : AxiomSet α) : FiniteFrameClass α := λ _ _ _ F => F ⊧* Ax
notation "𝔽ꟳ(" Ax ")" => Kripke.AxiomSetFiniteFrameClass Ax

variable {Ax : AxiomSet α}

namespace Kripke

lemma validOnAxiomSetFrameClass_axiom (h : p ∈ Ax) : 𝔽(Ax) ⊧ p := by
  intro _ _ _ hF;
  exact hF.realize h;


/-- Every frame that valid all axioms in `Ax` satisfy frame property `P` -/
class Definability (Ax : AxiomSet α) (P : FrameProperty α) where
  defines : ∀ W, [Inhabited W] → ∀ F, F ⊧* Ax ↔ @P W _ F

instance Definability.union [definability₁ : Definability Ax₁ P₁] [definability₂ : Definability Ax₂ P₂] : Definability (Ax₁ ∪ Ax₂) (λ F => P₁ F ∧ P₂ F) where
  defines W _ F := by
    constructor;
    . intro h;
      simp only [Semantics.RealizeSet.union_iff] at h;
      constructor;
      . exact Definability.defines W F |>.mp h.1;
      . exact Definability.defines W F |>.mp h.2;
    . intro h;
      simp only [Semantics.RealizeSet.union_iff];
      constructor;
      . apply Definability.defines W F |>.mpr h.1;
      . apply Definability.defines W F |>.mpr h.2;

lemma iff_definability_memAxiomSetFrameClass (definability : Definability Ax P) : ∀ {W}, [Inhabited W] → ∀ {F}, 𝔽(Ax) W F ↔ P F := by
  apply definability.defines;


/-- Every **finite** frame that valid all axioms in `Ax` satisfy **finite** frame property `P` -/
class FiniteDefinability (Ax : AxiomSet α) (P : FiniteFrameProperty α) where
  fin_defines : ∀ W, [Inhabited W] → [Finite W] → ∀ F, F ⊧* Ax ↔ @P W _ _ F

instance FiniteDefinability.union [definability₁ : FiniteDefinability Ax₁ P₁] [definability₂ : FiniteDefinability Ax₂ P₂] : FiniteDefinability (Ax₁ ∪ Ax₂) (λ F => P₁ F ∧ P₂ F) where
  fin_defines W _ _ F := by
    constructor;
    . intro h;
      simp only [Semantics.RealizeSet.union_iff] at h;
      constructor;
      . exact FiniteDefinability.fin_defines W F |>.mp h.1;
      . exact FiniteDefinability.fin_defines W F |>.mp h.2;
    . intro h;
      simp only [Semantics.RealizeSet.union_iff];
      constructor;
      . apply FiniteDefinability.fin_defines W F |>.mpr h.1;
      . apply FiniteDefinability.fin_defines W F |>.mpr h.2;

lemma iff_finiteDefinability_memFiniteFrameClass (definability : FiniteDefinability Ax P) : ∀ {W}, [Inhabited W] → [Finite W] → ∀ {F}, 𝔽ꟳ(Ax) W F ↔ P F := by
  apply definability.fin_defines;

instance [definability : Definability Ax P] : FiniteDefinability Ax (λ F => @P _ _ F) where
  fin_defines W _ _ F := by
    constructor;
    . exact iff_definability_memAxiomSetFrameClass definability |>.mp;
    . exact iff_definability_memAxiomSetFrameClass definability |>.mpr;

/-- Nonemptiness of frame class from finite frame class -/
instance {𝔽 : FrameClass α} [ne : FiniteFrameClass.Nonempty (α := α) 𝔽] : FrameClass.Nonempty (α := α) 𝔽 where
  W := ne.W
  W_inhabited := ne.W_inhabited
  existsi := by
    obtain ⟨F, hF⟩ := ne.existsi;
    existsi F;
    assumption;

end Kripke

section K

instance AxiomSet.K.definability : Definability (α := α) 𝗞 (λ _ => True) where
  defines := by
    simp_all;
    intros; subst_vars;
    simp [ValidOnFrame, ValidOnModel, Satisfies];
    intros; simp_all;

instance AxiomSet.K.finiteDefinability : FiniteDefinability (α := α) 𝗞 (λ _ => True) := inferInstance

instance [definability : Definability Ax P] : Definability (𝗞 ∪ Ax) P := by simpa using Definability.union (definability₁ := AxiomSet.K.definability);

instance [definability : FiniteDefinability Ax P] : FiniteDefinability (𝗞 ∪ Ax) P := by simpa using FiniteDefinability.union (definability₁ := AxiomSet.K.finiteDefinability);

instance : FiniteFrameClass.Nonempty (α := α) 𝔽(𝗞)ꟳ where
  W := PUnit
  existsi := by
    existsi (λ _ _ => True);
    apply iff_finiteDefinability_memFiniteFrameClass AxiomSet.K.finiteDefinability |>.mpr;
    trivial;

instance : FrameClass.Nonempty (α := α) 𝔽(𝗞) := inferInstance

/- TODO:
instance [definability : FiniteDefinability Ax P] [nonempty : FiniteFrameClass.Nonempty (α := α) 𝔽(Ax)ꟳ] : FiniteFrameClass.Nonempty 𝔽((𝐊 ∪ Ax))ꟳ where
  W := nonempty.W
  W_inhabited := nonempty.W_inhabited
  W_finite := nonempty.W_finite
  existsi := by sorry;
-/

end K

end LO.Modal.Standard
