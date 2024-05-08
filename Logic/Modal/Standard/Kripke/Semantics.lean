import Logic.Logic.System
import Logic.Modal.Standard.Formula

namespace LO.Modal.Standard

namespace Kripke

variable (W α : Type*)

set_option linter.unusedVariables false in
abbrev Frame (α : Type*) := W → W → Prop

@[simp]
def Multiframe {W α} (F : Frame W α) : ℕ → W → W → Prop
| 0 => (· = ·)
| n + 1 => λ x y => ∃ z, (F x z ∧ Multiframe F n z y)

notation:max F "^[" n "]" => Multiframe F n

abbrev Valuation := W → α → Prop

structure Model where
  frame : Frame W α
  valuation : Valuation W α

abbrev FrameClass := Set (Frame W α)

end Kripke


variable {W α : Type*}

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

lemma iff_models : (M, w) ⊧ f ↔ Formula.Kripke.Satisfies M w f := iff_of_eq rfl

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

@[simp] lemma iff_models : M ⊧ f ↔ Formula.Kripke.ValidOnModel M f := iff_of_eq rfl

instance [Inhabited W] : Semantics.Bot (Model W α) where
  realize_bot _ := by simp [ValidOnModel];

end Formula.Kripke.ValidOnModel


def Formula.Kripke.ValidOnFrame (F : Frame W α) (f : Formula α) := ∀ V, (Model.mk F V) ⊧ f

instance : Semantics (Formula α) (Frame W α) := ⟨fun F ↦ Formula.Kripke.ValidOnFrame F⟩

namespace Formula.Kripke.ValidOnFrame

@[simp] lemma models_iff : F ⊧ f ↔ Formula.Kripke.ValidOnFrame F f := iff_of_eq rfl

instance [Inhabited W] : Semantics.Bot (Frame W α) where
  realize_bot _ := by simp [ValidOnFrame];

end Formula.Kripke.ValidOnFrame


def Formula.Kripke.ValidOnFrameClass (𝔽 : FrameClass W α) (f : Formula α) := ∀ F ∈ 𝔽, F ⊧ f

instance : Semantics (Formula α) (FrameClass W α) := ⟨fun 𝔽 ↦ Formula.Kripke.ValidOnFrameClass 𝔽⟩

namespace Formula.Kripke.ValidOnFrameClass

@[simp] lemma models_iff : 𝔽 ⊧ f ↔ Formula.Kripke.ValidOnFrameClass 𝔽 f := iff_of_eq rfl

end Formula.Kripke.ValidOnFrameClass


structure Kripke.AxiomSetFrameClass (W) {α} (Λ : AxiomSet α) where
  frameclass : FrameClass W α
  spec : F ∈ frameclass ↔ F ⊧* Λ

instance : Inhabited (Kripke.AxiomSetFrameClass W Λ) := ⟨⟨{ F | F ⊧* Λ }, by simp;⟩⟩

variable {Λ : AxiomSet α}


def Formula.Kripke.ValidOnAxiomSetFrameClass (𝔽 : AxiomSetFrameClass W Λ) (f : Formula α) := Formula.Kripke.ValidOnFrameClass 𝔽.frameclass f

instance : Semantics (Formula α) (AxiomSetFrameClass W Λ) := ⟨fun 𝔽 ↦ Formula.Kripke.ValidOnAxiomSetFrameClass 𝔽⟩

namespace Formula.Kripke.ValidOnAxiomSetFrameClass

@[simp] lemma models_iff : 𝔽 ⊧ p ↔ Formula.Kripke.ValidOnAxiomSetFrameClass 𝔽 p := iff_of_eq rfl

end Formula.Kripke.ValidOnAxiomSetFrameClass


namespace Kripke

lemma validOnAxiomSetFrameClass_axiom {𝔽 : AxiomSetFrameClass W Λ} (h : p ∈ Λ) : 𝔽 ⊧ p := by
  intro F hF;
  exact 𝔽.spec.mp hF |>.realize h;

class AxiomSetDefinability (W) (Λ : AxiomSet α) (P : Frame W α → Prop) where
  defines : ∀ F, P F ↔ F ⊧* Λ

lemma iff_definability_memAxiomSetFrameClass (definability : AxiomSetDefinability W Λ P) {𝔽 : AxiomSetFrameClass W Λ} : ∀ {F}, P F ↔ F ∈ 𝔽.frameclass := by
  simp [AxiomSetFrameClass.spec];
  apply definability.defines;


@[simp]
instance AxiomSet.K.definability : AxiomSetDefinability W (𝐊 : AxiomSet α) (λ _ => True) where
  defines := by
    simp_all;
    intros; subst_vars;
    simp [ValidOnFrame, ValidOnModel, Satisfies];
    intros; simp_all;

instance {𝔽 : AxiomSetFrameClass W (𝐊 : AxiomSet α)} : Set.Nonempty 𝔽.frameclass := by
  existsi (λ _ _ => True);
  apply iff_definability_memAxiomSetFrameClass AxiomSet.K.definability |>.mp;
  simp;

/-
instance AxiomSetDefinability.union [def₁ : AxiomSetDefinability W Λ₁] [def₂ : AxiomSetDefinability W Λ₂] : AxiomSetDefinability W (Λ₁ ∪ Λ₂) where
  property F :=def₁.property F ∧ def₂.property F
  defines F := by
    constructor;
    . sorry;
    . simp_all [AxiomSetDefinability.spec];
-/

instance [dΛ : AxiomSetDefinability W Λ P] : AxiomSetDefinability W (𝐊 ∪ Λ) P where
  defines F := by
    constructor;
    . intro h;
      simp only [Semantics.RealizeSet.union_iff];
      constructor;
      . apply AxiomSet.K.definability.defines F |>.mp; simp_all;
      . exact dΛ.defines F |>.mp h;
    . intro h;
      simp only [Semantics.RealizeSet.union_iff] at h;
      exact dΛ.defines F |>.mpr h.2;

end LO.Modal.Standard.Kripke
