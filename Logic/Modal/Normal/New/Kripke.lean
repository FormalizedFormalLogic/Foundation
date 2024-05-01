import Logic.Logic.System
import Logic.Modal.Normal.Formula
import Logic.Modal.Normal.Axioms

namespace LO.Modal.Normal

namespace Kripkean

variable (W α : Type*)

set_option linter.unusedVariables false in
abbrev Frame (α : Type*) := W → W → Prop

@[simp]
def Multiframe (R : Frame W α) : ℕ → W → W → Prop
| 0 => (· = ·)
| n + 1 => λ x y => ∃ z, (R x z ∧ Multiframe R n z y)

notation:max F "[" n "]" => Multiframe F n

abbrev Valuation := W → α → Prop

structure Model where
  frame : Frame W α
  valuation : Valuation W α

abbrev FrameClass := Set (Frame W α)

end Kripkean

variable {W α : Type*}

open Normal.Kripkean

def Formula.Kripkean.Satisfies (M : Kripkean.Model W α) (w : W) : Formula α → Prop
  | atom a  => M.valuation w a
  | falsum  => False
  | and p q => (Satisfies M w p) ∧ (Satisfies M w q)
  | or p q  => (Satisfies M w p) ∨ (Satisfies M w q)
  | imp p q => ¬(Satisfies M w p) ∨ (Satisfies M w q)
  | box p   => ∀ w', M.frame w w' → (Satisfies M w' p)

instance : Semantics (Formula α) ((Model W α) × W) := ⟨fun ⟨M, w⟩ ↦ Formula.Kripkean.Satisfies M w⟩

open Formula.Kripkean

@[simp] lemma models_iff_satisfies : (M, w) ⊧ f ↔ Formula.Kripkean.Satisfies M w f := iff_of_eq rfl

instance : Semantics.Tarski ((Model W α) × W) where
  realize_top := by simp [Satisfies]
  realize_bot := by simp [Satisfies]
  realize_not := by simp [Satisfies]
  realize_and := by simp [Satisfies]
  realize_or := by simp [Satisfies]
  realize_imp := by simp [Satisfies, imp_iff_not_or]

namespace Formula.Kripkean.Satisfies

variable {M : Model W α} {w : W} {p q : Formula α}

@[simp] lemma box_def : (M, w) ⊧ □p ↔ ∀ w', M.frame w w' → (M, w') ⊧ p := by simp [models_iff_satisfies, Satisfies];
@[simp] lemma dia_def : (M, w) ⊧ ◇p ↔ ∃ w', M.frame w w' ∧ (M, w') ⊧ p := by simp [models_iff_satisfies, Satisfies];

end Formula.Kripkean.Satisfies


def Formula.Kripkean.ValidOnModel (M : Model W α) (f : Formula α) := ∀ w : W, (M, w) ⊧ f

instance : Semantics (Formula α) (Model W α) := ⟨fun M ↦ Formula.Kripkean.ValidOnModel M⟩

@[simp] lemma models_iff_validOnModel : M ⊧ f ↔ Formula.Kripkean.ValidOnModel M f := iff_of_eq rfl

instance [Inhabited W] : Semantics.Bot (Model W α) where
  realize_bot _ := by simp [ValidOnModel];


def Formula.Kripkean.ValidOnFrame (F : Frame W α) (f : Formula α) := ∀ V, (Model.mk F V) ⊧ f

instance : Semantics (Formula α) (Frame W α) := ⟨fun F ↦ Formula.Kripkean.ValidOnFrame F⟩

@[simp] lemma models_iff_validOnFrame : F ⊧ f ↔ Formula.Kripkean.ValidOnFrame F f := iff_of_eq rfl

instance [Inhabited W] : Semantics.Bot (Frame W α) where
  realize_bot _ := by simp [ValidOnFrame];


def Formula.Kripkean.ValidOnFrameClass (𝔽 : FrameClass W α) (f : Formula α) := ∀ F ∈ 𝔽, F ⊧ f

instance : Semantics (Formula α) (FrameClass W α) := ⟨fun 𝔽 ↦ Formula.Kripkean.ValidOnFrameClass 𝔽⟩

@[simp] lemma models_iff_validOnFrameClass : 𝔽 ⊧ f ↔ Formula.Kripkean.ValidOnFrameClass 𝔽 f := iff_of_eq rfl


def AxiomSetFrameClass (Λ : AxiomSet α) : FrameClass W α := { F | F ⊧* Λ }
notation "𝔽(" Λ ")" => AxiomSetFrameClass Λ

lemma union_AxiomSetFrameClass : (𝔽(Λ₁ ∪ Λ₂) : FrameClass W α) = 𝔽(Λ₁) ∩ 𝔽(Λ₂) := by simp [AxiomSetFrameClass]; rfl;

lemma validOnAxiomSetFrameClass_axiom (hp : p ∈ Λ) : (𝔽(Λ) : FrameClass W α) ⊧ p := by intro F hF; exact hF.realize hp;

class AxiomSetDefinability (W) (Λ : AxiomSet α) where
  property : Frame W α → Prop
  spec : ∀ {F}, property F ↔ F ⊧* Λ

lemma AxiomSetDefinability.spec' [h : AxiomSetDefinability W Λ] : ∀ {F}, h.property F ↔ F ∈ 𝔽(Λ) := h.spec

instance [h₁ : AxiomSetDefinability W Λ₁] [h₂ : AxiomSetDefinability W Λ₂] : AxiomSetDefinability W (Λ₁ ∪ Λ₂) where
  property := λ F => h₁.property F ∧ h₂.property F
  spec := by intro F; constructor <;> simp_all [AxiomSetDefinability.spec];

instance : AxiomSetDefinability W (𝐊 : AxiomSet α) where
  property _ := True
  spec := by
    simp_all;
    intros; subst_vars;
    simp [ValidOnFrame, ValidOnModel, Satisfies];
    intros; simp_all;

@[simp]
instance : Set.Nonempty (𝔽(𝐊) : FrameClass W α) := by
  existsi (λ _ _ => True);
  apply AxiomSetDefinability.spec'.mp;
  trivial;

variable [Inhabited W]

lemma meaningful_of_nonempty_frameclass {𝔽 : FrameClass W α} (h : Set.Nonempty 𝔽 := by simp) : Semantics.Meaningful 𝔽 where
  exists_unrealize := by
    simp [ValidOnFrameClass, ValidOnFrame, ValidOnModel];
    obtain ⟨F, hF⟩ := h;
    existsi ⊥, F;
    constructor;
    . simp_all;
    . simp [Satisfies];

end LO.Modal.Normal
