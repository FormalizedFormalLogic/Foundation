import Logic.Logic.System
import Logic.Modal.Normal.Formula
import Logic.Modal.Normal.Axioms

namespace LO.Semantics

variable {M F : Type*} [LogicalConnective F] [StandardModalLogicalConnective F] [𝓢 : Semantics F M]

variable (𝓜 : M) (p q : F)

variable (M)

/--
  Modeling `LO.System.Minimal`
-/
class HilbertMinimal where
  realize_mdp {𝓜 : M} {p q : F} : 𝓜 ⊧ p ⟶ q → 𝓜 ⊧ p → 𝓜 ⊧ q
  realize_verum {𝓜 : M} : 𝓜 ⊧ ⊤
  realize_imply₁ {𝓜 : M} {p q : F} : 𝓜 ⊧ p ⟶ q ⟶ p
  realize_imply₂ {𝓜 : M} {p q r : F} : 𝓜 ⊧ (p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r
  realize_conj₁ {𝓜 : M} {p q : F} : 𝓜 ⊧ p ⋏ q ⟶ p
  realize_conj₂ {𝓜 : M} {p q : F} : 𝓜 ⊧ p ⋏ q ⟶ q
  realize_conj₃ {𝓜 : M} {p q : F} : 𝓜 ⊧ p ⟶ q ⟶ p ⋏ q
  realize_disj₁ {𝓜 : M} {p q : F} : 𝓜 ⊧ p ⟶ p ⋎ q
  realize_disj₂ {𝓜 : M} {p q : F} : 𝓜 ⊧ q ⟶ p ⋎ q
  realize_disj₃ {𝓜 : M} {p q r : F} : 𝓜 ⊧ (p ⟶ r) ⟶ (q ⟶ r) ⟶ p ⋎ q ⟶ r

/--
  Modeling `LO.System.Classical`
-/
class HilbertClassical extends HilbertMinimal M where
  realize_dne {𝓜 : M} {p : F} : 𝓜 ⊧ ~~p ⟶ p

class Necessitation where
  realize_nec {𝓜 : M} {p : F} : 𝓜 ⊧ p → 𝓜 ⊧ □p

instance [Tarski M] : HilbertClassical M where
  realize_mdp := by simp_all;
  realize_verum := by simp_all;
  realize_dne := by simp_all
  realize_imply₁ := by simp_all;
  realize_imply₂ := by simp_all;
  realize_conj₁ := by simp_all;
  realize_conj₂ := by simp_all;
  realize_conj₃ := by simp_all;
  realize_disj₁ := by simp_all;
  realize_disj₂ := by simp_all;
  realize_disj₃ := by
    intros;
    simp;
    intro hpr hqr hpq;
    cases hpq;
    . apply hpr; assumption;
    . apply hqr; assumption;

end LO.Semantics


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

open Semantics.HilbertMinimal Semantics.HilbertClassical Semantics.Necessitation

instance [Inhabited W] : Semantics.Bot (Model W α) where
  realize_bot _ := by simp [ValidOnModel];

instance : Semantics.HilbertClassical (Model W α) where
  realize_mdp := by intro M p q hpq hp w; have := hpq w; have := hp w; simp_all [models_iff_satisfies, Satisfies];
  realize_verum _  := by apply realize_verum;
  realize_imply₁ _ := by apply realize_imply₁;
  realize_imply₂ _ := by apply realize_imply₂;
  realize_conj₁ _  := by apply realize_conj₁;
  realize_conj₂ _  := by apply realize_conj₂;
  realize_conj₃ _  := by apply realize_conj₃;
  realize_disj₁ _  := by apply realize_disj₁;
  realize_disj₂ _  := by apply realize_disj₂;
  realize_disj₃ _  := by apply realize_disj₃;
  realize_dne _    := by apply realize_dne;

instance : Semantics.Necessitation (Model W α) where
  realize_nec := by
    simp [ValidOnModel, Satisfies];
    intro M p hp _ _ _;
    apply hp;


def Formula.Kripkean.ValidOnFrame (F : Frame W α) (f : Formula α) := ∀ V, (Model.mk F V) ⊧ f

instance : Semantics (Formula α) (Frame W α) := ⟨fun F ↦ Formula.Kripkean.ValidOnFrame F⟩

@[simp] lemma models_iff_validOnFrame : F ⊧ f ↔ Formula.Kripkean.ValidOnFrame F f := iff_of_eq rfl

instance [Inhabited W] : Semantics.Bot (Frame W α) where
  realize_bot _ := by simp [ValidOnFrame];

instance : Semantics.HilbertClassical (Frame W α) where
  realize_mdp hpq hp := by intro V; exact realize_mdp (hpq V) (hp V);
  realize_verum _ _  := by apply realize_verum;
  realize_imply₁ _ _ := by apply realize_imply₁;
  realize_imply₂ _ _ := by apply realize_imply₂;
  realize_conj₁ _ _  := by apply realize_conj₁;
  realize_conj₂ _ _  := by apply realize_conj₂;
  realize_conj₃ _ _  := by apply realize_conj₃;
  realize_disj₁ _ _  := by apply realize_disj₁;
  realize_disj₂ _ _  := by apply realize_disj₂;
  realize_disj₃ _ _  := by apply realize_disj₃;
  realize_dne _ _    := by apply realize_dne;

instance : Semantics.Necessitation (Frame W α) where
  realize_nec hp := by intro V; exact realize_nec (hp V);


def Formula.Kripkean.ValidOnFrameClass (𝔽 : FrameClass W α) (f : Formula α) := ∀ F ∈ 𝔽, F ⊧ f

instance : Semantics (Formula α) (FrameClass W α) := ⟨fun 𝔽 ↦ Formula.Kripkean.ValidOnFrameClass 𝔽⟩

@[simp] lemma models_iff_validOnFrameClass : 𝔽 ⊧ f ↔ Formula.Kripkean.ValidOnFrameClass 𝔽 f := iff_of_eq rfl

instance : Semantics.HilbertClassical (FrameClass W α) where
  realize_mdp hpq hp := by intro F hF; exact realize_mdp (hpq F hF) (hp F hF);
  realize_verum _ _  := by apply realize_verum;
  realize_imply₁ _ _ := by apply realize_imply₁;
  realize_imply₂ _ _ := by apply realize_imply₂;
  realize_conj₁ _ _  := by apply realize_conj₁;
  realize_conj₂ _ _  := by apply realize_conj₂;
  realize_conj₃ _ _  := by apply realize_conj₃;
  realize_disj₁ _ _  := by apply realize_disj₁;
  realize_disj₂ _ _  := by apply realize_disj₂;
  realize_disj₃ _ _  := by apply realize_disj₃;
  realize_dne _ _    := by apply realize_dne;

instance : Semantics.Necessitation (FrameClass W α) where
  realize_nec hp := by intro F hF; exact realize_nec (hp F hF);


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
