import Logic.Logic.System
import Logic.Modal.Normal.Formula

namespace LO.Semantics

variable {M F : Type*} [LogicalConnective F] [𝓢 : Semantics F M]

variable (𝓜 : M) (p q : F)

variable (M)

/--
  Modeling `LO.System.Minimal`
-/
class HilbertMinimal where
  modusPonens {𝓜 : M} {p q : F} : 𝓜 ⊧ p ⟶ q → 𝓜 ⊧ p → 𝓜 ⊧ q
  verum {𝓜 : M} : 𝓜 ⊧ ⊤
  imply₁ {𝓜 : M} {p q : F} : 𝓜 ⊧ p ⟶ q ⟶ p
  imply₂ {𝓜 : M} {p q r : F} : 𝓜 ⊧ (p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r
  conj₁ {𝓜 : M} {p q : F} : 𝓜 ⊧ p ⋏ q ⟶ p
  conj₂ {𝓜 : M} {p q : F} : 𝓜 ⊧ p ⋏ q ⟶ q
  conj₃ {𝓜 : M} {p q : F} : 𝓜 ⊧ p ⟶ q ⟶ p ⋏ q
  disj₁ {𝓜 : M} {p q : F} : 𝓜 ⊧ p ⟶ p ⋎ q
  disj₂ {𝓜 : M} {p q : F} : 𝓜 ⊧ q ⟶ p ⋎ q
  disj₃ {𝓜 : M} {p q r : F} : 𝓜 ⊧ (p ⟶ r) ⟶ (q ⟶ r) ⟶ p ⋎ q ⟶ r

/--
  Modeling `LO.System.Classical`
-/
class HilbertClassical extends HilbertMinimal M where
  dne {𝓜 : M} {p : F} : 𝓜 ⊧ ~~p ⟶ p

instance [Tarski M] : HilbertClassical M where
  modusPonens := by simp_all;
  verum := by simp_all;
  dne := by simp_all
  imply₁ := by simp_all;
  imply₂ := by simp_all;
  conj₁ := by simp_all;
  conj₂ := by simp_all;
  conj₃ := by simp_all;
  disj₁ := by simp_all;
  disj₂ := by simp_all;
  disj₃ := by
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

structure Frame (α : Type*) where
  rel : W → W → Prop

instance : CoeFun (Frame W α) (fun _ => W → W → Prop) := ⟨Frame.rel⟩

structure Valuation where
  val : W → α → Prop

instance : CoeFun (Valuation W α) (fun _ => W → α → Prop) := ⟨Valuation.val⟩

structure Model where
  frame : Frame W α
  valuation : Valuation W α

abbrev FrameClass := Set (Frame W α)

end Kripkean

variable {W : Type*} {α : Type u}

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

lemma models_iff_satisfies {M : Model W α} {w : W} {f : Formula α} : (M, w) ⊧ f ↔ Formula.Kripkean.Satisfies M w f := iff_of_eq rfl

instance : Semantics.Tarski ((Model W α) × W) where
  realize_top := by simp [models_iff_satisfies, Satisfies]
  realize_bot := by simp [models_iff_satisfies, Satisfies]
  realize_not := by simp [models_iff_satisfies, Satisfies]
  realize_and := by simp [models_iff_satisfies, Satisfies]
  realize_or := by simp [models_iff_satisfies, Satisfies]
  realize_imp := by simp [models_iff_satisfies, Satisfies, imp_iff_not_or]

def Formula.Kripkean.Models (M : Model W α) (f : Formula α) := ∀ w : W, (M, w) ⊧ f

instance : Semantics (Formula α) (Model W α) := ⟨fun M ↦ Formula.Kripkean.Models M⟩

open Semantics.HilbertMinimal Semantics.HilbertClassical

instance : Semantics.HilbertClassical (Model W α) where
  modusPonens := by intro M p q hpq hp w; have := hpq w; have := hp w; simp_all [models_iff_satisfies, Satisfies];
  verum _  := by apply verum;
  imply₁ _ := by apply imply₁;
  imply₂ _ := by apply imply₂;
  conj₁ _  := by apply conj₁;
  conj₂ _  := by apply conj₂;
  conj₃ _  := by apply conj₃;
  disj₁ _  := by apply disj₁;
  disj₂ _  := by apply disj₂;
  disj₃ _  := by apply disj₃;
  dne _    := by apply dne;

def Formula.Kripkean.Frames (F : Frame W α) (f : Formula α) := ∀ V, (Model.mk F V) ⊧ f

instance : Semantics (Formula α) (Frame W α) := ⟨fun F ↦ Formula.Kripkean.Frames F⟩

instance : Semantics.HilbertClassical (Frame W α) where
  modusPonens hpq hp := by intro w; exact modusPonens (hpq w) (hp w);
  verum _ _  := by apply verum;
  imply₁ _ _ := by apply imply₁;
  imply₂ _ _ := by apply imply₂;
  conj₁ _ _  := by apply conj₁;
  conj₂ _ _  := by apply conj₂;
  conj₃ _ _  := by apply conj₃;
  disj₁ _ _  := by apply disj₁;
  disj₂ _ _  := by apply disj₂;
  disj₃ _ _  := by apply disj₃;
  dne _ _    := by apply dne;

def Formula.Kripkean.FramesClasses (𝔽 : FrameClass W α) (f : Formula α) := ∀ F ∈ 𝔽, F ⊧ f

instance : Semantics (Formula α) (FrameClass W α) := ⟨fun 𝔽 ↦ Formula.Kripkean.FramesClasses 𝔽⟩

instance : Semantics.HilbertClassical (FrameClass W α) where
  modusPonens hpq hp := by intro F hF; exact modusPonens (hpq F hF) (hp F hF);
  verum _ _  := by apply verum;
  imply₁ _ _ := by apply imply₁;
  imply₂ _ _ := by apply imply₂;
  conj₁ _ _  := by apply conj₁;
  conj₂ _ _  := by apply conj₂;
  conj₃ _ _  := by apply conj₃;
  disj₁ _ _  := by apply disj₁;
  disj₂ _ _  := by apply disj₂;
  disj₃ _ _  := by apply disj₃;
  dne _ _    := by apply dne;

end LO.Modal.Normal
