import Logic.Logic.System
import Logic.Modal.Normal.Formula

namespace LO.Modal.Normal

namespace Kripkean

variable (W P : Type*)

abbrev Frame := W → W → Prop

abbrev Valuation := W → P → Prop

structure Model where
  frame : Frame W
  val : Valuation W P

end Kripkean

variable {W P : Type*}

namespace Formula.Kripkean

open Normal.Kripkean

def Satisfies (𝓜 : Kripkean.Model W P) (w : W) : Formula P → Prop
  | atom a  => 𝓜.val w a
  | falsum  => False
  | and p q => (Satisfies 𝓜 w p) ∧ (Satisfies 𝓜 w q)
  | or p q  => (Satisfies 𝓜 w p) ∨ (Satisfies 𝓜 w q)
  | imp p q => ¬(Satisfies 𝓜 w p) ∨ (Satisfies 𝓜 w q)
  | box p   => ∀ w', 𝓜.frame w w' → (Satisfies 𝓜 w' p)

namespace Satisfies

variable {𝓜 : Model W P} {w : W} {p q : Formula P}

@[simp]
instance : LO.Semantics ((Model W P) × W) (Formula P) where
  Realize Mw p := Satisfies (Mw.1) (Mw.2) p

@[simp]
instance : LO.Semantics.Tarski (Model W P × W) where
  realize_top := by simp [Satisfies]
  realize_bot := by simp [Satisfies]
  realize_not := by simp [Satisfies]
  realize_and := by simp [Satisfies]
  realize_or := by simp [Satisfies]
  realize_imp := by simp [Satisfies, imp_iff_not_or]

end Satisfies

def Models (𝓜 : Model W P) (p : Formula P) := ∀ w : W, (𝓜, w) ⊧ p

namespace Models

variable {𝓜 : Model W P} {p q : Formula P}

@[simp]
instance : LO.Semantics (Model W P) (Formula P) where
  Realize 𝓜 p := Models 𝓜 p

end Models


def Frames (𝓕 : Frame W) (p : Formula P) := ∀ V, (Model.mk 𝓕 V) ⊧ p

namespace Frames

instance : LO.Semantics (Frame W) (Formula (outParam Type*)) where
  Realize 𝓕 p := Frames 𝓕 p

end Frames

abbrev FrameClass (W : Type*) := Set (Frame W)

def FrameClasses (𝔽 : FrameClass W) (p : Formula P) := ∀ 𝓕 ∈ 𝔽, Frames 𝓕 p

namespace FrameClasses

instance : LO.Semantics (FrameClass W) (Formula (outParam Type*)) where
  Realize 𝔽 p := FrameClasses 𝔽 p

end FrameClasses


end Formula.Kripkean

end LO.Modal.Normal
