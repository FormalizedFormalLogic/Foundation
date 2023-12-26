import Logic.Modal.Basic.Formula
import Logic.Modal.Basic.HilbertStyle
import Logic.Modal.Basic.Semantics

namespace LO

namespace Modal

open Formula

variable {α : Type*} [h : System (Formula α)]
variable {p : Formula α}

def LogicK.proves [𝗞 (Formula α)] (p : Formula α) := ∅ ⊢ᴴ p
local notation "⊢ᴴ(𝗞) " p => LogicK.proves p

variable (f : Frame β)

theorem LogicK.weakSoundness [𝗞 (Formula α)]
  : (⊢ᴴ(𝗞) p) → (f ⊨ᶠ p) := by
  intro h;
  induction p using rec' <;> simp [satisfy];
  . intro w; sorry;
  . intro V w; sorry;
  . intro V w; sorry;
  . intro V w; sorry;
  . intro V w; sorry;
  . intro V w;
    intro w' hRel;
    sorry;
  . intro V w;
    sorry;

def LogicS4.proves [𝗦𝟰 (Formula α)] (p : Formula α) := ∅ ⊢ᴴ p
local notation "⊢ᴴ(𝗦𝟰) " p => LogicS4.proves p

theorem LogicS4.weakSoundness [𝗦𝟰 (Formula α)] (hRefl : f.Reflexive) (hTrans : f.Transitive)
  : (⊢ᴴ(𝗦𝟰) p) → (f ⊨ᶠ p) := by
  induction p using rec' <;> simp [satisfy];
  repeat sorry;

end Modal

end LO
