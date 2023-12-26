import Logic.Modal.Basic.Formula
import Logic.Modal.Basic.HilbertStyle
import Logic.Modal.Basic.Semantics

namespace LO

namespace Modal

open Formula

variable {α β : Type u} {p : Formula α} (f : Frame β)

theorem Hilbert.LogicK.WeakSoundness : (⊢ᴴ(𝗞) p) → (f ⊨ᶠ p) := by
  intro h;
  cases h
  case axm => aesop;
  case verum => simp [satisfies];
  case imply₁ =>
    intro V w;
    simp [satisfies_imp2];
    aesop;
  case imply₂ =>
    intro V w;
    simp [satisfies_imp2];
    aesop;
  case conj₁ =>
    intro V w;
    simp [satisfies_imp2];
    simp [satisfies];
    aesop;
  case conj₂ =>
    intro V w;
    simp [satisfies_imp2];
    simp [satisfies];
  case conj₃ =>
    intro V w;
    simp [satisfies_imp2];
    simp [satisfies];
    aesop;
  case disj₁ =>
    intro V w;
    simp [satisfies_imp2];
    simp [satisfies];
    aesop;
  case disj₂ =>
    intro V w;
    simp [satisfies_imp2];
    simp [satisfies];
    aesop;
  case disj₃ =>
    intro V w;
    simp [satisfies_imp2];
    simp [satisfies];
    aesop;
  case explode p =>
    simp [models_imp2];
    simp [satisfies];
  case em p =>
    intro V w;
    simp [satisfies, satisfies_neg'];
    apply Classical.em;
  case modus_ponens q d₁ d₂ =>
    sorry;
    -- apply framesMP;
    -- rcases q with ⟨q₁, q₂⟩;
    -- exact frames_imp2.mp (WeakSoundness d₁) (WeakSoundness d₂);
  case necessitation d =>
    apply framesNec;
    sorry
    -- exact WeakSoundness d;
  case K p => apply framesK;

end Modal

end LO
