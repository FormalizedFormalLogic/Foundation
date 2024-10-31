import Foundation.Vorspiel.BinaryRelations
import Foundation.Modal.Kripke.Completeness

abbrev LO.Kripke.IsolatedFrameClass : FrameClass := λ F => Isolated F

namespace LO.Modal

namespace Kripke

open LO.Kripke
open System
open Kripke
open Formula

variable {α : Type u}

lemma axiomVer_defines : ∀ {F : Kripke.Frame}, (F#α ⊧* 𝗩𝗲𝗿 ↔ F ∈ IsolatedFrameClass) := by
  simp [Kripke.ValidOnFrame];
  intro F;
  constructor;
  . intro h x y hxy;
    exact h ⊥ (λ _ _ => True) x _ hxy;
  . intro hIrrefl _ _ x y hxy;
    have := hIrrefl hxy;
    contradiction;

instance axiomVer_definability : 𝔽((𝗩𝗲𝗿 : Theory α)).DefinedBy (IsolatedFrameClass) where
  define := axiomVer_defines
  nonempty := by
    use ⟨PUnit,  λ _ _ => False⟩
    tauto;

instance Ver_definability : 𝔽((𝐕𝐞𝐫 : Hilbert α)).DefinedBy (IsolatedFrameClass) := inferInstance

instance : Sound 𝐕𝐞𝐫 (IsolatedFrameClass#α) := inferInstance

instance : System.Consistent (𝐕𝐞𝐫 : Hilbert α) := inferInstance

variable [DecidableEq α]

lemma isolated_CanonicalFrame {Ax : Theory α} (h : 𝗩𝗲𝗿 ⊆ Ax) [System.Consistent 𝜿Ax] : Isolated (CanonicalFrame 𝜿Ax) := by
  intro x y rxy;
  have : (CanonicalModel 𝜿Ax) ⊧ □⊥ := iff_valid_on_canonicalModel_deducible.mpr $ Normal.maxm! (by aesop);
  exact this x _ rxy;

instance : Complete 𝐕𝐞𝐫 (IsolatedFrameClass.{u}#α) := instComplete_of_mem_canonicalFrame IsolatedFrameClass $ by
  apply isolated_CanonicalFrame;
  tauto;

end Kripke

end LO.Modal
