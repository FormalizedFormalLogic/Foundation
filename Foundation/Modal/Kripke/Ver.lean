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

instance Ver_definability : 𝔽(Hilbert.Ver α).DefinedBy (IsolatedFrameClass) := inferInstance

instance : Sound (Hilbert.Ver α) (IsolatedFrameClass#α) := inferInstance

instance : System.Consistent (Hilbert.Ver α) := inferInstance

variable [DecidableEq α]

lemma isolated_CanonicalFrame {Ax : Theory α} (h : 𝗩𝗲𝗿 ⊆ Ax) [System.Consistent (Hilbert.ExtK Ax)] : Isolated (CanonicalFrame (Hilbert.ExtK Ax)) := by
  intro x y rxy;
  have : (CanonicalModel (Hilbert.ExtK Ax)) ⊧ □⊥ := iff_valid_on_canonicalModel_deducible.mpr $ (Hilbert.ExtK.maxm!) (by apply h; simp);
  exact this x _ rxy;

instance : Complete (Hilbert.Ver α) (IsolatedFrameClass.{u}#α) := instComplete_of_mem_canonicalFrame IsolatedFrameClass $ by
  apply isolated_CanonicalFrame;
  tauto;

end Kripke

end LO.Modal
