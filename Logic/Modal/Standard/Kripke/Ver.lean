import Logic.Vorspiel.BinaryRelations
import Logic.Modal.Standard.Kripke.Completeness

abbrev LO.Kripke.IsolatedFrameClass : FrameClass := λ F => Isolated F

namespace LO.Modal.Standard

namespace Kripke

open LO.Kripke
open System
open Kripke
open Formula
open DeductionParameter (Normal)

variable {α : Type u} [Inhabited α] [DecidableEq α]

instance Ver_characterizable : 𝔽(𝐕𝐞𝐫 of α).Characteraizable (IsolatedFrameClass) := characterizable_of_valid_axiomset
  ⟨⟨PUnit,  λ _ _ => False⟩, by tauto⟩
  (by
    simp;
    intro p F hF V x y Rxy;
    have := hF Rxy;
    contradiction;
  )

/-
lemma axiomVer_defines : AxiomSet.DefinesKripkeFrameClass (α := α) 𝗩𝗲𝗿 IsolatedFrameClass := by
  simp [AxiomSet.DefinesKripkeFrameClass, Kripke.ValidOnFrame];
  intro F;
  constructor;
  . intro h x y hxy;
    exact h ⊥ (λ _ _ => True) x _ hxy;
  . intro hIrrefl _ _ x y hxy;
    have := hIrrefl hxy;
    contradiction;
-/

instance : Sound 𝐕𝐞𝐫 (IsolatedFrameClass#α) := inferInstance

instance : System.Consistent (𝐕𝐞𝐫 : DeductionParameter α) := inferInstance

lemma isolated_CanonicalFrame {Ax : AxiomSet α} (h : 𝗩𝗲𝗿 ⊆ Ax) [System.Consistent 𝝂Ax] : Isolated (CanonicalFrame 𝝂Ax) := by
  intro x y rxy;
  have : (CanonicalModel 𝝂Ax) ⊧ □⊥ := iff_valid_on_canonicalModel_deducible.mpr $ Normal.maxm! (by aesop);
  exact this x _ rxy;

instance : Complete 𝐕𝐞𝐫 (IsolatedFrameClass.{u}#α) := instComplete_of_mem_canonicalFrame (IsolatedFrameClass) $ by
  apply isolated_CanonicalFrame;
  tauto;

end Kripke

end LO.Modal.Standard
