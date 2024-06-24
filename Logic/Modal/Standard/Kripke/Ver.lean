import Logic.Vorspiel.BinaryRelations
import Logic.Modal.Standard.Kripke.Completeness

namespace LO.Modal.Standard

namespace Kripke

open System
open Kripke
open Formula
open DeductionParameter (Normal)

variable {α} [Inhabited α] [DecidableEq α]

abbrev IsolatedFrameClass : FrameClass := { ⟨_, F⟩ | Isolated F }

lemma IsolatedFrameClass.nonempty : IsolatedFrameClass.Nonempty.{0} := by
  use ⟨(Fin 1), PointFrame⟩
  simp [Isolated];

lemma axiomVer_defines : 𝗩𝗲𝗿.DefinesKripkeFrameClass (α := α) IsolatedFrameClass := by
  simp [AxiomSet.DefinesKripkeFrameClass, valid_on_KripkeFrame];
  intro _ F;
  constructor;
  . intro h x y hxy;
    exact h ⊥ (λ _ _ => True) x hxy;
  . intro hIrrefl _ _ x y hxy;
    have := hIrrefl hxy;
    contradiction;

instance : Sound 𝐕𝐞𝐫 IsolatedFrameClass[α] := sound_of_defines axiomVer_defines

instance : System.Consistent (𝐕𝐞𝐫 : DeductionParameter α) := consistent_of_defines axiomVer_defines IsolatedFrameClass.nonempty

lemma isolated_CanonicalFrame {Ax : AxiomSet α} (h : 𝗩𝗲𝗿 ⊆ Ax) [System.Consistent Axᴺ] : Isolated (CanonicalFrame Ax) := by
  intro x y rxy;
  have : (CanonicalModel Ax) ⊧ □⊥ := iff_valid_on_canonicalModel_deducible.mpr $ Normal.maxm! (by aesop);
  exact this x rxy;

instance : Complete 𝐕𝐞𝐫 IsolatedFrameClass[α] := instComplete_of_mem_canonicalFrame $ isolated_CanonicalFrame (by rfl)

end Kripke

end LO.Modal.Standard
