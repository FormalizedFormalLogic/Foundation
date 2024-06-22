import Logic.Vorspiel.BinaryRelations
import Logic.Modal.Standard.Kripke.Completeness

namespace LO.Modal.Standard

namespace Kripke

open System
open Kripke
open Formula
open DeductionParameter (Normal)

variable {α} [Inhabited α] [DecidableEq α]

abbrev IsolatedFrameClass (α) : FrameClass α := { F | Isolated F }

lemma IsolatedFrameClass.nonempty : (IsolatedFrameClass α).Nonempty := by
  use { World := PUnit, Rel := (· ≠ ·) };
  simp [Isolated];

lemma axiomVer_defines : 𝗩𝗲𝗿.DefinesKripkeFrameClass (IsolatedFrameClass α)  := by
  -- simp [valid_on_KripkeFrame, valid_on_KripkeModel, Isolated];
  simp [AxiomSet.DefinesKripkeFrameClass, valid_on_KripkeFrame];
  intro F;
  constructor;
  . intro h x y hxy;
    exact h ⊥ (λ _ _ => True) x hxy;
  . intro hIrrefl _ _ x y hxy;
    have := hIrrefl hxy;
    contradiction;



instance : System.Consistent (𝐕𝐞𝐫 : DeductionParameter α) := consistent_of_defines axiomVer_defines IsolatedFrameClass.nonempty

lemma isolated_CanonicalFrame {Ax : AxiomSet α} (h : 𝗩𝗲𝗿 ⊆ Ax) [System.Consistent Axᴺ] : Isolated (CanonicalFrame Ax) := by
  intro x y rxy;
  have : (CanonicalModel Ax) ⊧ □⊥ := iff_valid_on_canonicalModel_deducible.mpr $ Normal.maxm_ax! (by aesop);
  simp [valid_on_KripkeModel, kripke_satisfies] at this;
  obtain ⟨_, ⟨hx, hy⟩⟩ := @this x y;
  have hny := rxy hx;
  contradiction;

instance : Complete (𝐕𝐞𝐫 : DeductionParameter α) (IsolatedFrameClass α) := instComplete_of_mem_canonicalFrame $ isolated_CanonicalFrame (by rfl)

end Kripke

end LO.Modal.Standard
