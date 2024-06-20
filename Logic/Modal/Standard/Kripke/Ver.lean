import Logic.Vorspiel.BinaryRelations
import Logic.Modal.Standard.Kripke.Completeness

namespace LO.Modal.Standard

namespace Kripke

open System
open Kripke
open Formula

variable {α} [Inhabited α] [DecidableEq α]

abbrev IsolatedFrameClass (α) : FrameClass α := { F | Isolated F }

instance : 𝗩𝗲𝗿.DefinesKripkeFrameClass (IsolatedFrameClass α) where
  defines := by
    simp [valid_on_KripkeFrame, valid_on_KripkeModel, Isolated];
    intro F;
    constructor;
    . intro h x y hxy;
      exact h ⊥ (λ _ _ => True) x hxy;
    . intro hIrrefl p V x y hxy;
      simp_all;

instance : (IsolatedFrameClass α).IsNonempty where
  nonempty := by
    use { World := PUnit, Rel := (· ≠ ·) };
    simp [Isolated];

open DeductionParameter (Normal)

instance : System.Consistent (𝐕𝐞𝐫 : DeductionParameter α) := consistent (𝔽 := IsolatedFrameClass α)

lemma isolated_Ver_CanonicalFrame : (CanonicalFrame 𝗩𝗲𝗿) ∈ IsolatedFrameClass α := by
  intro x y rxy;
  have : (CanonicalModel (α := α) 𝗩𝗲𝗿) ⊧ □⊥ := iff_valid_on_canonicalModel_deducible.mpr $ axiomVer!;
  simp [valid_on_KripkeModel, kripke_satisfies] at this;
  obtain ⟨p, ⟨hx, hy⟩⟩ := @this x y;
  have := rxy hx;
  contradiction;

instance : Complete (𝐕𝐞𝐫 : DeductionParameter α) (IsolatedFrameClass α) := instComplete_of_mem_canonicalFrame isolated_Ver_CanonicalFrame

end Kripke

end LO.Modal.Standard
