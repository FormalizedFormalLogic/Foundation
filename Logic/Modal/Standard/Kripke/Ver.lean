import Logic.Vorspiel.BinaryRelations
import Logic.Modal.Standard.Kripke.Completeness

namespace LO.Modal.Standard

open System
open Kripke
open Formula

variable {α} [Inhabited α] [DecidableEq α]

instance AxiomSet.Ver.definability : Definability (α := α) 𝗩𝗲𝗿 (λ F => Isolated F.Rel) where
  defines := by
    simp [valid_on_KripkeFrame, valid_on_KripkeModel, Isolated];
    intro F;
    constructor;
    . intro h x y hxy;
      exact h ⊥ (λ _ _ => True) x y hxy;
    . intros;
      simp_all;

instance Ver.definability : Definability (α := α) Ax(𝐕𝐞𝐫) (λ F => Isolated F.Rel) := by
  simpa using Definability.union AxiomSet.K.definability AxiomSet.Ver.definability

instance : (𝔽ꟳ(Ax(𝐕𝐞𝐫)) : FiniteFrameClass α).IsNonempty where
  nonempty := by
    use { World := PUnit, Rel := (· ≠ ·) };
    apply iff_definability_memAxiomSetFrameClass (Ver.definability) |>.mpr;
    simp_all [Isolated];

namespace Kripke

open MaximalConsistentTheory

lemma definability_canonicalFrame_Ver {𝓓 : DeductionParameter α} [𝓓.Normal] [Inhabited (𝓓)-MCT] (hAx : 𝗩𝗲𝗿 ⊆ Ax(𝓓))
  : Isolated (CanonicalFrame 𝓓).Rel := by
  intro x y hxy;
  have : 𝓓 ⊢! □⊥ := ⟨Deduction.maxm (Set.mem_of_subset_of_mem hAx (by simp))⟩
  have := iff_valid_on_canonicalModel_deducible.mpr this x y hxy;
  contradiction;

instance : Canonical (𝐕𝐞𝐫 : DeductionParameter α) := by
  apply canonical_of_definability Ver.definability;
  apply definability_canonicalFrame_Ver;
  simp;

instance : Complete (𝐕𝐞𝐫 : DeductionParameter α) 𝔽(Ax(𝐕𝐞𝐫)) := instComplete

end Kripke

end LO.Modal.Standard
