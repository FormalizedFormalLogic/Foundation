import Foundation.FirstOrder.Bootstrapping.RosserProvability
import Foundation.FirstOrder.Bootstrapping.ProvabilityAbstraction.Refutability

namespace LO.FirstOrder.Arithmetic

open Bootstrapping Derivation ProvabilityAbstraction

namespace Bootstrapping

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

variable {L : Language} [L.Encodable] [L.LORDefinable]

variable {T U : Theory L} [T.Δ₁] [U.Δ₁]

def _root_.LO.FirstOrder.Theory.Refutable (T : Theory L) [T.Δ₁] (φ : V) : Prop := T.Provable (neg L φ)

lemma Refutable.quote_iff {σ : Sentence L} : T.Refutable (⌜σ⌝ : V) ↔ T.Provable (⌜∼σ⌝ : V) := by
  simp [Theory.Refutable, Sentence.quote_def, Semiformula.quote_def]

noncomputable def _root_.LO.FirstOrder.Theory.refutable (T : Theory L) [T.Δ₁] : 𝚺₁.Semisentence 1 := .mkSigma
  “φ. ∃ nφ, !(negGraph L) nφ φ ∧ !T.provable nφ”

instance refutable_defined : 𝚺₁-Predicate[V] T.Refutable via T.refutable := .mk fun v ↦ by
  simp [Theory.refutable, Theory.Refutable]

instance refutable_definable : 𝚺₁-Predicate[V] T.Refutable := refutable_defined.to_definable

end Bootstrapping

noncomputable def _root_.LO.FirstOrder.Theory.standardRefutability (T : ArithmeticTheory) [T.Δ₁] : Refutability 𝗜𝚺₁ T where
  refu := T.refutable.val
  refu_def {σ} h := provable_of_models _ _ fun (V : Type) _ _ ↦ by
    simpa [models_iff, Refutable.quote_iff] using internalize_provability h (V := V)

variable {T U : ArithmeticTheory} [T.Δ₁]  -- [𝗜𝚺₁ ⪯ T] [𝗜𝚺₁ ⪯ U]

@[simp]
lemma jeroslow_sigmaOne : Hierarchy 𝚺 1 (jeroslow (Theory.standardRefutability T)) := by
  dsimp [jeroslow, Diagonalization, Diagonalization.fixedpoint, fixedpoint];
  sorry;

instance : T.standardRefutability.SoundOn (jeroslow T.standardRefutability) := by
  constructor;
  intro h;
  simp [Theory.standardRefutability, Refutability.rf] at h;
  sorry;

instance [𝗜𝚺₁ ⪯ T] : T.standardProvability.FormalizedCompleteOn (jeroslow T.standardRefutability) := by
  constructor;
  apply Entailment.WeakerThan.pbl (𝓢 := 𝗜𝚺₁);
  apply provable_sigma_one_complete;
  simp;

theorem unprovable_jeroslow [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]
  : T ⊬ jeroslow (T.standardRefutability) := ProvabilityAbstraction.unprovable_jeroslow

theorem unprovable_formalized_law_of_noncontradiction
  [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]
  : T ⊬ flon (T.standardProvability) (T.standardRefutability) := ProvabilityAbstraction.unprovable_flon

end Arithmetic

end LO.FirstOrder
