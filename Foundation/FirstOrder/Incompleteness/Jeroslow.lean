module

public import Foundation.FirstOrder.Incompleteness.RosserProvability
public import Foundation.FirstOrder.Incompleteness.ProvabilityAbstraction.Refutability

/-!
# Jeroslow's Second Incompleteness Theorem

Jeroslow's formulation of the second incompleteness theorem
states that the sentence represents _formalized law of noncontradiction_ of `T`
(i.e. no statement can be both formally proved in `T` and formally refuted in `T`)
is not provable in `T` itself.

## References
- [Jeroslow, R. G., *Redundancies in the Hilbert-Bernays Derivability Conditions for Gödel's Second Incompleteness Theorem*][Jer73]
-/

@[expose] public section

namespace LO.FirstOrder

open Entailment
open Arithmetic Bootstrapping
open Derivation ProvabilityAbstraction

namespace Theory

variable {L : Language}


section

variable [L.Encodable] [L.LORDefinable]
         {T : Theory L} [T.Δ₁]

def Refutable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁] (T : Theory L) [T.Δ₁] (φ : V) : Prop
  := T.Provable (neg L φ)

noncomputable def refutable (T : Theory L) [T.Δ₁] : 𝚺₁.Semisentence 1
  := .mkSigma “φ. ∃ nφ, !(negGraph L) nφ φ ∧ !T.provable nφ”

section

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

lemma Refutable.quote_iff {σ : Sentence L} : T.Refutable (⌜σ⌝ : V) ↔ T.Provable (⌜∼σ⌝ : V) := by
  simp [Theory.Refutable, Sentence.quote_def, Semiformula.quote_def]

instance refutable_defined : 𝚺₁-Predicate[V] T.Refutable via T.refutable := .mk fun v ↦ by
  simp [Theory.refutable, Theory.Refutable]

instance refutable_definable : 𝚺₁-Predicate[V] T.Refutable := refutable_defined.to_definable

end

end


section

variable {T U : ArithmeticTheory} [T.Δ₁]

noncomputable abbrev standardRefutability (T : ArithmeticTheory) [T.Δ₁] : Refutability 𝗜𝚺₁ T where
  refu := T.refutable.val
  refu_def {σ} h := provable_of_models _ _ fun (V : Type) _ _ ↦ by
    simpa [models_iff, Refutable.quote_iff] using internalize_provability h (V := V)

noncomputable abbrev jeroslow (T : ArithmeticTheory) [T.Δ₁] : ArithmeticSentence := fixedpoint T.refutable

private noncomputable abbrev jeroslow' (T : ArithmeticTheory) [T.Δ₁] : ArithmeticSentence := (T.refutable)/[⌜T.jeroslow⌝]

private lemma jeroslow'_sigmaOne : Hierarchy 𝚺 1 (T.jeroslow') := by definability;

lemma def_jeroslow [𝗜𝚺₁ ⪯ U] : U ⊢ T.jeroslow 🡘 (T.refutable)/[⌜T.jeroslow⌝] := diagonal _

private lemma def_jeroslow' [𝗜𝚺₁ ⪯ U] : U ⊢ T.jeroslow' 🡘 (T.refutable)/[⌜T.jeroslow⌝] := by simp;

private lemma provable_E_jeroslow_jeroslow' [𝗜𝚺₁ ⪯ U] : U ⊢ T.jeroslow 🡘 T.jeroslow' := Entailment.E!_trans def_jeroslow def_jeroslow'

private lemma iff_provable_jeroslow_provable_jeroslow' [𝗜𝚺₁ ⪯ U] : U ⊢ (T.jeroslow) ↔ U ⊢ (T.jeroslow') := by
  apply Entailment.iff_of_E! provable_E_jeroslow_jeroslow';

open LO.Entailment in
instance [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1] : T.standardRefutability.SoundOn (ProvabilityAbstraction.jeroslow T.standardRefutability) := by
  constructor;
  intro h;
  have := ArithmeticTheory.SoundOn.sound (F := Arithmetic.Hierarchy 𝚺 1) h $ by simp [standardRefutability, Refutability.rf];
  exact provable_iff_provable (L := ℒₒᵣ) |>.mp $ by simpa [
    models_iff, standardRefutability, Refutability.rf, Refutable,
    Sentence.quote_def, Semiformula.quote_def,
    provable_iff_provable
  ] using this;

instance [𝗜𝚺₁ ⪯ T] : T.standardProvability.FormalizedCompleteOn (ProvabilityAbstraction.jeroslow T.standardRefutability) := by
  constructor;
  apply provable_sigma_one_complete_of_E;
  . show Hierarchy 𝚺 1 T.jeroslow';
    exact jeroslow'_sigmaOne;
  . apply Entailment.E!_symm $ provable_E_jeroslow_jeroslow';

end

end Theory


namespace Arithmetic

variable {L : Language} [L.Encodable] [L.LORDefinable]
variable {T : ArithmeticTheory} [T.Δ₁]

/--
  Jeroslow sentence of `T` is not provable in `T` itself.
-/
theorem unprovable_jeroslow [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]
  : T ⊬ T.jeroslow := ProvabilityAbstraction.unprovable_jeroslow (𝔚 := T.standardRefutability)

/--
  Jeroslow's formulation of the second incompleteness theorem.

  The sentence represents _formalized law of noncontradiction_ of `T`
  (i.e. no statement can be both formally proved in `T` and formally refuted in `T`)
  is not provable in `T` itself.
-/
theorem unprovable_formalized_law_of_noncontradiction [𝗜𝚺₁ ⪯ T] [Entailment.Consistent T]
  : T ⊬ (∀⁰ ∼(T.provable ⋏ T.refutable) : ArithmeticSentence) := by
    simpa [flon, safe, -DeMorgan.and] using ProvabilityAbstraction.unprovable_flon
      (𝔅 := T.standardProvability) (𝔚 := T.standardRefutability)

end Arithmetic


end LO.FirstOrder

end
