import Foundation.FirstOrder.Bootstrapping.RosserProvability


namespace LO.FirstOrder

open FirstOrder Arithmetic
open PeanoMinus ISigma0 ISigma1 Bootstrapping Derivation

namespace Theory

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

variable {T U : Theory L} [T.Δ₁] [U.Δ₁]

/-- Provability with restriction of proof-length -/
def RestrictedProvable (𝔢 : ℕ) (T : Theory L) [T.Δ₁] (φ : V) := ∃ d ≤ Exp.exp (ORingStructure.numeral 𝔢), T.Proof d φ

noncomputable def restrictedProvable (𝔢 : ℕ) : 𝚷₁.Semisentence 1 := .mkPi “φ. ∀ E, !expDef E !𝔢 → ∃ d <⁺ E, !T.proof.pi d φ”

noncomputable abbrev restrictedProvabilityPred (𝔢 : ℕ) (σ : Sentence L) : ArithmeticSentence := (T.restrictedProvable 𝔢).val/[⌜σ⌝]

instance RestrictedProvable.defined {𝔢} : 𝚷₁-Predicate[V] T.RestrictedProvable 𝔢 via T.restrictedProvable 𝔢 where
  defined {φ} := by simp [Theory.restrictedProvable, Theory.RestrictedProvable];

/-- Gödel sentence by restricted provability -/
noncomputable abbrev restrictedGödel (𝔢 : ℕ) (T : Theory L) [T.Δ₁] : ArithmeticSentence := fixedpoint (∼(T.restrictedProvable 𝔢))

noncomputable abbrev restrictedGödel' (𝔢 : ℕ) (T : Theory L) [T.Δ₁] : ArithmeticSentence := ∼(T.restrictedProvable 𝔢)/[⌜restrictedGödel 𝔢 T⌝]

lemma restrictedGödel'_sigmaOne {𝔢 : ℕ} : Hierarchy 𝚺 1 (T.restrictedGödel' 𝔢) := by definability;

end Theory


namespace Arithmetic

variable {V : Type} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]
variable {T U : ArithmeticTheory} [T.Δ₁] -- [𝗜𝚺₁ ⪯ T] [𝗜𝚺₁ ⪯ U]
variable {𝔢 : ℕ}

lemma def_restrictedGödel [𝗜𝚺₁ ⪯ U] : U ⊢ T.restrictedGödel 𝔢 ⭤ (∼T.restrictedProvable 𝔢)/[⌜T.restrictedGödel 𝔢⌝] := diagonal _

lemma def_restrictedGödel' [𝗜𝚺₁ ⪯ U] : U ⊢ T.restrictedGödel' 𝔢 ⭤ (∼T.restrictedProvable 𝔢)/[⌜T.restrictedGödel 𝔢⌝] := by simp;

lemma provable_E_restrictedGödel_restrictedGödel' [𝗜𝚺₁ ⪯ U] : U ⊢ T.restrictedGödel 𝔢 ⭤ T.restrictedGödel' 𝔢 := by
  apply Entailment.E!_trans;
  . exact def_restrictedGödel;
  . exact Entailment.E!_symm $ def_restrictedGödel';

lemma iff_provable_restrictedGödel_provable_restrictedGödel' [𝗜𝚺₁ ⪯ U] : U ⊢ (T.restrictedGödel 𝔢) ↔ U ⊢ (T.restrictedGödel' 𝔢) := by
  apply Entailment.iff_of_E! provable_E_restrictedGödel_restrictedGödel';

lemma iff_true_restrictedGödel_true_restrictedGödel' : ℕ ⊧ₘ (T.restrictedGödel 𝔢) ↔ ℕ ⊧ₘ (T.restrictedGödel' 𝔢) := by
  apply Semantics.models_iff.mp;
  apply models_of_provable (T := 𝗜𝚺₁) inferInstance;
  apply provable_E_restrictedGödel_restrictedGödel';

lemma models_restrictedGödel : V ⊧ₘ T.restrictedGödel 𝔢 ↔ ∀ x : V, x ≤ Exp.exp (ORingStructure.numeral 𝔢) → ¬T.Proof x (⌜T.restrictedGödel 𝔢⌝) := by
  apply Iff.trans $ Semantics.models_iff.mp $ models_of_provable (T := 𝗜𝚺₁) inferInstance $ def_restrictedGödel;
  simp [models_iff, Theory.RestrictedProvable]

lemma models_neg_restrictedGödel : ¬V ⊧ₘ T.restrictedGödel 𝔢 ↔ ∃ x : V, x ≤ Exp.exp (ORingStructure.numeral 𝔢) ∧ T.Proof x (⌜T.restrictedGödel 𝔢⌝) := by
  simpa using models_restrictedGödel.not;

theorem true_restrictedGödel [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1] : ℕ ⊧ₘ T.restrictedGödel 𝔢 := by
  by_contra hC;
  obtain ⟨e, _, he⟩ := models_neg_restrictedGödel (𝔢 := 𝔢) |>.mp hC;
  apply hC;
  apply iff_true_restrictedGödel_true_restrictedGödel'.mpr;
  apply ArithmeticTheory.soundOnHierarchy T _ _ ?_ T.restrictedGödel'_sigmaOne;
  apply iff_provable_restrictedGödel_provable_restrictedGödel'.mp;
  apply Arithmetic.Bootstrapping.provable_of_standard_proof (T := T) (V := ℕ) (n := e);
  simpa using he;

theorem provable_restrictedGödel [𝗥₀ ⪯ T] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1] : T ⊢ T.restrictedGödel 𝔢 := by
  apply iff_provable_restrictedGödel_provable_restrictedGödel'.mpr;
  apply Arithmetic.sigma_one_completeness_iff T.restrictedGödel'_sigmaOne |>.mp;
  apply iff_true_restrictedGödel_true_restrictedGödel'.mp $ true_restrictedGödel;

/--
  "This sentence cannot be proved by proof its Gödel number smaller than `2^100`" is true and provable.
-/
example [T.SoundOnHierarchy 𝚺 1] [𝗥₀ ⪯ T] [𝗜𝚺₁ ⪯ T] : ℕ ⊧ₘ T.restrictedGödel 100 ∧ T ⊢ T.restrictedGödel 100 := by
  constructor;
  . apply true_restrictedGödel;
  . apply provable_restrictedGödel;

end Arithmetic

end LO.FirstOrder
