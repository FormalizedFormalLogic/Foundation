import Foundation.FirstOrder.Bootstrapping.RosserProvability

/-!
# Provability with restricted proof size

Some results to consider provable predicate modified to state that "provable by proof whose Gödel number is less than `2^e`" (where `e` is an arbitary meta natural number).
-/

namespace LO.FirstOrder

open FirstOrder Arithmetic
open PeanoMinus ISigma0 ISigma1 Bootstrapping Derivation

namespace Theory

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

variable {T U : Theory L} [T.Δ₁] [U.Δ₁]

/-- Provability with restriction of proof size -/
def RestrictedProvable (e : ℕ) (T : Theory L) [T.Δ₁] (φ : V) := ∃ d < Exp.exp (ORingStructure.numeral e), T.Proof d φ

noncomputable def restrictedProvable (e : ℕ) : 𝚷₁.Semisentence 1 := .mkPi “φ. ∀ E, !expDef E !e → ∃ d < E, !T.proof.pi d φ”

noncomputable abbrev restrictedProvabilityPred (e : ℕ) (σ : Sentence L) : ArithmeticSentence := (T.restrictedProvable e).val/[⌜σ⌝]

instance RestrictedProvable.defined {e} : 𝚷₁-Predicate[V] T.RestrictedProvable e via T.restrictedProvable e where
  defined {φ} := by simp [Theory.restrictedProvable, Theory.RestrictedProvable];

/-- Gödel sentence by restricted provability -/
noncomputable abbrev restrictedGödel (e : ℕ) (T : Theory L) [T.Δ₁] : ArithmeticSentence := fixedpoint (∼(T.restrictedProvable e))

private noncomputable abbrev restrictedGödel' (e : ℕ) (T : Theory L) [T.Δ₁] : ArithmeticSentence := ∼(T.restrictedProvable e)/[⌜restrictedGödel e T⌝]

private lemma restrictedGödel'_sigmaOne {e : ℕ} : Hierarchy 𝚺 1 (T.restrictedGödel' e) := by definability;

end Theory


namespace Arithmetic

variable {V : Type} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]
variable {T U : ArithmeticTheory} [T.Δ₁] -- [𝗜𝚺₁ ⪯ T] [𝗜𝚺₁ ⪯ U]
variable {e : ℕ}

lemma def_restrictedGödel [𝗜𝚺₁ ⪯ U] : U ⊢ T.restrictedGödel e ⭤ (∼T.restrictedProvable e)/[⌜T.restrictedGödel e⌝] := diagonal _

private lemma def_restrictedGödel' [𝗜𝚺₁ ⪯ U] : U ⊢ T.restrictedGödel' e ⭤ (∼T.restrictedProvable e)/[⌜T.restrictedGödel e⌝] := by simp;

private lemma provable_E_restrictedGödel_restrictedGödel' [𝗜𝚺₁ ⪯ U] : U ⊢ T.restrictedGödel e ⭤ T.restrictedGödel' e := by
  apply Entailment.E!_trans;
  . exact def_restrictedGödel;
  . exact Entailment.E!_symm $ def_restrictedGödel';

private lemma iff_provable_restrictedGödel_provable_restrictedGödel' [𝗜𝚺₁ ⪯ U] : U ⊢ (T.restrictedGödel e) ↔ U ⊢ (T.restrictedGödel' e) := by
  apply Entailment.iff_of_E! provable_E_restrictedGödel_restrictedGödel';

private lemma iff_true_restrictedGödel_true_restrictedGödel' : ℕ ⊧ₘ (T.restrictedGödel e) ↔ ℕ ⊧ₘ (T.restrictedGödel' e) := by
  apply Semantics.models_iff.mp;
  apply models_of_provable (T := 𝗜𝚺₁) inferInstance;
  apply provable_E_restrictedGödel_restrictedGödel';

lemma models_restrictedGödel : V ⊧ₘ T.restrictedGödel e ↔ ∀ x : V, x < Exp.exp (ORingStructure.numeral e) → ¬T.Proof x (⌜T.restrictedGödel e⌝) := by
  apply Iff.trans $ Semantics.models_iff.mp $ models_of_provable (T := 𝗜𝚺₁) inferInstance $ def_restrictedGödel;
  simp [models_iff, Theory.RestrictedProvable]

private lemma models_neg_restrictedGödel : ¬V ⊧ₘ T.restrictedGödel e ↔ ∃ x : V, x < Exp.exp (ORingStructure.numeral e) ∧ T.Proof x (⌜T.restrictedGödel e⌝) := by
  simpa using models_restrictedGödel.not;

variable [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]

/- Gödel sentence by restricted provability is true. -/
theorem true_restrictedGödel : ℕ ⊧ₘ T.restrictedGödel e := by
  by_contra hC;
  obtain ⟨e, _, he⟩ := models_neg_restrictedGödel (e := e) |>.mp hC;
  apply hC;
  apply iff_true_restrictedGödel_true_restrictedGödel'.mpr;
  apply ArithmeticTheory.soundOnHierarchy T _ _ ?_ T.restrictedGödel'_sigmaOne;
  apply iff_provable_restrictedGödel_provable_restrictedGödel'.mp;
  apply Arithmetic.Bootstrapping.provable_of_standard_proof (T := T) (V := ℕ) (n := e);
  simpa using he;

/- Gödel sentence by restricted provability is provable. -/
theorem provable_restrictedGödel : T ⊢ T.restrictedGödel e := by
  apply iff_provable_restrictedGödel_provable_restrictedGödel'.mpr;
  apply Arithmetic.sigma_one_completeness_iff T.restrictedGödel'_sigmaOne |>.mp;
  apply iff_true_restrictedGödel_true_restrictedGödel'.mp $ true_restrictedGödel;

-- TODO: move to `Exp.lean`?
@[simp, grind =]
lemma exp_nat {n : ℕ} : Exp.exp n = 2 ^ n := by
  induction n with
  | zero => simp;
  | succ => grind [exp_succ];


/-- Lower bound of a Gödel number of proof of restricted Gödel sentence is `2^e`. -/
theorem lower_bound_gödelNumber_proof_restrictedGödel : ∀ b : T ⊢! T.restrictedGödel e, 2^e ≤ ⌜b⌝ := by
  intro b;
  have : Exp.exp (ORingStructure.numeral e) ≤ ⌜b⌝ := Nat.le_of_not_lt
    $ (imp_not_comm.mp $ models_restrictedGödel.mp true_restrictedGödel ⌜b⌝)
    $ proof_of_quote_proof b;
  simpa;

/--
  "This sentence cannot be proved by proof whose Gödel number is less than `2^(10^9)`" is provable and length of its proof is larger than `2^(10^9)`.
-/
example :
  letI 𝔲 : ℕ := 10^9;
   T ⊢ T.restrictedGödel 𝔲 ∧ ∀ b : T ⊢! T.restrictedGödel 𝔲, (2^𝔲) ≤ ⌜b⌝  := by
  constructor;
  . apply provable_restrictedGödel;
  . apply lower_bound_gödelNumber_proof_restrictedGödel;

end Arithmetic

end LO.FirstOrder
