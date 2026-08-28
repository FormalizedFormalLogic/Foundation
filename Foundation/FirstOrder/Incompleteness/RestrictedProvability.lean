module

public import Foundation.FirstOrder.Incompleteness.RosserProvability

@[expose] public section
/-!
# Provability with restricted proof size

Some results to consider provable predicate modified to state that "provable by proof whose Gödel number is less than `F e`" for a `𝚺₁`-definable bounding function `F` (where `e` is an arbitary meta natural number). The results with `F = Exp.exp` recover "provable by proof whose Gödel number is less than `2^e`".
-/

namespace LO.FirstOrder

open FirstOrder Arithmetic
open PeanoMinus ISigma0 ISigma1 Bootstrapping Derivation

namespace Theory

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

variable {T U : Theory L} [T.Δ₁] [U.Δ₁]

/-- Provability with restriction of proof size -/
def RestrictedProvable (F : V → V) (e : ℕ) (T : Theory L) [T.Δ₁] (φ : V) := ∃ d < F (ORingStructure.numeral e), Arithmetic.Bootstrapping.Proof T d φ

noncomputable def restrictedProvable (fDef : 𝚺₁.Semisentence 2) (e : ℕ) : 𝚷₁.Semisentence 1 := .mkPi “φ. ∀ E, !fDef E !e → ∃ d < E, !(proof T).pi d φ”

noncomputable abbrev restrictedProvabilityPred (fDef : 𝚺₁.Semisentence 2) (e : ℕ) (σ : Sentence L) : ArithmeticSentence := (T.restrictedProvable fDef e).val/[⌜σ⌝]

instance RestrictedProvable.defined {F : V → V} {fDef : 𝚺₁.Semisentence 2} [𝚺₁-Function₁[V] F via fDef] {e} :
    𝚷₁-Predicate[V] (T.RestrictedProvable F e) via (T.restrictedProvable fDef e) where
  defined {φ} := by simp [Theory.restrictedProvable, Theory.RestrictedProvable];

/-- Gödel sentence by restricted provability -/
noncomputable abbrev restrictedGödel (fDef : 𝚺₁.Semisentence 2) (e : ℕ) (T : Theory L) [T.Δ₁] : ArithmeticSentence := fixedpoint (∼(T.restrictedProvable fDef e))

private noncomputable abbrev restrictedGödel' (fDef : 𝚺₁.Semisentence 2) (e : ℕ) (T : Theory L) [T.Δ₁] : ArithmeticSentence :=
  ∼(T.restrictedProvable fDef e).val/[⌜restrictedGödel fDef e T⌝]

private lemma restrictedGödel'_sigmaOne {fDef : 𝚺₁.Semisentence 2} {e : ℕ} : Hierarchy 𝚺 1 (T.restrictedGödel' fDef e) := by definability;

end Theory


namespace Arithmetic

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {T U : ArithmeticTheory} [T.Δ₁] -- [𝗜𝚺₁ ⪯ T] [𝗜𝚺₁ ⪯ U]
variable {fDef : 𝚺₁.Semisentence 2} {e : ℕ}

lemma def_restrictedGödel [𝗜𝚺₁ ⪯ U] : U ⊢ T.restrictedGödel fDef e 🡘 (∼(T.restrictedProvable fDef e).val)/[⌜T.restrictedGödel fDef e⌝] := diagonal _

private lemma def_restrictedGödel' [𝗜𝚺₁ ⪯ U] : U ⊢ T.restrictedGödel' fDef e 🡘 (∼(T.restrictedProvable fDef e).val)/[⌜T.restrictedGödel fDef e⌝] := by simp;

private lemma provable_E_restrictedGödel_restrictedGödel' [𝗜𝚺₁ ⪯ U] : U ⊢ T.restrictedGödel fDef e 🡘 T.restrictedGödel' fDef e := by
  apply Entailment.E!_trans;
  . exact def_restrictedGödel;
  . exact Entailment.E!_symm $ def_restrictedGödel';

private lemma iff_provable_restrictedGödel_provable_restrictedGödel' [𝗜𝚺₁ ⪯ U] : U ⊢ (T.restrictedGödel fDef e) ↔ U ⊢ (T.restrictedGödel' fDef e) := by
  apply Entailment.iff_of_E! provable_E_restrictedGödel_restrictedGödel';

private lemma iff_true_restrictedGödel_true_restrictedGödel' : ℕ↓[ℒₒᵣ] ⊧ (T.restrictedGödel fDef e) ↔ ℕ↓[ℒₒᵣ] ⊧ (T.restrictedGödel' fDef e) := by
  apply Semantics.models_iff.mp;
  apply models_of_provable (T := 𝗜𝚺₁) inferInstance;
  apply provable_E_restrictedGödel_restrictedGödel';

lemma models_restrictedGödel {F : V → V} [𝚺₁-Function₁[V] F via fDef] :
    V↓[ℒₒᵣ] ⊧ T.restrictedGödel fDef e ↔ ∀ x : V, x < F (ORingStructure.numeral e) → ¬Arithmetic.Bootstrapping.Proof T x (⌜T.restrictedGödel fDef e⌝) := by
  apply Iff.trans $ Semantics.models_iff.mp $ models_of_provable (T := 𝗜𝚺₁) inferInstance $ def_restrictedGödel;
  simp [models_iff, Theory.RestrictedProvable]

private lemma models_neg_restrictedGödel {F : V → V} [𝚺₁-Function₁[V] F via fDef] :
    ¬V↓[ℒₒᵣ] ⊧ T.restrictedGödel fDef e ↔ ∃ x : V, x < F (ORingStructure.numeral e) ∧ Arithmetic.Bootstrapping.Proof T x (⌜T.restrictedGödel fDef e⌝) := by
  simpa using models_restrictedGödel.not;

variable [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]

/- Gödel sentence by restricted provability is true. -/
theorem true_restrictedGödel {F : ℕ → ℕ} [𝚺₁-Function₁ F via fDef] : ℕ↓[ℒₒᵣ] ⊧ T.restrictedGödel fDef e := by
  by_contra hC;
  obtain ⟨e, _, he⟩ := models_neg_restrictedGödel (F := F) (e := e) |>.mp hC;
  apply hC;
  apply iff_true_restrictedGödel_true_restrictedGödel'.mpr;
  apply ArithmeticTheory.soundOnHierarchy T _ _ ?_ T.restrictedGödel'_sigmaOne;
  apply iff_provable_restrictedGödel_provable_restrictedGödel'.mp;
  apply Arithmetic.Bootstrapping.provable_of_standard_proof (T := T) (V := ℕ) (n := e);
  simpa using he;

/- Gödel sentence by restricted provability is provable. -/
theorem provable_restrictedGödel {F : ℕ → ℕ} [𝚺₁-Function₁ F via fDef] : T ⊢ T.restrictedGödel fDef e := by
  apply iff_provable_restrictedGödel_provable_restrictedGödel'.mpr;
  apply Arithmetic.sigma_one_completeness_iff T.restrictedGödel'_sigmaOne |>.mp;
  apply iff_true_restrictedGödel_true_restrictedGödel'.mp $ true_restrictedGödel (F := F);

/-- Lower bound of a Gödel number of proof of restricted Gödel sentence is `F e`. -/
theorem lower_bound_gödelNumber_proof_restrictedGödel {F : ℕ → ℕ} [𝚺₁-Function₁ F via fDef] :
    ∀ b : T ⊢! T.restrictedGödel fDef e, F (ORingStructure.numeral e) ≤ ⌜b⌝ := by
  intro b;
  exact Nat.le_of_not_lt
    $ (imp_not_comm.mp $ models_restrictedGödel.mp (true_restrictedGödel (F := F)) ⌜b⌝)
    $ proof_of_quote_proof b;

end Arithmetic

namespace Arithmetic

-- TODO: move to `Exp.lean`?
@[simp, grind =]
lemma exp_nat {n : ℕ} : Exp.exp n = 2 ^ n := by
  induction n with
  | zero => simp;
  | succ => grind [exp_succ];

variable {T : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]

-- `Exp.exp` is `𝚺₀`-definable via `expDef`; lift this to `𝚺₁` so the generalized
-- restricted-provability machinery applies with `F := Exp.exp`.
instance exp_defined_sigmaOne {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    𝚺₁-Function₁[V] Exp.exp via expDef.ofZero 𝚺₁ := exp_defined_deltaZero.of_zero

theorem provable_restrictedGödel_exp {e : ℕ} : T ⊢ T.restrictedGödel (expDef.ofZero 𝚺₁) e :=
  provable_restrictedGödel (F := Exp.exp)

/-- Lower bound of a Gödel number of proof of restricted Gödel sentence is `2^e`. -/
theorem lower_bound_gödelNumber_proof_restrictedGödel_exp {e : ℕ} :
    ∀ b : T ⊢! T.restrictedGödel (expDef.ofZero 𝚺₁) e, 2 ^ e ≤ ⌜b⌝ := by
  simpa using lower_bound_gödelNumber_proof_restrictedGödel (F := Exp.exp) (e := e)

/--
  "This sentence cannot be proved by proof whose Gödel number is less than `2^(10^9)`" is provable and length of its proof is larger than `2^(10^9)`.
-/
example :
  letI 𝔲 : ℕ := 10^9;
   T ⊢ T.restrictedGödel (expDef.ofZero 𝚺₁) 𝔲 ∧ ∀ b : T ⊢! T.restrictedGödel (expDef.ofZero 𝚺₁) 𝔲, (2^𝔲) ≤ ⌜b⌝  := by
  constructor;
  . apply provable_restrictedGödel_exp;
  . apply lower_bound_gödelNumber_proof_restrictedGödel_exp;

end Arithmetic

end LO.FirstOrder
