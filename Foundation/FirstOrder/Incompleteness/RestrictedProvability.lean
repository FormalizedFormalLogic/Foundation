module

public import Foundation.FirstOrder.Incompleteness.RosserProvability

@[expose] public section
/-!
# Provability with restricted proof size

Some results to consider provable predicate modified to state that "provable by proof whose Gödel number is less than `F e`" for a `𝚺₁`-definable bounding function `F` (where `e` is an arbitary meta natural number). The results with `F = Superexp.superexp` recover "provable by proof whose Gödel number is less than the superexponential of `e`".
-/

namespace LO.FirstOrder

open FirstOrder Arithmetic
open PeanoMinus ISigma0 ISigma1 Bootstrapping Derivation

namespace Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A function equipped with a canonical `𝚺₁`-definition of its graph. -/
class SigmaOneFunction₁ (f : V → V) where
  fDef : 𝚺₁.Semisentence 2
  defined : 𝚺₁-Function₁[V] f via fDef

instance {f : V → V} [SigmaOneFunction₁ f] : 𝚺₁-Function₁[V] f via (SigmaOneFunction₁.fDef f) := SigmaOneFunction₁.defined

end Arithmetic

namespace Theory

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

variable {T U : Theory L} [T.Δ₁] [U.Δ₁]

/-- Provability with restriction of proof size -/
def RestrictedProvable (f : V → V) (e : ℕ) (T : Theory L) [T.Δ₁] (φ : V) := ∃ d < f (ORingStructure.numeral e), Arithmetic.Bootstrapping.Proof T d φ

noncomputable def restrictedProvable (f : V → V) [Arithmetic.SigmaOneFunction₁ f] (e : ℕ) : 𝚷₁.Semisentence 1 :=
  .mkPi “φ. ∀ E, !(Arithmetic.SigmaOneFunction₁.fDef f) E !e → ∃ d < E, !(proof T).pi d φ”

noncomputable abbrev restrictedProvabilityPred (f : V → V) [Arithmetic.SigmaOneFunction₁ f] (e : ℕ) (σ : Sentence L) : ArithmeticSentence :=
  (T.restrictedProvable f e).val/[⌜σ⌝]

instance RestrictedProvable.defined {f : V → V} [Arithmetic.SigmaOneFunction₁ f] {e} :
    𝚷₁-Predicate[V] (T.RestrictedProvable f e) via (T.restrictedProvable f e) where
  defined {φ} := by simp [Theory.restrictedProvable, Theory.RestrictedProvable];

/-- Gödel sentence by restricted provability -/
noncomputable abbrev restrictedGödel (f : V → V) [Arithmetic.SigmaOneFunction₁ f] (e : ℕ) (T : Theory L) [T.Δ₁] : ArithmeticSentence :=
  fixedpoint (∼(T.restrictedProvable f e))

private noncomputable abbrev restrictedGödel' (f : V → V) [Arithmetic.SigmaOneFunction₁ f] (e : ℕ) (T : Theory L) [T.Δ₁] : ArithmeticSentence :=
  ∼(T.restrictedProvable f e).val/[⌜restrictedGödel f e T⌝]

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
private lemma restrictedGödel'_sigmaOne {f : V → V} [Arithmetic.SigmaOneFunction₁ f] {e : ℕ} : Hierarchy 𝚺 1 (T.restrictedGödel' f e) := by definability;

end Theory


namespace Arithmetic

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {T U : ArithmeticTheory} [T.Δ₁]
variable {f : V → V} [SigmaOneFunction₁ f] {e : ℕ}

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
lemma def_restrictedGödel [𝗜𝚺₁ ⪯ U] : U ⊢ T.restrictedGödel f e 🡘 (∼(T.restrictedProvable f e).val)/[⌜T.restrictedGödel f e⌝] := diagonal _

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
private lemma def_restrictedGödel' [𝗜𝚺₁ ⪯ U] : U ⊢ T.restrictedGödel' f e 🡘 (∼(T.restrictedProvable f e).val)/[⌜T.restrictedGödel f e⌝] := by simp;

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
private lemma provable_E_restrictedGödel_restrictedGödel' [𝗜𝚺₁ ⪯ U] : U ⊢ T.restrictedGödel f e 🡘 T.restrictedGödel' f e := by
  apply Entailment.E!_trans;
  . exact def_restrictedGödel;
  . exact Entailment.E!_symm $ def_restrictedGödel';

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
private lemma iff_provable_restrictedGödel_provable_restrictedGödel' [𝗜𝚺₁ ⪯ U] : U ⊢ (T.restrictedGödel f e) ↔ U ⊢ (T.restrictedGödel' f e) := by
  apply Entailment.iff_of_E! provable_E_restrictedGödel_restrictedGödel';

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
private lemma iff_true_restrictedGödel_true_restrictedGödel' : ℕ↓[ℒₒᵣ] ⊧ (T.restrictedGödel f e) ↔ ℕ↓[ℒₒᵣ] ⊧ (T.restrictedGödel' f e) := by
  apply Semantics.models_iff.mp;
  apply models_of_provable (T := 𝗜𝚺₁) inferInstance;
  apply provable_E_restrictedGödel_restrictedGödel';

lemma models_restrictedGödel :
    V↓[ℒₒᵣ] ⊧ T.restrictedGödel f e ↔ ∀ x : V, x < f (ORingStructure.numeral e) → ¬Arithmetic.Bootstrapping.Proof T x (⌜T.restrictedGödel f e⌝) := by
  apply Iff.trans $ Semantics.models_iff.mp $ models_of_provable (T := 𝗜𝚺₁) inferInstance $ def_restrictedGödel;
  simp [models_iff, Theory.RestrictedProvable]

private lemma models_neg_restrictedGödel :
    ¬V↓[ℒₒᵣ] ⊧ T.restrictedGödel f e ↔ ∃ x : V, x < f (ORingStructure.numeral e) ∧ Arithmetic.Bootstrapping.Proof T x (⌜T.restrictedGödel f e⌝) := by
  simpa using models_restrictedGödel (f := f).not;

variable [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]

/- Gödel sentence by restricted provability is true. -/
theorem true_restrictedGödel {f : ℕ → ℕ} [SigmaOneFunction₁ f] : ℕ↓[ℒₒᵣ] ⊧ T.restrictedGödel f e := by
  by_contra hC;
  obtain ⟨e, _, he⟩ := models_neg_restrictedGödel (f := f) (e := e) |>.mp hC;
  apply hC;
  apply iff_true_restrictedGödel_true_restrictedGödel'.mpr;
  apply ArithmeticTheory.soundOnHierarchy T _ _ ?_ T.restrictedGödel'_sigmaOne;
  apply iff_provable_restrictedGödel_provable_restrictedGödel'.mp;
  apply Arithmetic.Bootstrapping.provable_of_standard_proof (T := T) (V := ℕ) (n := e);
  simpa using he;

/- Gödel sentence by restricted provability is provable. -/
theorem provable_restrictedGödel {f : ℕ → ℕ} [SigmaOneFunction₁ f] : T ⊢ T.restrictedGödel f e := by
  apply iff_provable_restrictedGödel_provable_restrictedGödel'.mpr;
  apply Arithmetic.sigma_one_completeness_iff T.restrictedGödel'_sigmaOne |>.mp;
  apply iff_true_restrictedGödel_true_restrictedGödel'.mp $ true_restrictedGödel (f := f);

/-- Lower bound of a Gödel number of proof of restricted Gödel sentence is `F e`. -/
theorem lower_bound_gödelNumber_proof_restrictedGödel {f : ℕ → ℕ} [SigmaOneFunction₁ f] :
    ∀ b : T ⊢! T.restrictedGödel f e, f (ORingStructure.numeral e) ≤ ⌜b⌝ := by
  intro b;
  exact Nat.le_of_not_lt
    $ (imp_not_comm.mp $ models_restrictedGödel (f := f).mp (true_restrictedGödel (f := f)) ⌜b⌝)
    $ proof_of_quote_proof b;

end Arithmetic

namespace Arithmetic

private lemma exp_nat {n : ℕ} : Exp.exp n = 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => grind [exp_succ]

private lemma iterExp_le_succ (x y : ℕ) : iterExp x y ≤ iterExp x (y + 1) := by
  simp only [iterExp_succ];
  exact (exponential_exp (iterExp x y)).lt.le

private lemma iterExp_mono_right {x : ℕ} : Monotone (iterExp x) :=
  monotone_nat_of_le_succ (iterExp_le_succ x)

theorem two_pow_le_superexp {e : ℕ} (he : 1 ≤ e) : 2 ^ e ≤ Superexp.superexp e := by
  have h1 : iterExp e 1 = 2 ^ e := (iterExp_succ e 0).trans (by rw [iterExp_zero]; exact exp_nat)
  calc 2 ^ e = iterExp e 1 := h1.symm
    _ ≤ iterExp e e := iterExp_mono_right he
    _ = Superexp.superexp e := (superexp_eq e).symm

instance {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] : SigmaOneFunction₁ (Superexp.superexp : V → V) := ⟨superexpDef, superexp_defined⟩

variable {T : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]

theorem provable_restrictedGödel_superexp {e : ℕ} : T ⊢ T.restrictedGödel (Superexp.superexp : ℕ → ℕ) e :=
  provable_restrictedGödel

theorem lower_bound_gödelNumber_proof_restrictedGödel_superexp {e : ℕ} :
    ∀ b : T ⊢! T.restrictedGödel (Superexp.superexp : ℕ → ℕ) e, Superexp.superexp e ≤ ⌜b⌝ := by
  simpa [numeral_eq_natCast] using lower_bound_gödelNumber_proof_restrictedGödel (f := (Superexp.superexp : ℕ → ℕ)) (e := e)

/--
  "This sentence cannot be proved by proof whose Gödel number is less than the superexponential of `10^9`" is provable and length of its proof is larger than the superexponential of `10^9`.
-/
example :
  letI e : ℕ := 10^9;
   T ⊢ T.restrictedGödel (Superexp.superexp : ℕ → ℕ) e ∧ ∀ b : T ⊢! T.restrictedGödel (Superexp.superexp : ℕ → ℕ) e, Superexp.superexp e ≤ ⌜b⌝  := by
  constructor;
  . apply provable_restrictedGödel_superexp;
  . apply lower_bound_gödelNumber_proof_restrictedGödel_superexp;

end Arithmetic

end LO.FirstOrder
