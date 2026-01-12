import Foundation.FirstOrder.Bootstrapping.RosserProvability

namespace LO

namespace ProvabilityLogic

open LO.Entailment FirstOrder Diagonalization Provability

variable {L₀ L : Language}

structure Refutability [L.ReferenceableBy L₀] (T₀ : Theory L₀) (T : Theory L) where
  refu : Semisentence L₀ 1
  protected R1 {σ : Sentence L} : T ⊢ ∼σ → T₀ ⊢ refu/[⌜σ⌝]

namespace Refutability

variable [L.ReferenceableBy L₀] {T₀ : Theory L₀} {T : Theory L}

@[coe] def rf (ℜ : Refutability T₀ T) (σ : Sentence L) : Sentence L₀ := ℜ.refu/[⌜σ⌝]
instance : CoeFun (Refutability T₀ T) (fun _ ↦ Sentence L → Sentence L₀) := ⟨rf⟩

end Refutability


namespace Refutability

variable
  [L.ReferenceableBy L] {T₀ T : Theory L}
  [Diagonalization T₀]
  {ℜ : Refutability T₀ T}

/-- This sentence is refutable. -/
def jeroslow (ℜ : Refutability T₀ T) [Diagonalization T₀] : Sentence L := fixedpoint T₀ ℜ.refu

lemma jeroslow_def : T₀ ⊢ ℜ.jeroslow ⭤ ℜ ℜ.jeroslow := Diagonalization.diag _

lemma jeroslow_def' [T₀ ⪯ T] : T ⊢ ℜ.jeroslow ⭤ ℜ ℜ.jeroslow := Entailment.WeakerThan.pbl $ jeroslow_def

class JeroslowIntended (ℜ : Refutability T₀ T) where
  jeroslow_intended : T ⊢ ℜ ℜ.jeroslow → T ⊢ ∼ℜ.jeroslow
export JeroslowIntended (jeroslow_intended)

end Refutability


section

variable
  [L.ReferenceableBy L] {T₀ T : Theory L}
  [Diagonalization T₀]
  {ℜ : Refutability T₀ T}

lemma unprovable_jeroslow [T₀ ⪯ T] [Consistent T] [ℜ.JeroslowIntended] : T ⊬ ℜ.jeroslow := by
  by_contra hC;
  apply Entailment.Consistent.not_bot (𝓢 := T);
  . infer_instance;
  . have : T ⊢ ∼ℜ.jeroslow := Refutability.jeroslow_intended $ (Entailment.iff_of_E! $ Refutability.jeroslow_def') |>.mp hC;
    exact (N!_iff_CO!.mp this) ⨀ hC;

end


section

variable
  [L.ReferenceableBy L] {T₀ T : Theory L}
  [Diagonalization T₀]
  {𝔅 : Provability T₀ T} {ℜ : Refutability T₀ T}

-- TODO: Guarantee `x` is sentence.
/-- Formalized Law of Noncontradiction holds on `x` -/
def safeOn (𝔅 : Provability T₀ T) (ℜ : Refutability T₀ T) : Semisentence L 1 := “x. ¬(!𝔅.prov x ∧ !ℜ.refu x)”

/-- Formalized Law of Noncontradiction -/
def safe (𝔅 : Provability T₀ T) (ℜ : Refutability T₀ T) : Sentence L := “∀ x, !(safeOn 𝔅 ℜ) x”

end

end ProvabilityLogic

end LO




namespace LO.FirstOrder

open FirstOrder Arithmetic
open PeanoMinus ISigma0 ISigma1 Bootstrapping Derivation

namespace Theory

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

variable {T U : Theory L} [T.Δ₁] [U.Δ₁]

def Refutable (T : Theory L) [T.Δ₁] (φ : V) : Prop := T.Provable (neg L φ)

lemma Refutable.quote_iff {σ : Sentence L} : T.Refutable (V := V) ⌜σ⌝ ↔ T.Provable (V := V) ⌜∼σ⌝ := by
  simp [Refutable, Sentence.quote_def, Semiformula.quote_def]

noncomputable def refutable (T : Theory L) [T.Δ₁] : 𝚷-[2].Semisentence 1 := .mkPi
  “φ. ∀ nφ, !(negGraph L) nφ φ → !T.provable nφ” $ by
    apply Hierarchy.all_iff.mpr;
    apply Hierarchy.imp_iff.mpr;
    constructor;
    . apply Hierarchy.strict_mono (Γ := 𝚺) (s := 1) <;> simp;
    . apply Hierarchy.strict_mono (Γ := 𝚺) (s := 1) <;> simp;

lemma refutable_defined : 𝚷-[2]-Predicate[V] T.Refutable via T.refutable := .mk fun v ↦ by
  simp [Theory.refutable, Theory.Refutable];


noncomputable abbrev jeroslow (T : Theory L) [T.Δ₁] : ArithmeticSentence := fixedpoint (T.refutable.val)

private noncomputable abbrev jeroslow' (T : Theory L) [T.Δ₁] : ArithmeticSentence := (T.refutable.val)/[⌜T.jeroslow⌝]

private lemma jeroslow'_piTwo : Hierarchy 𝚷 2 (T.jeroslow') := by definability;

end Theory


namespace Arithmetic

variable {V : Type} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]
variable {T U : ArithmeticTheory} [T.Δ₁]  -- [𝗜𝚺₁ ⪯ T] [𝗜𝚺₁ ⪯ U]

lemma def_jeroslow [𝗜𝚺₁ ⪯ U] : U ⊢ T.jeroslow ⭤ T.refutable.val/[⌜T.jeroslow⌝] := diagonal _

lemma refutable_quote₀ {σ : ArithmeticSentence} : T.Refutable (V := V) ⌜σ⌝ ↔ T.Provable (V := V) ⌜∼σ⌝ := by
  simp [Theory.Refutable, Sentence.quote_def, Semiformula.quote_def];

lemma iff_refutable_neg_provable [ℕ ⊧ₘ* U] {σ : ArithmeticSentence} : U ⊢ T.refutable.val/[⌜σ⌝] ↔ U ⊢ T.provable.val/[⌜∼σ⌝] := by
  have := refutable_quote₀ (T := T) (σ := σ) (V := ℕ);
  dsimp [Theory.Refutable] at this;
  constructor;
  . intro h;
    have := T.refutable_defined (V := ℕ) |>.to_definable;
    sorry;
  . intro h;
    have := models_of_provable (T := U) (M := ℕ) inferInstance h;
    have := models_iff.mp this;
    simp at this;
    sorry;

lemma jeroslow_unprovable [ℕ ⊧ₘ* T] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1] : T ⊬ T.jeroslow := by
  by_contra hC;
  apply Entailment.Consistent.not_bot (𝓢 := T);
  . infer_instance;
  . have : T ⊢ T.refutable.val/[⌜T.jeroslow⌝] := (Entailment.iff_of_E! $ def_jeroslow) |>.mp hC;
    have : T ⊢ T.provable.val/[⌜∼T.jeroslow⌝] := iff_refutable_neg_provable.mp this;
    have : ℕ ⊧ₘ T.provable/[⌜∼Theory.jeroslow T⌝] := ArithmeticTheory.soundOnHierarchy T 𝚺 1 this (by definability);
    have : T ⊢ ∼T.jeroslow := by simpa [models_iff] using this;
    cl_prover [hC, this];

end Arithmetic

end LO.FirstOrder
