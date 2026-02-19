module

public import Foundation.FirstOrder.Bootstrapping.RosserProvability

@[expose] public section

namespace LO.FirstOrder

namespace ProvabilityAbstraction

open LO.Entailment FirstOrder Diagonalization Provability

variable {L₀ L : Language}

structure Refutability [L.ReferenceableBy L₀] (T₀ : Theory L₀) (T : Theory L) where
  refu : Semisentence L₀ 1
  refu_def {σ : Sentence L} : T ⊢ ∼σ → T₀ ⊢ refu/[⌜σ⌝]

namespace Refutability

variable [L.ReferenceableBy L₀] {T₀ : Theory L₀} {T : Theory L}

@[coe] def rf (𝔚 : Refutability T₀ T) (σ : Sentence L) : Sentence L₀ := 𝔚.refu/[⌜σ⌝]
instance : CoeFun (Refutability T₀ T) (fun _ ↦ Sentence L → Sentence L₀) := ⟨rf⟩

end Refutability


section

variable
  {L₀ L : Language} [L.ReferenceableBy L₀]
  {T₀ : Theory L₀} {T : Theory L}

lemma R1 {𝔚 : Refutability T₀ T} {σ : Sentence L} : T ⊢ ∼σ → T₀ ⊢ 𝔚 σ := fun h ↦ 𝔚.refu_def h

lemma R1' {L : Language} [L.ReferenceableBy L] {T₀ T : Theory L}
  {𝔚 : Refutability T₀ T} {σ : Sentence L} [T₀ ⪯ T] : T ⊢ ∼σ → T ⊢ 𝔚 σ := fun h ↦
  WeakerThan.pbl $ R1 h

end


section

variable
  [L.ReferenceableBy L] {T₀ T : Theory L}
  [Diagonalization T₀]
  {𝔚 : Refutability T₀ T}

/-- This sentence is refutable. -/
def jeroslow (𝔚 : Refutability T₀ T) [Diagonalization T₀] : Sentence L := fixedpoint T₀ 𝔚.refu

lemma jeroslow_def : T₀ ⊢ jeroslow 𝔚 ⭤ 𝔚 (jeroslow 𝔚) := Diagonalization.diag _

lemma jeroslow_def' [T₀ ⪯ T] : T ⊢ jeroslow 𝔚 ⭤ 𝔚 (jeroslow 𝔚) := WeakerThan.pbl $ jeroslow_def


class Refutability.SoundOn (𝔚 : Refutability T₀ T) (σ : Sentence L) where
  sound_on : T ⊢ 𝔚 σ → T ⊢ ∼σ
alias Refutability.sound_on := Refutability.SoundOn.sound_on

end


section

variable
  [L.ReferenceableBy L] {T₀ T : Theory L}
  [Diagonalization T₀]
  {𝔚 : Refutability T₀ T}

lemma unprovable_jeroslow [T₀ ⪯ T] [Consistent T] [𝔚.SoundOn (jeroslow 𝔚)] : T ⊬ jeroslow 𝔚 := by
  by_contra hC;
  apply Entailment.Consistent.not_bot (𝓢 := T);
  . infer_instance;
  . have : T ⊢ ∼(jeroslow 𝔚) := Refutability.sound_on $ (Entailment.iff_of_E! $ jeroslow_def') |>.mp hC;
    exact (N!_iff_CO!.mp this) ⨀ hC;

end


section

variable
  [L.ReferenceableBy L] {T₀ T : Theory L}
  [Diagonalization T₀]
  {𝔅 : Provability T₀ T} {𝔚 : Refutability T₀ T}

/-- Formalized Law of Noncontradiction holds on `x` -/
def safe (𝔅 : Provability T₀ T) (𝔚 : Refutability T₀ T) : Semisentence L 1 := “x. ¬(!𝔅.prov x ∧ !𝔚.refu x)”

/-- Formalized Law of Noncontradiction -/
def flon (𝔅 : Provability T₀ T) (𝔚 : Refutability T₀ T) : Sentence L := “∀ x, !(safe 𝔅 𝔚) x”

end


section

variable
  [L.DecidableEq] [L.ReferenceableBy L] {T₀ T : Theory L}
  [Diagonalization T₀] [T₀ ⪯ T]
  {𝔅 : Provability T₀ T} {𝔚 : Refutability T₀ T}

local notation "𝐉" => jeroslow 𝔚

lemma jeroslow_not_safe [𝔅.FormalizedCompleteOn 𝐉] : T ⊢ 𝐉 ➝ (𝔅 𝐉 ⋏ 𝔚 𝐉) := by
  have h₁ : T ⊢ 𝐉 ➝ 𝔅 𝐉 := 𝔅.formalized_complete_on;
  have h₂ : T ⊢ 𝐉 ⭤ 𝔚 𝐉 := jeroslow_def';
  cl_prover [h₁, h₂];

/--
  Formalized law of noncontradiction cannot be proved.
  Alternative formulation of Gödel's second incompleteness theorem.
-/
lemma unprovable_flon [consis : Consistent T] [𝔅.FormalizedCompleteOn 𝐉] : T ⊬ flon 𝔅 𝔚 := by
  contrapose! consis;
  replace consis : T ⊢ ∀⁰ safe 𝔅 𝔚 := by simpa [flon] using consis;
  have h₁ : T ⊢ ∼(𝔅 𝐉 ⋏ 𝔚 𝐉) := by simpa [safe] using FirstOrder.Theory.specialize _ _ ⨀ consis;
  have h₂ : T ⊢ ∼𝐉 := (contra! jeroslow_not_safe) ⨀ h₁;
  have h₃ : T ⊢ 𝐉 ⭤ 𝔚 𝐉 := jeroslow_def';
  have h₄ : T ⊢ 𝔚 𝐉 := R1' h₂;
  have h₅ : T ⊢ 𝔚 𝐉 ➝ 𝐉 := by cl_prover [h₃];
  have h₆ : T ⊢ 𝐉 := h₅ ⨀ h₄;
  exact not_consistent_iff_inconsistent.mpr <| inconsistent_iff_provable_bot.mpr $ (N!_iff_CO!.mp h₂) ⨀ h₆;

end

end ProvabilityAbstraction

end LO.FirstOrder

end
