import Foundation.FirstOrder.Bootstrapping.RosserProvability

namespace LO.FirstOrder

namespace ProvabilityAbstraction

open LO.Entailment FirstOrder Diagonalization Provability

variable {L₀ L : Language}

structure Refutability [L.ReferenceableBy L₀] (T₀ : Theory L₀) (T : Theory L) where
  refu : Semisentence L₀ 1
  refu_def {σ : Sentence L} : T ⊢ ∼σ → T₀ ⊢ refu/[⌜σ⌝]

namespace Refutability

variable [L.ReferenceableBy L₀] {T₀ : Theory L₀} {T : Theory L}

@[coe] def rf (ℜ : Refutability T₀ T) (σ : Sentence L) : Sentence L₀ := ℜ.refu/[⌜σ⌝]
instance : CoeFun (Refutability T₀ T) (fun _ ↦ Sentence L → Sentence L₀) := ⟨rf⟩

end Refutability


section

variable
  {L₀ L : Language} [L.ReferenceableBy L₀]
  {T₀ : Theory L₀} {T : Theory L}

lemma R1 {ℜ : Refutability T₀ T} {σ : Sentence L} : T ⊢ ∼σ → T₀ ⊢ ℜ σ := fun h ↦ ℜ.refu_def h

lemma R1' {L : Language} [L.ReferenceableBy L] {T₀ T : Theory L}
  {ℜ : Refutability T₀ T} {σ : Sentence L} [T₀ ⪯ T] : T ⊢ ∼σ → T ⊢ ℜ σ := fun h ↦
  WeakerThan.pbl $ R1 h

end


section

variable
  [L.ReferenceableBy L] {T₀ T : Theory L}
  [Diagonalization T₀]
  {ℜ : Refutability T₀ T}

/-- This sentence is refutable. -/
def jeroslow (ℜ : Refutability T₀ T) [Diagonalization T₀] : Sentence L := fixedpoint T₀ ℜ.refu

lemma jeroslow_def : T₀ ⊢ jeroslow ℜ ⭤ ℜ (jeroslow ℜ) := Diagonalization.diag _

lemma jeroslow_def' [T₀ ⪯ T] : T ⊢ jeroslow ℜ ⭤ ℜ (jeroslow ℜ) := WeakerThan.pbl $ jeroslow_def


/-- Abstraction of formalized `𝚺₁`-completeness -/
class Provability.FormalizedCompleteOn (𝔅 : Provability T₀ T) (σ : Sentence L) where
  formalized_complete_on : T ⊢ σ ➝ 𝔅 σ
alias Provability.formalized_complete_on := Provability.FormalizedCompleteOn.formalized_complete_on

class Provability.SoundOn (𝔅 : Provability T₀ T) (σ : Sentence L) where
  sound_on : T ⊢ 𝔅 σ → T ⊢ σ
alias Provability.sound_on := Provability.SoundOn.sound_on

class Refutability.SoundOn (ℜ : Refutability T₀ T) (σ : Sentence L) where
  sound_on : T ⊢ ℜ σ → T ⊢ ∼σ
alias Refutability.sound_on := Refutability.SoundOn.sound_on

end


section

variable
  [L.ReferenceableBy L] {T₀ T : Theory L}
  [Diagonalization T₀]
  {ℜ : Refutability T₀ T}

lemma unprovable_jeroslow [T₀ ⪯ T] [Consistent T] [Refutability.SoundOn ℜ (jeroslow ℜ)] : T ⊬ jeroslow ℜ := by
  by_contra hC;
  apply Entailment.Consistent.not_bot (𝓢 := T);
  . infer_instance;
  . have : T ⊢ ∼(jeroslow ℜ) := Refutability.sound_on $ (Entailment.iff_of_E! $ jeroslow_def') |>.mp hC;
    exact (N!_iff_CO!.mp this) ⨀ hC;

end


section

variable
  [L.ReferenceableBy L] {T₀ T : Theory L}
  [Diagonalization T₀]
  {𝔅 : Provability T₀ T} {ℜ : Refutability T₀ T}

/-- Formalized Law of Noncontradiction holds on `x` -/
def safe (𝔅 : Provability T₀ T) (ℜ : Refutability T₀ T) : Semisentence L 1 := “x. ¬(!𝔅.prov x ∧ !ℜ.refu x)”

/-- Formalized Law of Noncontradiction -/
def flon (𝔅 : Provability T₀ T) (ℜ : Refutability T₀ T) : Sentence L := “∀ x, !(safe 𝔅 ℜ) x”

end


section

variable
  [L.DecidableEq] [L.ReferenceableBy L] {T₀ T : Theory L}
  [Diagonalization T₀] [T₀ ⪯ T]
  {𝔅 : Provability T₀ T} {ℜ : Refutability T₀ T}

local notation "𝐉" => jeroslow ℜ

lemma jeroslow_not_safe [𝔅.FormalizedCompleteOn 𝐉] : T ⊢ 𝐉 ➝ (𝔅 𝐉 ⋏ ℜ 𝐉) := by
  have h₁ : T ⊢ 𝐉 ➝ 𝔅 𝐉 := Provability.formalized_complete_on;
  have h₂ : T ⊢ 𝐉 ⭤ ℜ 𝐉 := jeroslow_def';
  cl_prover [h₁, h₂];

/--
  Formalized law of noncontradiction cannot be proved.
  Alternative form of Gödel's second incompleteness theorem.
-/
lemma unprovable_flon [consis : Consistent T] [𝔅.FormalizedCompleteOn 𝐉] : T ⊬ flon 𝔅 ℜ := by
  contrapose! consis;
  have h₁ : T ⊢ 𝐉 ➝ 𝔅 𝐉 := Provability.formalized_complete_on;
  have h₂ : T ⊢ 𝐉 ⭤ ℜ 𝐉 := jeroslow_def';
  dsimp [flon] at consis;
  have : T ⊢ (safe 𝔅 ℜ)/[⌜𝐉⌝] := by
    sorry;
  have h₃ : T ⊢ ∼(𝔅 𝐉 ⋏ ℜ 𝐉) := by simpa [safe] using this;
  have h₄ : T ⊢ ∼(𝔅 𝐉 ⋏ ℜ 𝐉) ➝ ∼𝐉 := contra! $ by cl_prover [h₁, h₂];
  have h₅ : T ⊢ ∼𝐉 := h₄ ⨀ h₃;
  have h₆ : T ⊢ ℜ 𝐉 := R1' h₅;
  have h₇ : T ⊢ ℜ 𝐉 ➝ 𝐉 := by cl_prover [h₂];
  have h₈ : T ⊢ 𝐉 := h₇ ⨀ h₆;
  exact not_consistent_iff_inconsistent.mpr <| inconsistent_iff_provable_bot.mpr $ (N!_iff_CO!.mp h₅) ⨀ h₈;

end


end ProvabilityAbstraction

end LO.FirstOrder
