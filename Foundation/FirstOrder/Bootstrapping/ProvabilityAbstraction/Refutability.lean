import Foundation.FirstOrder.Bootstrapping.RosserProvability

namespace LO.FirstOrder

namespace Schema

variable {𝓢 : Schema L}

open Derivation

def specialize (φ : SyntacticSemiformula L 1) (t : SyntacticTerm L) : 𝓢 ⊢! ∀⁰ φ ➝ φ/[t] :=
  have : 𝓢 ⟹ [(∼φ)/[t], φ/[t]] := Derivation.em (φ := φ/[t]) (by simp) (by simp)
  have : 𝓢 ⟹ [∃⁰ ∼φ, φ/[t]] := this.exs t
  this.or.cast (by simp [Semiformula.imp_eq])

end Schema

namespace Theory

variable {T : Theory L} {φ : Semisentence L 1}

def specialize! (φ : Semisentence L 1) (t) : T ⊢! ∀⁰ φ ➝ φ/[t] := ofSyntacticProof <| by
  simpa [Semiformula.coe_subst_eq_subst_coe₁] using (Schema.specialize (𝓢 := T) φ (t : SyntacticTerm L))

lemma specialize (φ : Semisentence L 1) (t) : T ⊢ ∀⁰ φ ➝ φ/[t] := ⟨specialize! φ t⟩

end Theory

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


/-- Abstraction of formalized `𝚺₁`-completeness -/
class Provability.FormalizedCompleteOn (𝔅 : Provability T₀ T) (σ : Sentence L) where
  formalized_complete_on : T ⊢ σ ➝ 𝔅 σ
alias Provability.formalized_complete_on := Provability.FormalizedCompleteOn.formalized_complete_on

class Provability.SoundOn (𝔅 : Provability T₀ T) (σ : Sentence L) where
  sound_on : T ⊢ 𝔅 σ → T ⊢ σ
alias Provability.sound_on := Provability.SoundOn.sound_on

class Refutability.SoundOn (𝔚 : Refutability T₀ T) (σ : Sentence L) where
  sound_on : T ⊢ 𝔚 σ → T ⊢ ∼σ
alias Refutability.sound_on := Refutability.SoundOn.sound_on

end


section

variable
  [L.ReferenceableBy L] {T₀ T : Theory L}
  [Diagonalization T₀]
  {𝔚 : Refutability T₀ T}

lemma unprovable_jeroslow [T₀ ⪯ T] [Consistent T] [Refutability.SoundOn 𝔚 (jeroslow 𝔚)] : T ⊬ jeroslow 𝔚 := by
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
  have h₁ : T ⊢ 𝐉 ➝ 𝔅 𝐉 := Provability.formalized_complete_on;
  have h₂ : T ⊢ 𝐉 ⭤ 𝔚 𝐉 := jeroslow_def';
  cl_prover [h₁, h₂];

/--
  Formalized law of noncontradiction cannot be proved.
  Alternative form of Gödel's second incompleteness theorem.
-/
lemma unprovable_flon [consis : Consistent T] [𝔅.FormalizedCompleteOn 𝐉] : T ⊬ flon 𝔅 𝔚 := by
  contrapose! consis;
  replace consis : T ⊢ ∀⁰ safe 𝔅 𝔚 := by simpa [flon] using consis;
  have h₁ : T ⊢ ∼(𝔅 𝐉 ⋏ 𝔚 𝐉) := by simpa [safe] using FirstOrder.Theory.specialize _ _ ⨀ consis;
  have h₂ : T ⊢ 𝐉 ➝ 𝔅 𝐉 := Provability.formalized_complete_on;
  have h₃ : T ⊢ 𝐉 ⭤ 𝔚 𝐉 := jeroslow_def';
  have h₄ : T ⊢ ∼(𝔅 𝐉 ⋏ 𝔚 𝐉) ➝ ∼𝐉 := contra! $ by cl_prover [h₂, h₃];
  have h₅ : T ⊢ ∼𝐉 := h₄ ⨀ h₁;
  have h₆ : T ⊢ 𝔚 𝐉 := R1' h₅;
  have h₇ : T ⊢ 𝔚 𝐉 ➝ 𝐉 := by cl_prover [h₃];
  have h₈ : T ⊢ 𝐉 := h₇ ⨀ h₆;
  exact not_consistent_iff_inconsistent.mpr <| inconsistent_iff_provable_bot.mpr $ (N!_iff_CO!.mp h₅) ⨀ h₈;

end


end ProvabilityAbstraction

end LO.FirstOrder
