module

public import Foundation.FirstOrder.Incompleteness.Examples
public import Foundation.Vorspiel.ENat

@[expose] public section
namespace FFL.FirstOrder

variable {L : Language} [L.ReferenceableBy L] {T₀ T : Theory L}

open ProvabilityAbstraction

namespace ProvabilityAbstraction

variable {𝔅 : Provability T₀ T}

open scoped Classical in
noncomputable def Provability.height (𝔅 : Provability T₀ T) : ENat := ENat.find (T ⊢ 𝔅^[·] ⊥)

@[simp]
lemma neg_iterated_prov {n : ℕ} (φ : Sentence L) : ∼(𝔅^[n] φ) = 𝔅.dia^[n] (∼φ) := by
  induction n generalizing φ <;> simp [Provability.dia, *]

/-- The `n`-times iterated consistency `∼𝔅^[n] ⊥`. -/
def Provability.conItr (𝔅 : Provability T₀ T) (n : ℕ) : Sentence L := ∼𝔅^[n] ⊥

lemma Provability.provable_boxItr_bot_mono [𝔅.HBL3] {n m : ℕ} (h : n ≤ m) :
    T₀ ⊢ 𝔅^[n] ⊥ 🡒 𝔅^[m] ⊥ := by
  induction m, h using Nat.le_induction with
  | base => exact Entailment.C_id
  | succ m _ ih =>
    suffices T₀ ⊢ 𝔅^[m] ⊥ 🡒 𝔅^[m + 1] ⊥ from Entailment.C_trans ih this;
    rcases m with _ | m;
    · exact Entailment.efq;
    · simpa only [Function.iterate_succ_apply'] using 𝔅.D3;

lemma boxBot_monotone [T₀ ⪯ T] [𝔅.HBL] {n m : ℕ} (h : n ≤ m) : T ⊢ 𝔅^[n] ⊥ 🡒 𝔅^[m] ⊥ :=
  Entailment.WeakerThan.pbl <| 𝔅.provable_boxItr_bot_mono h

lemma iIncon_unprovable_of_sigma1_sound [𝔅.Kreisel] [Entailment.Consistent T] : ∀ n, T ⊬ 𝔅^[n] ⊥
  |     0 => Entailment.consistent_iff_unprovable_bot.mp inferInstance
  | n + 1 => fun h ↦
    have : T ⊢ 𝔅 (𝔅^[n] ⊥) := by simpa [Function.iterate_succ_apply'] using h
    iIncon_unprovable_of_sigma1_sound n <| 𝔅.KR this


namespace Provability


lemma height_eq_top_iff : 𝔅.height = ⊤ ↔ ∀ n, T ⊬ 𝔅^[n] ⊥ := ENat.find_eq_top_iff _

lemma height_le_of_boxBot {n : ℕ} (h : T ⊢ 𝔅^[n] ⊥) : 𝔅.height ≤ n :=
  ENat.find_le (T ⊢ 𝔅^[·] ⊥) n h

lemma height_lt_pos_of_boxBot (hSound : ∀ {σ}, T₀ ⊢ 𝔅 σ → T ⊢ σ)
  {n : ℕ} (pos : 0 < n) (h : T₀ ⊢ 𝔅^[n] ⊥) : 𝔅.height < n := by
  have e : n.pred.succ = n := Eq.symm <| (Nat.sub_eq_iff_eq_add pos).mp rfl
  have : T₀ ⊢ 𝔅 (𝔅^[n.pred] ⊥) := by rwa [←Function.iterate_succ_apply' (f := 𝔅), e];
  have : 𝔅.height ≤ n.pred := height_le_of_boxBot <| hSound this
  have : 𝔅.height < n := by
    rw [←e]
    exact lt_of_le_of_lt this <| ENat.natCast_lt_natCast.mpr <| by simp
  exact this

lemma height_le_iff_boxBot [T₀ ⪯ T] [𝔅.HBL] {n : ℕ} :
    𝔅.height ≤ n ↔ T ⊢ 𝔅^[n] ⊥ := by
  constructor
  · intro h
    have : ∃ m ≤ n, T ⊢ (↑𝔅)^[m] ⊥ := ENat.exists_of_find_le _ n h
    rcases this with ⟨m, hmn, hm⟩
    exact boxBot_monotone hmn ⨀ hm
  · exact height_le_of_boxBot

lemma height_eq_top_of_sound_and_consistent [𝔅.Kreisel] [Entailment.Consistent T] : 𝔅.height = ⊤ :=
  height_eq_top_iff.mpr iIncon_unprovable_of_sigma1_sound

@[grind =>]
lemma height_eq_zero_of_inconsistent (h : Entailment.Inconsistent T) : 𝔅.height = 0 := by
  suffices 𝔅.height ≤ 0 from le_bot_iff.mp this
  exact height_le_of_boxBot (n := 0) (h ⊥)

end Provability

end ProvabilityAbstraction


open ProvabilityAbstraction

noncomputable abbrev ArithmeticTheory.height (T : ArithmeticTheory) [T.Δ₁] : ℕ∞ :=
  T.standardProvability.height

namespace Arithmetic

@[grind =]
lemma height_eq_top_of_sigma1_sound (T : ArithmeticTheory) [T.Δ₁]
    [ArithmeticTheory.SoundOnHierarchy T 𝚺 1] : T.height = ⊤ :=
  T.standardProvability.height_eq_top_of_sound_and_consistent

section

variable {T : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T] {n : ℕ}

lemma models_boxBot_iff : ℕ↓[ℒₒᵣ] ⊧ T.standardProvability^[n + 1] ⊥ ↔ T.height ≤ n := by
  simpa [Function.iterate_succ_apply', models_standardProvability_iff] using
    Provability.height_le_iff_boxBot.symm;

end

@[simp, grind =]
lemma ISigma1_height_eq_top : 𝗜𝚺⁺₁.height = ⊤ := height_eq_top_of_sigma1_sound 𝗜𝚺⁺₁

@[simp, grind =]
lemma Peano_height_eq_top : 𝗣𝗔.height = ⊤ := height_eq_top_of_sigma1_sound 𝗣𝗔

end Arithmetic

end FFL.FirstOrder
