import Foundation.FirstOrder.Incompleteness.Examples
import Foundation.FirstOrder.Internal.DerivabilityCondition
import Foundation.ProvabilityLogic.Provability
import Foundation.Vorspiel.ENat

namespace LO.ProvabilityLogic.Provability

open FirstOrder

variable {L : Language} [L.ReferenceableBy L] {T₀ T : Theory L} {𝔅 : Provability T₀ T}

@[simp] lemma neg_iterated_prov (φ : Sentence L) : ∼(𝔅^[n] φ) = 𝔅.dia^[n] (∼φ) := by
  induction n generalizing φ <;> simp [dia, *]

open Classical

lemma boxBot_monotone [T₀ ⪯ T] [𝔅.HBL] : n ≤ m → T ⊢ 𝔅^[n] ⊥ ➝ 𝔅^[m] ⊥ := by
  revert m
  suffices ∀ k, T ⊢ 𝔅^[n] ⊥ ➝ 𝔅^[n + k] ⊥ by
    intro m hnm
    simpa [Nat.add_sub_of_le hnm] using this (m - n)
  intro k
  induction k
  case zero => simp
  case succ k ih =>
    simp only [← add_assoc, Function.iterate_succ_apply']
    have b₀ : T ⊢ 𝔅^[n] ⊥ ➝ 𝔅 (𝔅^[n] ⊥) := by
      cases n
      · simp
      · simpa only [Function.iterate_succ_apply'] using 𝔅.D3_shift
    have b₁ : T ⊢ 𝔅 (𝔅^[n] ⊥) ➝ 𝔅 (𝔅^[n + k] ⊥) := 𝔅.prov_distribute_imply'' ih
    cl_prover [b₀, b₁]

open Classical

variable (𝔅)

noncomputable def height : ENat := ENat.find (T ⊢ 𝔅^[·] ⊥)

noncomputable abbrev _root_.LO.FirstOrder.ArithmeticTheory.height (T : ArithmeticTheory) [T.Δ₁] : ℕ∞ :=
  T.standardProvability.height

variable {𝔅}

lemma height_eq_top_iff : 𝔅.height = ⊤ ↔ ∀ n, T ⊬ 𝔅^[n] ⊥ := ENat.find_eq_top_iff _

variable (𝔅)

lemma iIncon_unprovable_of_sigma1_sound [𝔅.Sound] [Entailment.Consistent T] : ∀ n, T ⊬ 𝔅^[n] ⊥
  |     0 => Entailment.consistent_iff_unprovable_bot.mp inferInstance
  | n + 1 => fun h ↦
    have : T ⊢ 𝔅 (𝔅^[n] ⊥) := by simpa [Function.iterate_succ_apply'] using h
    iIncon_unprovable_of_sigma1_sound n <| Sound.sound this

lemma height_le_of_boxBot {n : ℕ} (h : T ⊢ 𝔅^[n] ⊥) : 𝔅.height ≤ n :=
  ENat.find_le (T ⊢ 𝔅^[·] ⊥) n h

lemma height_lt_pos_of_boxBot [𝔅.Sound₀] {n : ℕ} (pos : 0 < n) (h : T₀ ⊢ 𝔅^[n] ⊥) : 𝔅.height < n := by
  have e : n.pred.succ = n := Eq.symm <| (Nat.sub_eq_iff_eq_add pos).mp rfl
  have : T₀ ⊢ 𝔅 (𝔅^[n.pred] ⊥) := by
    rwa [←Function.iterate_succ_apply' (f := 𝔅), e]
  have := 𝔅.height_le_of_boxBot (Sound₀.sound₀ this)
  have : 𝔅.height < n := by
    rw [←e]
    exact lt_of_le_of_lt this <| ENat.coe_lt_coe.mpr <| by simp
  exact this

variable {𝔅}

lemma height_le_iff_boxBot [T₀ ⪯ T] [𝔅.HBL] {n : ℕ} :
    𝔅.height ≤ n ↔ T ⊢ 𝔅^[n] ⊥ := by
  constructor
  · intro h
    have : ∃ m ≤ n, T ⊢ (↑𝔅)^[m] ⊥ := ENat.exists_of_find_le _ n h
    rcases this with ⟨m, hmn, hm⟩
    exact 𝔅.boxBot_monotone hmn ⨀ hm
  · exact 𝔅.height_le_of_boxBot

variable (𝔅)

lemma hight_eq_top_of_sound_and_consistent [𝔅.Sound] [Entailment.Consistent T] : 𝔅.height = ⊤ :=
  height_eq_top_iff.mpr 𝔅.iIncon_unprovable_of_sigma1_sound

lemma hight_eq_zero_of_inconsistent (h : Entailment.Inconsistent T) : 𝔅.height = 0 := by
  suffices 𝔅.height ≤ 0 from nonpos_iff_eq_zero.mp this
  simpa using 𝔅.height_le_of_boxBot (n := 0) (h ⊥)

lemma hight_eq_top_of_sigma1_sound (T : ArithmeticTheory) [T.Δ₁] [ArithmeticTheory.SoundOnHierarchy T 𝚺 1] :
    T.height = ⊤ :=
  hight_eq_top_of_sound_and_consistent _

@[simp] lemma ISigma1_hight_eq_top : 𝗜𝚺₁.height = ⊤ := hight_eq_top_of_sigma1_sound 𝗜𝚺₁

@[simp] lemma Peano_hight_eq_top : 𝗣𝗔.height = ⊤ := hight_eq_top_of_sigma1_sound 𝗣𝗔

end LO.ProvabilityLogic.Provability
