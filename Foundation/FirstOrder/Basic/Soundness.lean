module
public import Foundation.FirstOrder.Basic.Semantics.Semantics
public import Foundation.FirstOrder.Basic.Calculus
@[expose] public section

/-! # Soundness theorem for first-order classical logic -/

namespace LO

namespace FirstOrder

section sound
open Semiformula

variable {L : Language}

namespace Derivation

lemma sound {M : Type*} [s : Structure L M] [Nonempty M] (f : ℕ → M) {Γ : Sequent L} :
    ⊢ᴷ Γ → ∃ φ ∈ Γ, φ.Evalf f
  | identity r v => by
    by_cases h : s.rel r (Semiterm.val ![] f ∘ v)
    · exact ⟨rel r v, by simp, h⟩
    · exact ⟨nrel r v, by simp, h⟩
  | verum => ⟨⊤, by simp⟩
  | or (Γ := Γ) (φ := φ) (ψ := ψ) d => by
    have : Evalf f φ ∨ Evalf f ψ ∨ ∃ ψ ∈ Γ, Evalf f ψ := by simpa using sound f d
    rcases this with (hp | hq | ⟨r, hr, hhr⟩)
    · exact ⟨φ ⋎ ψ, by simp, by simp [hp]⟩
    · exact ⟨φ ⋎ ψ, by simp, by simp [hq]⟩
    · exact ⟨r, by simp [hr], hhr⟩
  | and (Γ := Γ) (φ := φ) (ψ := ψ) dp dq => by
    have : Evalf f φ ∨ ∃ r ∈ Γ, Evalf f r := by simpa using sound f dp
    rcases this with (hp | ⟨r, hr, hhr⟩)
    · have : Evalf f ψ ∨ ∃ r ∈ Γ, Evalf f r := by simpa using sound f dq
      rcases this with (hq | ⟨r, hr, hhr⟩)
      · exact ⟨φ ⋏ ψ, by simp, by simp [hp, hq]⟩
      · exact ⟨r, by simp [hr], hhr⟩
    · exact ⟨r, by simp [hr], hhr⟩
  | all (Γ := Γ) (φ := φ) d => by
    have : (∀ a : M, Eval ![a] f φ) ∨ ∃ ψ ∈ Γ, Evalf f ψ := by
      simpa [Rewriting.shifts, Matrix.vecConsLast_vecEmpty, forall_or_right]
        using fun a : M => sound (a :>ₙ f) d
    rcases this with (hp | ⟨ψ, hq, hhq⟩)
    · exact ⟨∀⁰ φ, by simp, hp⟩
    · exact ⟨ψ, by simp [hq], hhq⟩
  | exs (Γ := Γ) (φ := φ) (t := t) d => by
    have : Eval ![t.val ![] f] f φ ∨ ∃ φ ∈ Γ, Evalf f φ := by
      simpa [eval_substs, Matrix.constant_eq_singleton] using sound f d
    rcases this with (hp | ⟨ψ, hq, hhq⟩)
    · exact ⟨∃⁰ φ, by simp, t.val ![] f, hp⟩
    · exact ⟨ψ, by simp [hq], hhq⟩
  | wk (Δ := Δ) (Γ := Γ) d ss => by
    have : ∃ φ ∈ Δ, Evalf f φ := sound f d
    rcases this with ⟨φ, hp, h⟩
    exact ⟨φ, ss hp, h⟩
  | cut (Γ := Γ) (Δ := Δ) (φ := φ) d dn => by
    have h : Evalf f φ ∨ ∃ ψ ∈ Γ, Evalf f ψ := by simpa using sound f d
    have hn : ¬Evalf f φ ∨ ∃ ψ ∈ Δ, Evalf f ψ := by simpa using sound f dn
    rcases h with (h | ⟨ψ, h, hq⟩)
    · rcases hn with (hn | ⟨ψ, hn, hq⟩)
      · contradiction
      · exact ⟨ψ, by simp [hn], hq⟩
    · exact ⟨ψ, by simp [h], hq⟩

end Derivation

theorem Provable.sound {M : Type*} [s : Structure L M] [Nonempty M] {φ : Proposition L} (f : ℕ → M) :
    𝐋𝐊¹ ⊢ φ → φ.Evalf f := fun b ↦ by simpa using Derivation.sound f b.get

variable {𝔖 : Schema L}

theorem Schema.sound_proposition {M : Type*} [s : Structure L M] [Nonempty M] :
    𝔖 ⊢ φ → M↓[L] ⊧* 𝔖 → ∀ f : ℕ → M, φ.Evalf f := fun b H f ↦ by
  rcases Schema.provable_iff.mp b with ⟨Γ, hΓ, ⟨b⟩⟩
  have : φ.Evalf f ∨ ∃ ψ, ∼ψ ∈ Γ ∧ ψ.Evalf f := by simpa using b.sound f
  rcases this with (h | ⟨ψ, hψ, h⟩)
  · assumption
  · have : ¬ψ.Evalf f := by
      have := by simpa [models_iff] using H.models _ (φ := (∼ψ).univCl) (by grind only [Schema.mem_uniClosure])
      exact this f
    contradiction

theorem Schema.sound_proposition' :
    𝔖 ⊢ φ → (𝔖 : Theory L) ⊨[Struc.{v, u} L] φ.univCl := fun b s hS ↦ by
  simpa [struc_models_iff_models (s := s), models_iff]
    using Schema.sound_proposition b hS

theorem Schema.sound_sentence {σ : Sentence L} :
    𝔖 ⊢ ↑σ → (𝔖 : Theory L) ⊨[Struc.{v, u} L] σ := fun b ↦ by
  simpa using Schema.sound_proposition' b

theorem Schema.smallSound_sentence {σ : Sentence L} : 𝔖 ⊢ ↑σ → (𝔖 : Theory L) ⊨ σ := Schema.sound_sentence

instance sound (𝔖 : Schema L) :
    Sound (Entailment.pullback 𝔖 ((↑·) : Sentence L → Proposition L)) (Semantics.models (Struc.{v, u} L) 𝔖) :=
  ⟨Schema.sound_sentence⟩

lemma models_of_subtheory {𝔖 𝔗 : Schema L} [𝔖 ⪯ 𝔗] {M : Type*} [Structure L M] [Nonempty M] : M↓[L] ⊧* 𝔗 → M↓[L] ⊧* 𝔖 :=
  fun hM ↦ ⟨fun {σ} hσ ↦ by
    rcases show ∃ φ ∈ 𝔖, univCl φ = σ by simpa using hσ with ⟨φ, hφ, rfl⟩
    have : 𝔗 ⊢ φ := (inferInstanceAs (𝔖 ⪯ 𝔗)).pbl (Entailment.by_axm hφ)
    exact Schema.sound_proposition' this hM⟩

lemma consistent_of_satisfiable (h : Semantics.Satisfiable (Struc.{v, u} L) 𝔖) : Entailment.Consistent 𝔖 :=
  Entailment.Pullback.consistent <| Sound.consistent_of_satisfiable (𝓢 := Entailment.pullback 𝔖 ((↑·) : Sentence L → Proposition L)) h

lemma consistent_of_model (𝔖 : Schema L) (M : Type*) [Structure L M] [Nonempty M] [hM : M↓[L] ⊧* 𝔖] :
    Entailment.Consistent 𝔖 := consistent_of_satisfiable ⟨M↓[L], hM⟩

lemma unprovable_of_countermodel {M : Type*} [Structure L M] [Nonempty M] [hM : M↓[L] ⊧* 𝔖] {σ} : M↓[L] ⊭ σ → 𝔖 ⊬ ↑σ := by
  contrapose!; intro h
  exact Schema.sound_sentence h hM

lemma models_of_provable {M : Type*} [Nonempty M] [Structure L M] (hT : M↓[L] ⊧* 𝔖) {σ : Sentence L} (h : 𝔖 ⊢ ↑σ) :
    M↓[L] ⊧ σ := consequence_iff.mp (Schema.sound_sentence h) M inferInstance

end sound

end FirstOrder

end LO

end
