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
    ⊢ᴸᴷ¹ Γ → ∃ φ ∈ Γ, φ.Evalf f
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

@[simp] lemma nil_empty : IsEmpty (⊢ᴸᴷ¹ ([] : Sequent L)) := by
  refine ⟨fun b ↦ ?_⟩
  simpa using sound (fun _ ↦ ()) b

end Derivation

theorem Provable.sound {M : Type*} [s : Structure L M] [Nonempty M] {φ : Proposition L} (f : ℕ → M) :
    𝐋𝐊¹ ⊢ φ → φ.Evalf f := fun b ↦ by simpa using Derivation.sound f b.get

variable {T : Theory L}

theorem Theory.Proof.sound_proposition {M : Type*} [s : Structure L M] [Nonempty M] :
    T ⊢ φ → M↓[L] ⊧* T → φ.Realize M := fun b H ↦ by
  rcases Theory.Proof.provable_iff.mp b with ⟨Γ, hΓ, ⟨b⟩⟩
  have : Inhabited M := Classical.inhabited_of_nonempty inferInstance
  let f : ℕ → M := fun _ ↦ default
  have : φ.Realize M ∨ ∃ ψ, ∼ψ ∈ Sequent.embed Γ ∧ ψ.Evalf f := by simpa using b.sound f
  rcases this with (h | ⟨ψ, hψ, h⟩)
  · assumption
  · have : ∃ χ, ∼χ ∈ Γ ∧ ↑χ = ψ := by
      have : ∃ χ ∈ Γ, χ = ∼ψ := by simpa [Sequent.embed] using hψ
      rcases this with ⟨χ, hχ, e⟩
      refine ⟨∼χ, by simpa using hχ, by simp [e]⟩
    rcases this with ⟨χ, hχ, rfl⟩
    have : χ.Realize M := by simpa using h
    have : ¬χ.Realize M := by
      simpa [models_iff] using H.models _ (hΓ _ hχ)
    contradiction

theorem Theory.Proof.sound {φ : Sentence L} :
    T ⊢ φ → T ⊨[Struc.{v, u} L] φ := fun b s hS ↦ by
  simpa [struc_models_iff_models (s := s), models_iff]
    using Theory.Proof.sound_proposition b hS

theorem Theory.Proof.sound_small : T ⊢ φ → T ⊨ φ := Theory.Proof.sound

instance sound (T : Theory L) : Sound T (Semantics.models (Struc.{v, u} L) T) := ⟨Theory.Proof.sound⟩

lemma models_of_subtheory {T U : Theory L} [T ⪯ U] {M : Type*} [Structure L M] [Nonempty M] : M↓[L] ⊧* U → M↓[L] ⊧* T :=
  fun hM ↦ ⟨fun {φ} hφ ↦ by
    have : T ⪯ U := inferInstance
    have : U ⊢ φ := this.pbl (Entailment.by_axm hφ)
    exact Theory.Proof.sound this hM⟩

lemma consistent_of_satisfiable (h : Semantics.Satisfiable (Struc.{v, u} L) T) : Entailment.Consistent T :=
  Sound.consistent_of_satisfiable h

lemma consistent_of_model (T : Theory L) (M : Type*) [Structure L M] [Nonempty M] [hM : M↓[L] ⊧* T] :
    Entailment.Consistent T := consistent_of_satisfiable ⟨M↓[L], hM⟩

lemma unprovable_of_countermodel {M : Type*} [Structure L M] [Nonempty M] [hM : M↓[L] ⊧* T] {φ} : M↓[L] ⊭ φ → T ⊬ φ := by
  contrapose!; intro h
  exact Theory.Proof.sound h hM

lemma models_of_provable {M : Type*} [Nonempty M] [Structure L M] (hT : M↓[L] ⊧* ↑↑T) {φ : Sentence L} (h : T ⊢ φ) :
    M↓[L] ⊧ φ := consequence_iff.mp (Theory.Proof.sound h) M inferInstance

end sound

end FirstOrder

end LO

end
