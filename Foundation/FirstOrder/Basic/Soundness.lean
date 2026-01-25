module
public import Foundation.FirstOrder.Basic.Semantics.Semantics
public import Foundation.FirstOrder.Basic.Calculus
@[expose] public section

namespace LO

namespace FirstOrder

section sound
open Semiformula

variable {L : Language} {T : Theory L}

namespace Derivation

lemma sound (M : Type*) [s : Structure L M] [Nonempty M] [M ⊧ₘ* T] (ε : ℕ → M) {Γ : Sequent L} :
    (T : SyntacticFormulas L) ⟹ Γ → ∃ φ ∈ Γ, Evalfm M ε φ
  | @axL _ _ Δ _ r v => by
    by_cases h : s.rel r (Semiterm.valm M ![] ε ∘ v)
    · exact ⟨rel r v, by simp, h⟩
    · exact ⟨nrel r v, by simp, h⟩
  | verum Δ => ⟨⊤, by simp⟩
  | @or _ _ Δ φ ψ d => by
    have : Evalfm M ε φ ∨ Evalfm M ε ψ ∨ ∃ ψ ∈ Δ, Evalfm M ε ψ := by simpa using sound M ε d
    rcases this with (hp | hq | ⟨r, hr, hhr⟩)
    · exact ⟨φ ⋎ ψ, by simp, by simp [hp]⟩
    · exact ⟨φ ⋎ ψ, by simp, by simp [hq]⟩
    · exact ⟨r, by simp [hr], hhr⟩
  | @and _ _ Δ φ ψ dp dq => by
    have : Evalfm M ε φ ∨ ∃ r ∈ Δ, Evalfm M ε r := by simpa using sound M ε dp
    rcases this with (hp | ⟨r, hr, hhr⟩)
    · have : Evalfm M ε ψ ∨ ∃ r ∈ Δ, Evalfm M ε r := by simpa using sound M ε dq
      rcases this with (hq | ⟨r, hr, hhr⟩)
      · exact ⟨φ ⋏ ψ, by simp, by simp [hp, hq]⟩
      · exact ⟨r, by simp [hr], hhr⟩
    · exact ⟨r, by simp [hr], hhr⟩
  | @all _ _ Δ φ d => by
    have : (∀ a : M, Evalm M ![a] ε φ) ∨ ∃ ψ ∈ Δ, Evalfm M ε ψ := by
      simpa [Rewriting.shifts, Matrix.vecConsLast_vecEmpty, forall_or_right]
        using fun a : M => sound M (a :>ₙ ε) d
    rcases this with (hp | ⟨ψ, hq, hhq⟩)
    · exact ⟨∀' φ, by simp, hp⟩
    · exact ⟨ψ, by simp [hq], hhq⟩
  | @ex _ _ Δ φ t d => by
    have : Evalm M ![t.valm M ![] ε] ε φ ∨ ∃ φ ∈ Δ, Evalfm M ε φ := by
      simpa [eval_substs, Matrix.constant_eq_singleton] using sound M ε d
    rcases this with (hp | ⟨ψ, hq, hhq⟩)
    · exact ⟨∃' φ, by simp, t.valm M ![] ε, hp⟩
    · exact ⟨ψ, by simp [hq], hhq⟩
  | @wk _ _ Γ Δ d ss => by
    have : ∃ φ ∈ Δ, Evalfm M ε φ := sound M ε d
    rcases this with ⟨φ, hp, h⟩
    exact ⟨φ, ss hp, h⟩
  | @cut _ _ Δ φ d dn => by
    have h : Evalfm M ε φ ∨ ∃ ψ ∈ Δ, Evalfm M ε ψ := by simpa using sound M ε d
    have hn : ¬Evalfm M ε φ ∨ ∃ ψ ∈ Δ, Evalfm M ε ψ := by simpa using sound M ε dn
    rcases h with (h | ⟨ψ, h, hq⟩)
    · rcases hn with (hn | ⟨ψ, hn, hq⟩)
      · contradiction
      · exact ⟨ψ, by simp [hn], hq⟩
    · exact ⟨ψ, by simp [h], hq⟩
  | axm (φ := φ) h => ⟨φ, by simp, by
      have : ∃ σ ∈ T, ↑σ = φ := by
        simpa [Theory.toSyntacticFormulas] using h
      rcases this with ⟨σ, hσ, rfl⟩
      simpa using Theory.models M T hσ⟩

end Derivation

theorem sound : T ⊢! σ → T ⊨[Struc.{v, u} L] σ := fun b s hT ↦ by
  have : s.Dom ⊧ₘ* T := hT
  have : Inhabited s.Dom := Classical.inhabited_of_nonempty s.nonempty
  simpa using Derivation.sound s.Dom default b

theorem sound! : T ⊢ σ → T ⊨[Struc.{v, u} L] σ := fun ⟨b⟩ ↦ sound b

theorem smallSound : T ⊢! σ → T ⊨ σ := sound

theorem smallSound! : T ⊢ σ → T ⊨ σ := sound!

instance (T : Theory L) : Sound T (Semantics.models (Struc.{v, u} L) T) := ⟨sound!⟩

lemma models_of_subtheory {T U : Theory L} [U ⪯ T] {M : Type*} [Structure L M] [Nonempty M] (hM : M ⊧ₘ* T) : M ⊧ₘ* U :=
  ⟨ fun {φ} hp ↦ by
    have : T ⊢ φ := (inferInstanceAs (U ⪯ T)).pbl (Entailment.by_axm _ hp)
    exact sound! this hM ⟩

lemma consistent_of_satisfiable (h : Semantics.Satisfiable (Struc.{v, u} L) T) : Entailment.Consistent T :=
  Sound.consistent_of_satisfiable h

lemma consistent_of_model (T : Theory L) (M : Type*) [s : Structure L M] [Nonempty M] [hM : M ⊧ₘ* T] :
    Entailment.Consistent T := consistent_of_satisfiable ⟨s.toStruc, hM⟩

lemma unprovable_of_countermodel {M : Type*} [s : Structure L M] [Nonempty M] [hM : M ⊧ₘ* T]
    {σ} (c : ¬M ⊧ₘ σ) : T ⊬ σ := by
  apply Sound.not_provable_of_countermodel (𝓜 := Semantics.models (Struc L) T) (𝓢 := T)
  intro h
  exact c (h hM)

lemma models_of_provable {M : Type*} [Nonempty M] [Structure L M] (hT : M ⊧ₘ* T) (h : T ⊢ σ) :
    M ⊧ₘ σ := consequence_iff.mp (sound! h) M inferInstance

end sound

end FirstOrder

end LO

end
