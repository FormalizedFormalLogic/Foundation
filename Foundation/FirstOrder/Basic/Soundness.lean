import Foundation.FirstOrder.Basic.Semantics.Semantics
import Foundation.FirstOrder.Basic.Calculus

namespace LO

namespace FirstOrder

section sound
open Semiformula

variable {L : Language} {T : Theory L}

namespace Derivation

lemma sound (M : Type*) [s : Structure L M] [Nonempty M] [M ⊧ₘ* T] (ε : ℕ → M) {Γ : Sequent L} : T ⟹ Γ → ∃ φ ∈ Γ, Evalfm M ε φ
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
      simpa[eval_substs, Matrix.constant_eq_singleton] using sound M ε d
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
  | root (φ := φ) h => ⟨φ, by simp, Theory.models M T h ε⟩

end Derivation

variable {φ : SyntacticFormula L}

theorem sound : T ⊢ φ → T ⊨[Struc.{v, u} L] φ := fun b s hT f ↦ by
  haveI : s.Dom ⊧ₘ* T := hT
  rcases Derivation.sound s.Dom f b with ⟨ψ, hp, h⟩
  have : ψ = φ := by simpa using hp
  rcases this
  exact h

theorem sound! : T ⊢! φ → T ⊨[Struc.{v, u} L] φ := fun ⟨b⟩ ↦ sound b

theorem sound₀ : T ⊢ φ → T ⊨ φ := sound

theorem sound₀! : T ⊢! φ → T ⊨ φ := sound!

instance (T : Theory L) : Sound T (Semantics.models (Struc.{v, u} L) T) := ⟨sound!⟩

lemma models_of_subtheory {T U : Theory L} [U ⪯ T] {M : Type*} [Structure L M] [Nonempty M] (hM : M ⊧ₘ* T) : M ⊧ₘ* U :=
  ⟨ fun {φ} hp ↦ by
    have : T ⊢! φ := (inferInstanceAs (U ⪯ T)).pbl (System.by_axm _ hp)
    exact sound! this hM ⟩

lemma consistent_of_satidfiable (h : Semantics.Satisfiable (Struc.{v, u} L) T) : System.Consistent T :=
  Sound.consistent_of_satisfiable h

end sound

end FirstOrder

end LO
