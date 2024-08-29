import Logic.FirstOrder.Basic.Semantics.Semantics
import Logic.FirstOrder.Basic.Calculus

namespace LO

namespace FirstOrder

section sound
open Semiformula

variable {L : Language} {T : Theory L}

namespace Derivation

lemma sound (M : Type*) [s : Structure L M] [Nonempty M] [M ⊧ₘ* T] (ε : ℕ → M) {Γ : Sequent L} : T ⟹ Γ → ∃ p ∈ Γ, Evalfm M ε p
  | @axL _ _ Δ _ r v => by
    by_cases h : s.rel r (Semiterm.valm M ![] ε ∘ v)
    · exact ⟨rel r v, by simp, h⟩
    · exact ⟨nrel r v, by simp, h⟩
  | verum Δ => ⟨⊤, by simp⟩
  | @or _ _ Δ p q d => by
    have : Evalfm M ε p ∨ Evalfm M ε q ∨ ∃ q ∈ Δ, Evalfm M ε q := by simpa using sound M ε d
    rcases this with (hp | hq | ⟨r, hr, hhr⟩)
    · exact ⟨p ⋎ q, by simp, by simp [hp]⟩
    · exact ⟨p ⋎ q, by simp, by simp [hq]⟩
    · exact ⟨r, by simp [hr], hhr⟩
  | @and _ _ Δ p q dp dq => by
    have : Evalfm M ε p ∨ ∃ r ∈ Δ, Evalfm M ε r := by simpa using sound M ε dp
    rcases this with (hp | ⟨r, hr, hhr⟩)
    · have : Evalfm M ε q ∨ ∃ r ∈ Δ, Evalfm M ε r := by simpa using sound M ε dq
      rcases this with (hq | ⟨r, hr, hhr⟩)
      · exact ⟨p ⋏ q, by simp, by simp [hp, hq]⟩
      · exact ⟨r, by simp [hr], hhr⟩
    · exact ⟨r, by simp [hr], hhr⟩
  | @all _ _ Δ p d => by
    have : (∀ a : M, Evalm M ![a] ε p) ∨ ∃ q ∈ Δ, Evalfm M ε q := by
      simpa[shifts, shiftEmb, Matrix.vecConsLast_vecEmpty, forall_or_right]
        using fun a : M => sound M (a :>ₙ ε) d
    rcases this with (hp | ⟨q, hq, hhq⟩)
    · exact ⟨∀' p, by simp, hp⟩
    · exact ⟨q, by simp [hq], hhq⟩
  | @ex _ _ Δ p t d => by
    have : Evalm M ![t.valm M ![] ε] ε p ∨ ∃ p ∈ Δ, Evalfm M ε p := by
      simpa[eval_substs, Matrix.constant_eq_singleton] using sound M ε d
    rcases this with (hp | ⟨q, hq, hhq⟩)
    · exact ⟨∃' p, by simp, t.valm M ![] ε, hp⟩
    · exact ⟨q, by simp [hq], hhq⟩
  | @wk _ _ Δ Γ d ss => by
    have : ∃ p ∈ Δ, Evalfm M ε p := sound M ε d
    rcases this with ⟨p, hp, h⟩
    exact ⟨p, ss hp, h⟩
  | @cut _ _ Δ p d dn => by
    have h : Evalfm M ε p ∨ ∃ q ∈ Δ, Evalfm M ε q := by simpa using sound M ε d
    have hn : ¬Evalfm M ε p ∨ ∃ q ∈ Δ, Evalfm M ε q := by simpa using sound M ε dn
    rcases h with (h | ⟨q, h, hq⟩)
    · rcases hn with (hn | ⟨q, hn, hq⟩)
      · contradiction
      · exact ⟨q, by simp [hn], hq⟩
    · exact ⟨q, by simp [h], hq⟩
  | root (p := p) h => ⟨p, by simp, Theory.models M T h ε⟩

end Derivation

variable {p : SyntacticFormula L}

theorem sound : T ⊢ p → T ⊨[Struc.{v, u} L] p := fun b s hT f ↦ by
  haveI : s.Dom ⊧ₘ* T := hT
  rcases Derivation.sound s.Dom f b with ⟨p, hp, h⟩
  simp at hp; rcases hp with rfl
  exact h

theorem sound! : T ⊢! p → T ⊨[Struc.{v, u} L] p := fun ⟨b⟩ ↦ sound b

theorem sound₀ : T ⊢ p → T ⊨ p := sound

theorem sound₀! : T ⊢! p → T ⊨ p := sound!

instance (T : Theory L) : Sound T (Semantics.models (Struc.{v, u} L) T) := ⟨sound!⟩

lemma models_of_subtheory {T U : Theory L} [U ≼ T] {M : Type*} [Structure L M] [Nonempty M] (hM : M ⊧ₘ* T) : M ⊧ₘ* U :=
  ⟨ fun {p} hp ↦ by
    have : T ⊢ p := System.Subtheory.prf (System.byAxm hp)
    exact sound this hM ⟩

lemma consistent_of_satidfiable (h : Semantics.Satisfiable (Struc.{v, u} L) T) : System.Consistent T :=
  Sound.consistent_of_satisfiable h

end sound

end FirstOrder

end LO
