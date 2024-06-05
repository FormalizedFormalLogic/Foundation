import Logic.FirstOrder.Basic.Semantics.Semantics
import Logic.FirstOrder.Basic.Calculus

namespace LO

namespace FirstOrder

section sound
open Semiformula

variable {L : Language}

namespace Derivation

lemma sound : ∀ {Γ : Sequent L}, ⊢¹ Γ →
    ∀ (M : Type*) [s : Structure L M] (ε : ℕ → M), ∃ p ∈ Γ, Evalfm M ε p
  | _, @axL _ Δ _ r v,     M, s, ε => by
    by_cases h : s.rel r (Semiterm.valm M ![] ε ∘ v)
    · exact ⟨rel r v, by simp, h⟩
    · exact ⟨nrel r v, by simp, h⟩
  | _, verum Δ,            M, s, ε => ⟨⊤, by simp⟩
  | _, @or _ Δ p q d,      M, s, ε => by
    have : Evalfm M ε p ∨ Evalfm M ε q ∨ ∃ q ∈ Δ, Evalfm M ε q := by simpa using sound d M ε
    rcases this with (hp | hq | ⟨r, hr, hhr⟩)
    · exact ⟨p ⋎ q, by simp, by simp [hp]⟩
    · exact ⟨p ⋎ q, by simp, by simp [hq]⟩
    · exact ⟨r, by simp [hr], hhr⟩
  | _, @and _ Δ p q dp dq, M, s, ε => by
    have : Evalfm M ε p ∨ ∃ r ∈ Δ, Evalfm M ε r := by simpa using sound dp M ε
    rcases this with (hp | ⟨r, hr, hhr⟩)
    · have : Evalfm M ε q ∨ ∃ r ∈ Δ, Evalfm M ε r := by simpa using sound dq M ε
      rcases this with (hq | ⟨r, hr, hhr⟩)
      · exact ⟨p ⋏ q, by simp, by simp [hp, hq]⟩
      · exact ⟨r, by simp [hr], hhr⟩
    · exact ⟨r, by simp [hr], hhr⟩
  | _, @all _ Δ p d,       M, s, ε => by
    have : (∀ a : M, Evalm M ![a] ε p) ∨ ∃ q ∈ Δ, Evalfm M ε q := by
      simpa[shifts, shiftEmb, Matrix.vecConsLast_vecEmpty, forall_or_right]
        using fun a : M => sound d M (a :>ₙ ε)
    rcases this with (hp | ⟨q, hq, hhq⟩)
    · exact ⟨∀' p, by simp, hp⟩
    · exact ⟨q, by simp [hq], hhq⟩
  | _, @ex _ Δ p t d,      M, s, ε => by
    have : Evalm M ![t.valm M ![] ε] ε p ∨ ∃ p ∈ Δ, Evalfm M ε p := by
      simpa[eval_substs, Matrix.constant_eq_singleton] using sound d M ε
    rcases this with (hp | ⟨q, hq, hhq⟩)
    · exact ⟨∃' p, by simp, t.valm M ![] ε, hp⟩
    · exact ⟨q, by simp [hq], hhq⟩
  | _, @wk _ Δ Γ d ss,     M, s, ε => by
    have : ∃ p ∈ Δ, Evalfm M ε p := sound d M ε
    rcases this with ⟨p, hp, h⟩
    exact ⟨p, ss hp, h⟩
  | _, @cut _ Δ p d dn,    M, s, ε => by
    have h : Evalfm M ε p ∨ ∃ q ∈ Δ, Evalfm M ε q := by simpa using sound d M ε
    have hn : ¬Evalfm M ε p ∨ ∃ q ∈ Δ, Evalfm M ε q := by simpa using sound dn M ε
    rcases h with (h | ⟨q, h, hq⟩)
    · rcases hn with (hn | ⟨q, hn, hq⟩)
      · contradiction
      · exact ⟨q, by simp [hn], hq⟩
    · exact ⟨q, by simp [h], hq⟩

end Derivation

theorem sound {T} {σ : Sentence L} : T ⊢ σ → T ⊨[Struc.{v, u} L] σ := fun b s hT => by
  rcases s.nonempty with ⟨x⟩
  rcases Derivation.sound b.derivation s.Dom (fun _ ↦ x) with ⟨p, hp, h⟩
  simp at hp; rcases hp with (⟨π, hπ, rfl⟩ | rfl)
  · have : s ⊧ π := hT.RealizeSet (Gentzen.Disjconseq.subset b π hπ)
    have : ¬s ⊧ π := by simpa using h
    contradiction
  · simpa using h

theorem sound! {T} {σ : Sentence L} : T ⊢! σ → T ⊨[Struc.{v, u} L] σ := fun ⟨b⟩ ↦ sound b

theorem sound₀ {T} {σ : Sentence L} : T ⊢ σ → T ⊨ σ := sound

theorem sound₀! {T} {σ : Sentence L} : T ⊢! σ → T ⊨ σ := sound!

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
