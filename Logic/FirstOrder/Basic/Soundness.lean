import Logic.FirstOrder.Basic.Semantics.Semantics
import Logic.FirstOrder.Basic.Calculus

namespace LO

namespace FirstOrder

section soundness
open Semiformula

variable {L : Language}

namespace Derivation

lemma sound : ∀ {Γ : Sequent L}, ⊢¹ Γ →
    ∀ (M : Type u) [s : Structure L M] (ε : ℕ → M), ∃ p ∈ Γ, Val! M ε p
  | _, @axL _ Δ _ r v,     M, s, ε => by
    by_cases h : s.rel r (Semiterm.val! M ![] ε ∘ v)
    · exact ⟨rel r v, by simp, h⟩
    · exact ⟨nrel r v, by simp, h⟩
  | _, verum Δ,            M, s, ε => ⟨⊤, by simp⟩
  | _, @or _ Δ p q d,      M, s, ε => by
    have : Val! M ε p ∨ Val! M ε q ∨ ∃ q ∈ Δ, Val! M ε q := by simpa using sound d M ε
    rcases this with (hp | hq | ⟨r, hr, hhr⟩)
    · exact ⟨p ⋎ q, by simp, by simp[hp]⟩
    · exact ⟨p ⋎ q, by simp, by simp[hq]⟩
    · exact ⟨r, by simp[hr], hhr⟩
  | _, @and _ Δ p q dp dq, M, s, ε => by
    have : Val! M ε p ∨ ∃ r ∈ Δ, Val! M ε r := by simpa using sound dp M ε
    rcases this with (hp | ⟨r, hr, hhr⟩)
    · have : Val! M ε q ∨ ∃ r ∈ Δ, Val! M ε r := by simpa using sound dq M ε
      rcases this with (hq | ⟨r, hr, hhr⟩)
      · exact ⟨p ⋏ q, by simp, by simp[hp, hq]⟩
      · exact ⟨r, by simp[hr], hhr⟩
    · exact ⟨r, by simp[hr], hhr⟩
  | _, @all _ Δ p d,       M, s, ε => by
    have : (∀ a : M, Eval! M ![a] ε p) ∨ ∃ q ∈ Δ, Val! M ε q := by
      simpa[shifts, shiftEmb, Matrix.vecConsLast_vecEmpty, forall_or_right]
        using fun a : M => sound d M (a :>ₙ ε)
    rcases this with (hp | ⟨q, hq, hhq⟩)
    · exact ⟨∀' p, by simp, hp⟩
    · exact ⟨q, by simp[hq], hhq⟩
  | _, @ex _ Δ p t d,      M, s, ε => by
    have : Eval! M ![t.val! M ![] ε] ε p ∨ ∃ p ∈ Δ, Val! M ε p := by
      simpa[eval_substs, Matrix.constant_eq_singleton] using sound d M ε
    rcases this with (hp | ⟨q, hq, hhq⟩)
    · exact ⟨∃' p, by simp, t.val! M ![] ε, hp⟩
    · exact ⟨q, by simp[hq], hhq⟩
  | _, @wk _ Δ Γ d ss,     M, s, ε => by
    have : ∃ p ∈ Δ, Val! M ε p := sound d M ε
    rcases this with ⟨p, hp, h⟩
    exact ⟨p, ss hp, h⟩
  | _, @cut _ Δ p d dn,    M, s, ε => by
    have h : Val! M ε p ∨ ∃ q ∈ Δ, Val! M ε q := by simpa using sound d M ε
    have hn : ¬Val! M ε p ∨ ∃ q ∈ Δ, Val! M ε q := by simpa using sound dn M ε
    rcases h with (h | ⟨q, h, hq⟩)
    · rcases hn with (hn | ⟨q, hn, hq⟩)
      · contradiction
      · exact ⟨q, by simp[hn], hq⟩
    · exact ⟨q, by simp[h], hq⟩

end Derivation

theorem soundness {T} {σ : Sentence L} : T ⊢ σ → T ⊨ σ := fun b s hT => by
  rcases s.nonempty with ⟨x⟩
  rcases Derivation.sound b.derivation s.Dom (fun _ ↦ x) with ⟨p, hp, h⟩
  simp at hp; rcases hp with (⟨π, hπ, rfl⟩ | rfl)
  · have : s ⊧ π := hT.RealizeSet (b.antecedent_ss π hπ)
    have : ¬s ⊧ π := by simpa using h
    contradiction
  · simpa using h

theorem soundness' {T} {σ : Sentence L} : T ⊢! σ → T ⊨ σ := fun ⟨b⟩ ↦ soundness b

instance : Sound (Sentence L) := ⟨soundness⟩

end soundness

end FirstOrder

end LO
