import Logic.Predicate.FirstOrder.Basic.Semantics
import Logic.Predicate.FirstOrder.Basic.Calculus

namespace LO

namespace FirstOrder

section soundness

variable {L : Language.{u}} [∀ k, DecidableEq (L.func k)] [∀ k, DecidableEq (L.rel k)]

variable {P : SyntacticFormula L → Prop}

namespace DerivationCR

lemma sound : ∀ {Γ : Sequent L}, ⊢ᶜ[P] Γ → ∀ (M : Type u) [s : Structure L M] (ε : ℕ → M), ∃ p ∈ Γ, Subformula.Val! M ε p
  | _, axL Δ r v hrel hnrel, M, s, ε => by
    by_cases h : s.rel r (Subterm.val! M ![] ε ∘ v)
    · exact ⟨Subformula.rel r v, hrel, h⟩
    · exact ⟨Subformula.nrel r v, hnrel, h⟩
  | _, verum Δ h,            M, s, ε => ⟨⊤, h, by simp⟩
  | _, or Δ p q d,       M, s, ε => by
    have : Subformula.Val! M ε p ∨ Subformula.Val! M ε q ∨ ∃ q ∈ Δ, Subformula.Val! M ε q := by simpa using sound d M ε
    rcases this with (hp | hq | ⟨r, hr, hhr⟩)
    · exact ⟨p ⋎ q, by simp, by simp[hp]⟩
    · exact ⟨p ⋎ q, by simp, by simp[hq]⟩
    · exact ⟨r, by simp[hr], hhr⟩
  | _, and Δ p q dp dq,       M, s, ε => by
    have : Subformula.Val! M ε p ∨ ∃ r ∈ Δ, Subformula.Val! M ε r := by simpa using sound dp M ε
    rcases this with (hp | ⟨r, hr, hhr⟩)
    · have : Subformula.Val! M ε q ∨ ∃ r ∈ Δ, Subformula.Val! M ε r := by simpa using sound dq M ε
      rcases this with (hq | ⟨r, hr, hhr⟩)
      · exact ⟨p ⋏ q, by simp, by simp[hp, hq]⟩
      · exact ⟨r, by simp[hr], hhr⟩
    · exact ⟨r, by simp[hr], hhr⟩
  | _, all Δ p d,             M, s, ε => by
    have : (∀ a : M, Subformula.Eval! M ![a] ε p) ∨ ∃ q ∈ Δ, Subformula.Val! M ε q := by
      simpa[shifts, Subformula.shiftEmb, Matrix.vecConsLast_vecEmpty, forall_or_right]
        using fun a : M => sound d M (a :>ₙ ε)
    rcases this with (hp | ⟨q, hq, hhq⟩)
    · exact ⟨∀' p, by simp, hp⟩
    · exact ⟨q, by simp[hq], hhq⟩
  | _, ex Δ t p d,            M, s, ε => by
    have : Subformula.Eval! M ![t.val! M ![] ε] ε p ∨ ∃ p ∈ Δ, Subformula.Val! M ε p := by
      simpa[Subformula.eval_substs, Matrix.constant_eq_singleton] using sound d M ε
    rcases this with (hp | ⟨q, hq, hhq⟩)
    · exact ⟨∃' p, by simp, t.val! M ![] ε, hp⟩
    · exact ⟨q, by simp[hq], hhq⟩
  | _, cut Δ Γ p _ dΔ dΓ,    M, s, ε => by
    have hΔ : Subformula.Val! M ε p ∨ ∃ q ∈ Δ, Subformula.Val! M ε q := by simpa using dΔ.sound M ε
    have hΓ : ¬Subformula.Val! M ε p ∨ ∃ q ∈ Γ, Subformula.Val! M ε q := by simpa using dΓ.sound M ε
    rcases hΔ with (hΔ | ⟨q, hΔ, hq⟩)
    · rcases hΓ with (hΓ | ⟨q, hΓ, hq⟩)
      · contradiction
      · exact ⟨q, by simp[hΓ], hq⟩
    · exact ⟨q, by simp[hΔ], hq⟩

end DerivationCR

lemma DerivationCRWA.soundness (b : T ⊢ᶜ[P] Γ) {M : Type u} [s : Structure L M] (h : M ⊧* T) (ε : ℕ → M) :
    ∃ p ∈ Γ, Subformula.Val! M ε p := by
  have : ∃ p, (p ∈ Γ ∨ ∃ σ ∈ b.leftHand, Rew.embl σ = p) ∧ Subformula.Val! M ε p := by simpa using b.derivation.sound M ε
  rcases this with ⟨p, (hp | ⟨σ, hσ, rfl⟩), vp⟩
  { exact ⟨p, hp, vp⟩ }
  { have : M ⊧ σ := by simpa using vp
    have : ¬M ⊧ σ := by simpa using h (DerivationCRWA.neg_mem hσ)
    contradiction }

theorem soundness {T} {σ : Sentence L} : T ⊢ σ → T ⊨ σ := fun d M hM s hT => by
  simpa using d.soundness hT

instance : Logic.Sound (Sentence L) := ⟨soundness⟩

end soundness

end FirstOrder

end LO