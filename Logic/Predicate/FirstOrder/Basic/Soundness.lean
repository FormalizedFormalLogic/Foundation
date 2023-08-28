import Logic.Predicate.FirstOrder.Basic.Semantics
import Logic.Predicate.FirstOrder.Basic.Calculus

namespace LO

namespace FirstOrder

section soundness

variable {L : Language.{u}} [∀ k, DecidableEq (L.func k)] [∀ k, DecidableEq (L.rel k)]

variable {P : SyntacticFormula L → Prop}

namespace DerivationCutRestricted

lemma sound : ∀ {Γ : Sequent L}, ⊢ᶜ[P] Γ → ∀ (M : Type u) [s : Structure L M] (ε : ℕ → M), ∃ p ∈ Γ, SubFormula.Val! M ε p
  | _, axL Δ r v hrel hnrel, M, s, ε => by
    by_cases h : s.rel r (SubTerm.val! M ![] ε ∘ v)
    · exact ⟨SubFormula.rel r v, hrel, h⟩
    · exact ⟨SubFormula.nrel r v, hnrel, h⟩
  | _, verum Δ h,            M, s, ε => ⟨⊤, h, by simp⟩
  | _, or Δ p q d,       M, s, ε => by
    have : SubFormula.Val! M ε p ∨ SubFormula.Val! M ε q ∨ ∃ q ∈ Δ, SubFormula.Val! M ε q := by simpa using sound d M ε
    rcases this with (hp | hq | ⟨r, hr, hhr⟩)
    · exact ⟨p ⋎ q, by simp, by simp[hp]⟩
    · exact ⟨p ⋎ q, by simp, by simp[hq]⟩
    · exact ⟨r, by simp[hr], hhr⟩
  | _, and Δ p q dp dq,       M, s, ε => by
    have : SubFormula.Val! M ε p ∨ ∃ r ∈ Δ, SubFormula.Val! M ε r := by simpa using sound dp M ε
    rcases this with (hp | ⟨r, hr, hhr⟩)
    · have : SubFormula.Val! M ε q ∨ ∃ r ∈ Δ, SubFormula.Val! M ε r := by simpa using sound dq M ε
      rcases this with (hq | ⟨r, hr, hhr⟩)
      · exact ⟨p ⋏ q, by simp, by simp[hp, hq]⟩
      · exact ⟨r, by simp[hr], hhr⟩
    · exact ⟨r, by simp[hr], hhr⟩
  | _, all Δ p d,             M, s, ε => by
    have : (∀ a : M, SubFormula.Eval! M ![a] ε p) ∨ ∃ q ∈ Δ, SubFormula.Val! M ε q := by
      simpa[shifts, SubFormula.shiftEmb, Matrix.vecConsLast_vecEmpty, forall_or_right]
        using fun a : M => sound d M (a :>ₙ ε)
    rcases this with (hp | ⟨q, hq, hhq⟩)
    · exact ⟨∀' p, by simp, hp⟩
    · exact ⟨q, by simp[hq], hhq⟩
  | _, ex Δ t p d,            M, s, ε => by
    have : SubFormula.Eval! M ![t.val! M ![] ε] ε p ∨ ∃ p ∈ Δ, SubFormula.Val! M ε p := by
      simpa[SubFormula.eval_substs, Matrix.constant_eq_singleton] using sound d M ε
    rcases this with (hp | ⟨q, hq, hhq⟩)
    · exact ⟨∃' p, by simp, t.val! M ![] ε, hp⟩
    · exact ⟨q, by simp[hq], hhq⟩
  | _, cut Δ Γ p _ dΔ dΓ,    M, s, ε => by
    have hΔ : SubFormula.Val! M ε p ∨ ∃ q ∈ Δ, SubFormula.Val! M ε q := by simpa using dΔ.sound M ε
    have hΓ : ¬SubFormula.Val! M ε p ∨ ∃ q ∈ Γ, SubFormula.Val! M ε q := by simpa using dΓ.sound M ε
    rcases hΔ with (hΔ | ⟨q, hΔ, hq⟩)
    · rcases hΓ with (hΓ | ⟨q, hΓ, hq⟩)
      · contradiction
      · exact ⟨q, by simp[hΓ], hq⟩
    · exact ⟨q, by simp[hΔ], hq⟩

end DerivationCutRestricted

theorem soundness {T} {σ : Sentence L} : T ⊢ σ → T ⊨ σ := by
  simp[consequence_iff]; rintro b M _ _ hT
  have : M ⊧ σ ∨ ∃ τ ∈ SentenceCalculus.leftHand b, M ⊧ τ := by simpa using (SentenceCalculus.derivation b).sound M default
  rcases this with (hσ | ⟨τ, hτ, hhτ⟩)
  · assumption
  · have : ~τ ∈ T := by rcases (SentenceCalculus.hleftHand b) hτ with ⟨τ', hτ', rfl⟩; simpa[←SubFormula.neg_eq] using hτ'
    have : ¬ M ⊧ τ := by simpa using hT this
    contradiction

instance : Logic.Sound (Sentence L) := ⟨soundness⟩

end soundness

end FirstOrder

end LO