import Logic.FirstOrder.Basic.Calculus

namespace LO.FirstOrder

variable {L : Language} [(k : ℕ) → DecidableEq (L.Func k)] [(k : ℕ) → DecidableEq (L.Rel k)]

inductive Derivation2 : Finset (SyntacticFormula L) → Type _
| axL   {Δ} (p : SyntacticFormula L)       : p ∈ Δ → ~p ∈ Δ → Derivation2 Δ
| verum {Δ}                                : ⊤ ∈ Δ → Derivation2 Δ
| and   {Δ} {p q : SyntacticFormula L}     : p ⋏ q ∈ Δ → Derivation2 (insert p Δ) → Derivation2 (insert q Δ) → Derivation2 Δ
| or    {Δ} {p q : SyntacticFormula L}     : p ⋎ q ∈ Δ → Derivation2 (insert p (insert q Δ)) → Derivation2 Δ
| all   {Δ} {p : SyntacticSemiformula L 1} : ∀' p ∈ Δ → Derivation2 (insert (Rew.free.hom p) (Δ.image Rew.shift.hom)) → Derivation2 Δ
| ex    {Δ} {p : SyntacticSemiformula L 1} : ∃' p ∈ Δ → (t : SyntacticTerm L) → Derivation2 (insert (p/[t]) Δ) → Derivation2 Δ
| wk    {Δ Γ} : Derivation2 Δ → Δ ⊆ Γ → Derivation2 Γ
| shift {Δ}   : Derivation2 Δ → Derivation2 (Δ.image Rew.shift.hom)
| cut   {Δ p} : Derivation2 (insert p Δ) → Derivation2 (insert (~p) Δ) → Derivation2 Δ

prefix: 45 "⊢¹ᶠ " => Derivation2

lemma shifts_toFinset_eq_image_shift (Δ : Sequent L) :
    (shifts Δ).toFinset = Δ.toFinset.image Rew.shift.hom := by ext p; simp [shifts]

def Derivation.toDerivation2 : {Γ : Sequent L} → ⊢¹ Γ → ⊢¹ᶠ Γ.toFinset
  | _, Derivation.axL Δ r v          => Derivation2.axL (Semiformula.rel r v) (by simp) (by simp)
  | _, Derivation.verum Δ            => Derivation2.verum (by simp)
  | _, @Derivation.and _ Δ p q dp dq =>
    Derivation2.and (p := p) (q := q) (by simp)
      (Derivation2.wk (Derivation.toDerivation2 dp) (by simpa using Finset.insert_subset_insert _ (by simp)))
      (Derivation2.wk (Derivation.toDerivation2 dq) (by simpa using Finset.insert_subset_insert _ (by simp)))
  | _, @Derivation.or _ Δ p q dpq    =>
    Derivation2.or (p := p) (q := q) (by simp)
      (Derivation2.wk (Derivation.toDerivation2 dpq)
      (by simpa using Finset.insert_subset_insert _ <| Finset.insert_subset_insert _ (by simp)))
  | _, @Derivation.all _ Δ p dp      =>
    Derivation2.all (p := p) (by simp)
      (Derivation2.wk (Derivation.toDerivation2 dp)
        (by simpa using Finset.insert_subset_insert _ (by simp [shifts_toFinset_eq_image_shift])))
  | _, @Derivation.ex _ Δ p t dp     =>
    Derivation2.ex (p := p) (by simp) t
      (Derivation2.wk (Derivation.toDerivation2 dp) (by simpa using Finset.insert_subset_insert _ (by simp)))
  | _, Derivation.wk d h             =>
    Derivation2.wk (Derivation.toDerivation2 d) (List.toFinset_mono h)
  | _, @Derivation.cut _ Δ p d₁ d₂   =>
    Derivation2.cut (p := p)
      (Derivation2.wk (Derivation.toDerivation2 d₁) (by simp))
      (Derivation2.wk (Derivation.toDerivation2 d₂) (by simp))

noncomputable def Derivation2.toDerivation : {Γ : Finset (SyntacticFormula L)} → ⊢¹ᶠ Γ → ⊢¹ Γ.toList
  | _, Derivation2.axL p hp hn => Derivation.em (p := p) (by simp [hp]) (by simp [hn])
  | _, Derivation2.verum h => Derivation.verum' (by simp [h])
  | _, Derivation2.and (p := p) (q := q) h dp dq =>
    Tait.and' (p := p) (q := q) (by simp [h])
      (Tait.wk dp.toDerivation <| by intro x; simp)
      (Tait.wk dq.toDerivation <| by intro x; simp)
  | _, Derivation2.or (p := p) (q := q) h dpq =>
    Tait.or' (p := p) (q := q) (by simp [h]) (Tait.wk dpq.toDerivation <| by intro x; simp)
  | _, Derivation2.all (p := p) h d =>
    Derivation.all' (p := p) (by simp [h]) (Tait.wk d.toDerivation <| by intro x; simp [shifts])
  | _, Derivation2.ex (p := p) h t d =>
    Derivation.ex' (p := p) (by simp [h]) t (Tait.wk d.toDerivation <| by intro x; simp [shifts])
  | _, Derivation2.wk d h =>
    Tait.wk d.toDerivation (by intro x; simp; exact @h x)
  | _, Derivation2.shift d => Derivation.wk (Derivation.shift d.toDerivation) <| by intro x; simp [shifts]
  | _, Derivation2.cut (p := p) d dn =>
    Derivation.cut (p := p) (Tait.wk d.toDerivation <| by intro x; simp) (Tait.wk dn.toDerivation <| by intro x; simp)

lemma Derivation2.nonempty_iff {Γ : List (SyntacticFormula L)} : ⊢¹! Γ ↔ Nonempty (⊢¹ᶠ Γ.toFinset) := by
  constructor
  · rintro ⟨d⟩; exact ⟨by simpa using Derivation.toDerivation2 d⟩
  · rintro ⟨d⟩; exact ⟨Tait.wk d.toDerivation (by intro x; simp)⟩

variable {T : Theory L}

lemma syntactic_provable_iff_derivation2 {T : SyntacticTheory L} {σ} :
    T ⊢! σ ↔ ∃ Γ : Finset (SyntacticFormula L), (∀ π ∈ Γ, ~π ∈ T) ∧ Nonempty (⊢¹ᶠ insert σ Γ) := by
  simp [Gentzen.provable_iff, Tait.derivable_iff, Derivation2.nonempty_iff]
  constructor
  · rintro ⟨Δ, hΔ, ⟨d⟩⟩
    exact ⟨(Δ.map (~·)).toFinset, by simpa using hΔ, ⟨Derivation2.wk d <| by intro x; simp; tauto⟩⟩
  · rintro ⟨Γ, hΓ, ⟨d⟩⟩
    exact ⟨Γ.toList.map (~·), by simpa, ⟨Derivation2.wk d <| by intro x; simp [Function.comp]; tauto⟩⟩

lemma provable_iff_derivation2 {σ} :
    T ⊢! σ ↔ ∃ Γ : Finset (SyntacticFormula L),
      (∀ π ∈ Γ, ∃ π₀ ∈ T, Rew.emb.hom π₀ = ~ π) ∧ Nonempty (⊢¹ᶠ insert (Rew.emb.hom σ) Γ) := by
  simp [provable_iff, syntactic_provable_iff_derivation2]

end LO.FirstOrder
