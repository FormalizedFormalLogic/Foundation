import Foundation.FirstOrder.Basic.Calculus

/-!

# Derivation2

Different characterizations of proof.

-/

namespace LO.FirstOrder

variable {L : Language} [L.DecidableEq]

section derivation2

inductive Derivation2 (𝓢 : SyntacticFormulas L) : Finset (SyntacticFormula L) → Type _
| closed (Δ) (φ : SyntacticFormula L)      : φ ∈ Δ → ∼φ ∈ Δ → Derivation2 𝓢 Δ
| axm  {Δ} (φ : SyntacticFormula L)       : φ ∈ 𝓢 → φ ∈ Δ → Derivation2 𝓢 Δ
| verum {Δ}                                : ⊤ ∈ Δ → Derivation2 𝓢 Δ
| and   {Δ} {φ ψ : SyntacticFormula L}     : φ ⋏ ψ ∈ Δ → Derivation2 𝓢 (insert φ Δ) → Derivation2 𝓢 (insert ψ Δ) → Derivation2 𝓢 Δ
| or    {Δ} {φ ψ : SyntacticFormula L}     : φ ⋎ ψ ∈ Δ → Derivation2 𝓢 (insert φ (insert ψ Δ)) → Derivation2 𝓢 Δ
| all   {Δ} {φ : SyntacticSemiformula L 1} : ∀' φ ∈ Δ → Derivation2 𝓢 (insert (Rewriting.free φ) (Δ.image Rewriting.shift)) → Derivation2 𝓢 Δ
| ex    {Δ} {φ : SyntacticSemiformula L 1} : ∃' φ ∈ Δ → (t : SyntacticTerm L) → Derivation2 𝓢 (insert (φ/[t]) Δ) → Derivation2 𝓢 Δ
| wk    {Δ Γ} : Derivation2 𝓢 Δ → Δ ⊆ Γ → Derivation2 𝓢 Γ
| shift {Δ}   : Derivation2 𝓢 Δ → Derivation2 𝓢 (Δ.image Rewriting.shift)
| cut   {Δ φ} : Derivation2 𝓢 (insert φ Δ) → Derivation2 𝓢 (insert (∼φ) Δ) → Derivation2 𝓢 Δ

scoped infix:45 " ⊢₂ " => Derivation2

abbrev Derivable2 (𝓢 : SyntacticFormulas L) (Γ : Finset (SyntacticFormula L)) := Nonempty (𝓢 ⊢₂ Γ)

scoped infix:45 " ⊢₂! " => Derivable2

abbrev Derivable2SingleConseq (𝓢 : SyntacticFormulas L) (φ : SyntacticFormula L) : Prop := 𝓢 ⊢₂! {φ}

scoped infix: 45 " ⊢₂.! " => Derivable2SingleConseq

variable {𝓢 : SyntacticFormulas L}

lemma shifts_toFinset_eq_image_shift (Δ : Sequent L) :
    (Rewriting.shifts Δ).toFinset = Δ.toFinset.image Rewriting.shift := by ext φ; simp [Rewriting.shifts]

def Derivation.toDerivation2 (𝓢) {Γ : Sequent L} : 𝓢 ⟹ Γ → 𝓢 ⊢₂ Γ.toFinset
  | Derivation.axL Δ R v            => Derivation2.closed _ (Semiformula.rel R v) (by simp) (by simp)
  | Derivation.axm (φ := φ) h      => Derivation2.axm φ h (by simp)
  | Derivation.verum Δ              => Derivation2.verum (by simp)
  | @Derivation.and _ _ Δ φ ψ dp dq =>
    Derivation2.and (φ := φ) (ψ := ψ) (by simp)
      (Derivation2.wk (Derivation.toDerivation2 𝓢 dp) (by simpa using Finset.insert_subset_insert _ (by simp)))
      (Derivation2.wk (Derivation.toDerivation2 𝓢 dq) (by simpa using Finset.insert_subset_insert _ (by simp)))
  | @Derivation.or _ _ Δ φ ψ dpq    =>
    Derivation2.or (φ := φ) (ψ := ψ) (by simp)
      (Derivation2.wk (Derivation.toDerivation2 𝓢 dpq)
      (by simpa using Finset.insert_subset_insert _ <| Finset.insert_subset_insert _ (by simp)))
  | @Derivation.all _ _ Δ φ dp      =>
    Derivation2.all (φ := φ) (by simp)
      (Derivation2.wk (Derivation.toDerivation2 𝓢 dp)
        (by simpa using Finset.insert_subset_insert _ (by simp [shifts_toFinset_eq_image_shift])))
  | @Derivation.ex _ _ Δ φ t dp     =>
    Derivation2.ex (φ := φ) (by simp) t
      (Derivation2.wk (Derivation.toDerivation2 𝓢 dp) (by simpa using Finset.insert_subset_insert _ (by simp)))
  | Derivation.wk d h               =>
    Derivation2.wk (Derivation.toDerivation2 𝓢 d) (List.toFinset_mono h)
  | @Derivation.cut _ _ Δ φ d₁ d₂   =>
    Derivation2.cut (φ := φ)
      (Derivation2.wk (Derivation.toDerivation2 𝓢 d₁) (by simp))
      (Derivation2.wk (Derivation.toDerivation2 𝓢 d₂) (by simp))

noncomputable def Derivation2.toDerivation {Γ : Finset (SyntacticFormula L)} : 𝓢 ⊢₂ Γ → 𝓢 ⟹ Γ.toList
  | Derivation2.closed Δ φ hp hn              => Derivation.em (φ := φ) (by simp [hp]) (by simp [hn])
  | Derivation2.axm φ hp h                   => Tait.wk (Derivation.axm hp) (by simp_all)
  | Derivation2.verum h                       => Tait.verum' (by simp [h])
  | Derivation2.and (φ := φ) (ψ := ψ) h dp dq =>
    Tait.and' (φ := φ) (ψ := ψ) (by simp [h])
      (Tait.wk dp.toDerivation <| by intro x; simp)
      (Tait.wk dq.toDerivation <| by intro x; simp)
  | Derivation2.or (φ := φ) (ψ := ψ) h dpq    =>
    Tait.or' (φ := φ) (ψ := ψ) (by simp [h]) (Tait.wk dpq.toDerivation <| by intro x; simp)
  | Derivation2.all (φ := φ) h d              =>
    Derivation.all' (φ := φ) (by simp [h]) (Tait.wk d.toDerivation <| by intro x; simp [Rewriting.shifts])
  | Derivation2.ex (φ := φ) h t d             =>
    Derivation.ex' (φ := φ) (by simp [h]) t (Tait.wk d.toDerivation <| by intro x; simp)
  | Derivation2.wk d h                        =>
    Tait.wk d.toDerivation (by intro x; simpa using @h x)
  | Derivation2.shift d                       =>
    Tait.wk (Derivation.shift d.toDerivation) <| by intro x; simp [Rewriting.shifts]
  | Derivation2.cut (φ := φ) d dn             =>
    Tait.cut (φ := φ)
      (Tait.wk d.toDerivation <| by intro x; simp)
      (Tait.wk dn.toDerivation <| by intro x; simp)

lemma derivable_iff_derivable2 {Γ : List (SyntacticFormula L)} : 𝓢 ⟹! Γ ↔ 𝓢 ⊢₂! Γ.toFinset := by
  constructor
  · rintro ⟨d⟩; exact ⟨by simpa using Derivation.toDerivation2 𝓢 d⟩
  · rintro ⟨d⟩; exact ⟨.wk d.toDerivation (by intro x; simp)⟩

def provable_iff_derivable2 {φ} : 𝓢 ⊢! φ ↔ 𝓢 ⊢₂.! φ := derivable_iff_derivable2

end derivation2

end LO.FirstOrder
