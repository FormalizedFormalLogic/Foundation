import Foundation.FirstOrder.Basic.Calculus

/-!

# Derivation2

Different characterizations of proof.

-/

namespace LO.FirstOrder

variable {L : Language} [(k : ℕ) → DecidableEq (L.Func k)] [(k : ℕ) → DecidableEq (L.Rel k)]

section derivation2

inductive Derivation2 (T : Theory L) : Finset (SyntacticFormula L) → Type _
| closed (Δ) (φ : SyntacticFormula L)      : φ ∈ Δ → ∼φ ∈ Δ → Derivation2 T Δ
| root  {Δ} (φ : SyntacticFormula L)       : φ ∈ T → φ ∈ Δ → Derivation2 T Δ
| verum {Δ}                                : ⊤ ∈ Δ → Derivation2 T Δ
| and   {Δ} {φ ψ : SyntacticFormula L}     : φ ⋏ ψ ∈ Δ → Derivation2 T (insert φ Δ) → Derivation2 T (insert ψ Δ) → Derivation2 T Δ
| or    {Δ} {φ ψ : SyntacticFormula L}     : φ ⋎ ψ ∈ Δ → Derivation2 T (insert φ (insert ψ Δ)) → Derivation2 T Δ
| all   {Δ} {φ : SyntacticSemiformula L 1} : ∀' φ ∈ Δ → Derivation2 T (insert (Rewriting.free φ) (Δ.image Rewriting.shift)) → Derivation2 T Δ
| ex    {Δ} {φ : SyntacticSemiformula L 1} : ∃' φ ∈ Δ → (t : SyntacticTerm L) → Derivation2 T (insert (φ/[t]) Δ) → Derivation2 T Δ
| wk    {Δ Γ} : Derivation2 T Δ → Δ ⊆ Γ → Derivation2 T Γ
| shift {Δ}   : Derivation2 T Δ → Derivation2 T (Δ.image Rewriting.shift)
| cut   {Δ φ} : Derivation2 T (insert φ Δ) → Derivation2 T (insert (∼φ) Δ) → Derivation2 T Δ

scoped infix:45 " ⊢₂ " => Derivation2

abbrev Derivable2 (T : Theory L) (Γ : Finset (SyntacticFormula L)) := Nonempty (T ⊢₂ Γ)

scoped infix:45 " ⊢₂! " => Derivable2

abbrev Derivable2SingleConseq (T : Theory L) (φ : SyntacticFormula L) : Prop := T ⊢₂! {φ}

scoped infix: 45 " ⊢₂.! " => Derivable2SingleConseq

variable {T : Theory L}

lemma shifts_toFinset_eq_image_shift (Δ : Sequent L) :
    (shifts Δ).toFinset = Δ.toFinset.image Rewriting.shift := by ext φ; simp [shifts]

def Derivation.toDerivation2 T : {Γ : Sequent L} → T ⟹ Γ → T ⊢₂ Γ.toFinset
  | _, Derivation.axL Δ R v            => Derivation2.closed _ (Semiformula.rel R v) (by simp) (by simp)
  | _, Derivation.root (φ := φ) h      => Derivation2.root φ h (by simp)
  | _, Derivation.verum Δ              => Derivation2.verum (by simp)
  | _, @Derivation.and _ _ Δ φ ψ dp dq =>
    Derivation2.and (φ := φ) (ψ := ψ) (by simp)
      (Derivation2.wk (Derivation.toDerivation2 T dp) (by simpa using Finset.insert_subset_insert _ (by simp)))
      (Derivation2.wk (Derivation.toDerivation2 T dq) (by simpa using Finset.insert_subset_insert _ (by simp)))
  | _, @Derivation.or _ _ Δ φ ψ dpq    =>
    Derivation2.or (φ := φ) (ψ := ψ) (by simp)
      (Derivation2.wk (Derivation.toDerivation2 T dpq)
      (by simpa using Finset.insert_subset_insert _ <| Finset.insert_subset_insert _ (by simp)))
  | _, @Derivation.all _ _ Δ φ dp      =>
    Derivation2.all (φ := φ) (by simp)
      (Derivation2.wk (Derivation.toDerivation2 T dp)
        (by simpa using Finset.insert_subset_insert _ (by simp [shifts_toFinset_eq_image_shift])))
  | _, @Derivation.ex _ _ Δ φ t dp     =>
    Derivation2.ex (φ := φ) (by simp) t
      (Derivation2.wk (Derivation.toDerivation2 T dp) (by simpa using Finset.insert_subset_insert _ (by simp)))
  | _, Derivation.wk d h               =>
    Derivation2.wk (Derivation.toDerivation2 T d) (List.toFinset_mono h)
  | _, @Derivation.cut _ _ Δ φ d₁ d₂   =>
    Derivation2.cut (φ := φ)
      (Derivation2.wk (Derivation.toDerivation2 T d₁) (by simp))
      (Derivation2.wk (Derivation.toDerivation2 T d₂) (by simp))

noncomputable def Derivation2.toDerivation : {Γ : Finset (SyntacticFormula L)} → T ⊢₂ Γ → T ⟹ Γ.toList
  | _, Derivation2.closed Δ φ hp hn              => Derivation.em (φ := φ) (by simp [hp]) (by simp [hn])
  | _, Derivation2.root φ hp h                   => Tait.wk (Derivation.root hp) (by simp_all)
  | _, Derivation2.verum h                       => Tait.verum' (by simp [h])
  | _, Derivation2.and (φ := φ) (ψ := ψ) h dp dq =>
    Tait.and' (φ := φ) (ψ := ψ) (by simp [h])
      (Tait.wk dp.toDerivation <| by intro x; simp)
      (Tait.wk dq.toDerivation <| by intro x; simp)
  | _, Derivation2.or (φ := φ) (ψ := ψ) h dpq    =>
    Tait.or' (φ := φ) (ψ := ψ) (by simp [h]) (Tait.wk dpq.toDerivation <| by intro x; simp)
  | _, Derivation2.all (φ := φ) h d              =>
    Derivation.all' (φ := φ) (by simp [h]) (Tait.wk d.toDerivation <| by intro x; simp [shifts])
  | _, Derivation2.ex (φ := φ) h t d             =>
    Derivation.ex' (φ := φ) (by simp [h]) t (Tait.wk d.toDerivation <| by intro x; simp [shifts])
  | _, Derivation2.wk d h                        =>
    Tait.wk d.toDerivation (by intro x; simp; exact @h x)
  | _, Derivation2.shift d                       =>
    Tait.wk (Derivation.shift d.toDerivation) <| by intro x; simp [shifts]
  | _, Derivation2.cut (φ := φ) d dn             =>
    Tait.cut (φ := φ)
      (Tait.wk d.toDerivation <| by intro x; simp)
      (Tait.wk dn.toDerivation <| by intro x; simp)

lemma derivable_iff_derivable2 {Γ : List (SyntacticFormula L)} : T ⟹! Γ ↔ T ⊢₂! Γ.toFinset := by
  constructor
  · rintro ⟨d⟩; exact ⟨by simpa using Derivation.toDerivation2 T d⟩
  · rintro ⟨d⟩; exact ⟨.wk d.toDerivation (by intro x; simp)⟩

def provable_iff_derivable2 {φ} : T ⊢! φ ↔ T ⊢₂.! φ := derivable_iff_derivable2

end derivation2

end LO.FirstOrder
