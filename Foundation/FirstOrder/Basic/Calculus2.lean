module
public import Foundation.FirstOrder.Basic.Calculus
@[expose] public section

/-! # Alternative definition of proof -/

namespace LO.FirstOrder

variable {L : Language} [L.DecidableEq]

section derivation2

inductive Derivation2 (𝓢 : Schema L) : Finset (Proposition L) → Type _
| closed (Γ) (φ : Proposition L) : φ ∈ Γ → ∼φ ∈ Γ → Derivation2 𝓢 Γ
| axm {Γ} (φ : Proposition L) : φ ∈ 𝓢 → φ ∈ Γ → Derivation2 𝓢 Γ
| verum {Γ} : ⊤ ∈ Γ → Derivation2 𝓢 Γ
| and {Γ} {φ ψ : Proposition L} : φ ⋏ ψ ∈ Γ → Derivation2 𝓢 (insert φ Γ) → Derivation2 𝓢 (insert ψ Γ) → Derivation2 𝓢 Γ
| or {Γ} {φ ψ : Proposition L} : φ ⋎ ψ ∈ Γ → Derivation2 𝓢 (insert φ (insert ψ Γ)) → Derivation2 𝓢 Γ
| all {Γ} {φ : Semiproposition L 1} : ∀⁰ φ ∈ Γ → Derivation2 𝓢 (insert (Rewriting.free φ) (Γ.image Rewriting.shift)) → Derivation2 𝓢 Γ
| exs {Γ} {φ : Semiproposition L 1} : ∃⁰ φ ∈ Γ → (t : SyntacticTerm L) → Derivation2 𝓢 (insert (φ/[t]) Γ) → Derivation2 𝓢 Γ
| wk {Δ Γ} : Derivation2 𝓢 Δ → Δ ⊆ Γ → Derivation2 𝓢 Γ
| shift {Γ}   : Derivation2 𝓢 Γ → Derivation2 𝓢 (Γ.image Rewriting.shift)
| cut {Γ φ} : Derivation2 𝓢 (insert φ Γ) → Derivation2 𝓢 (insert (∼φ) Γ) → Derivation2 𝓢 Γ

scoped infix:45 " ⟹₂" => Derivation2

abbrev Derivable2 (𝓢 : Schema L) (Γ : Finset (Proposition L)) := Nonempty (𝓢 ⟹₂ Γ)

scoped infix:45 " ⟹₂! " => Derivable2

abbrev Derivable2SingleConseq (𝓢 : Schema L) (φ : Proposition L) : Prop := 𝓢 ⟹₂! {φ}

scoped infix: 45 " ⊢!₂! " => Derivable2SingleConseq

variable {𝓢 : Schema L}

lemma shifts_toFinset_eq_image_shift (Γ : Sequent L) :
    (Rewriting.shifts Γ).toFinset = Γ.toFinset.image Rewriting.shift := by ext φ; simp [Rewriting.shifts]

def Derivation.toDerivation2 (𝓢) {Γ : Sequent L} : 𝓢 ⟹ Γ → 𝓢 ⟹₂ Γ.toFinset
  | Derivation.axL R v => Derivation2.closed _ (Semiformula.rel R v) (by simp) (by simp)
  | Derivation.axm (φ := φ) h => Derivation2.axm φ h (by simp)
  | Derivation.verum => Derivation2.verum (by simp)
  | Derivation.and (Γ := Γ) (φ := φ) (ψ := ψ) dp dq =>
    Derivation2.and (φ := φ) (ψ := ψ) (by simp)
      (Derivation2.wk (Derivation.toDerivation2 𝓢 dp) (by simp))
      (Derivation2.wk (Derivation.toDerivation2 𝓢 dq) (by simp))
  | Derivation.or (Γ := Γ) (φ := φ) (ψ := ψ) dpq =>
    Derivation2.or (φ := φ) (ψ := ψ) (by simp)
      (Derivation2.wk (Derivation.toDerivation2 𝓢 dpq)
      (by simp))
  | Derivation.all (Γ := Γ) (φ := φ) dp =>
    Derivation2.all (φ := φ) (by simp)
      (Derivation2.wk (Derivation.toDerivation2 𝓢 dp)
        (by simpa using Finset.insert_subset_insert _ (by simp [shifts_toFinset_eq_image_shift])))
  | Derivation.exs (Γ := Γ) (φ := φ) t dp =>
    Derivation2.exs (φ := φ) (by simp) t
      (Derivation2.wk (Derivation.toDerivation2 𝓢 dp) (by simp))
  | Derivation.wk d h =>
    Derivation2.wk (Derivation.toDerivation2 𝓢 d) (List.toFinset_mono h)
  | Derivation.cut (Γ := Γ) (φ := φ) d₁ d₂ =>
    Derivation2.cut (φ := φ)
      (Derivation2.wk (Derivation.toDerivation2 𝓢 d₁) (by simp))
      (Derivation2.wk (Derivation.toDerivation2 𝓢 d₂) (by simp))

noncomputable def Derivation2.toDerivation {Γ : Finset (Proposition L)} : 𝓢 ⟹₂ Γ → 𝓢 ⟹ Γ.toList
  | Derivation2.closed Γ φ hp hn              => Derivation.em (φ := φ) (by simp [hp]) (by simp [hn])
  | Derivation2.axm φ hp h                    => Tait.wk (Derivation.axm hp) (by simp_all)
  | Derivation2.verum h                       => Tait.verum' (by simp [h])
  | Derivation2.and (φ := φ) (ψ := ψ) h dp dq =>
    Tait.and' (φ := φ) (ψ := ψ) (by simp [h])
      (Tait.wk dp.toDerivation <| by intro x; simp)
      (Tait.wk dq.toDerivation <| by intro x; simp)
  | Derivation2.or (φ := φ) (ψ := ψ) h dpq    =>
    Tait.or' (φ := φ) (ψ := ψ) (by simp [h]) (Tait.wk dpq.toDerivation <| by intro x; simp)
  | Derivation2.all (φ := φ) h d              =>
    Derivation.all' (φ := φ) (by simp [h]) (Tait.wk d.toDerivation <| by intro x; simp [Rewriting.shifts])
  | Derivation2.exs (φ := φ) h t d             =>
    Derivation.exs' (φ := φ) (by simp [h]) t (Tait.wk d.toDerivation <| by intro x; simp)
  | Derivation2.wk d h                        =>
    Tait.wk d.toDerivation (by intro x; simpa using @h x)
  | Derivation2.shift d                       =>
    Tait.wk (Derivation.shift d.toDerivation) <| by intro x; simp [Rewriting.shifts]
  | Derivation2.cut (φ := φ) d dn             =>
    Tait.cut (φ := φ)
      (Tait.wk d.toDerivation <| by intro x; simp)
      (Tait.wk dn.toDerivation <| by intro x; simp)

lemma derivable_iff_derivable2 {Γ : List (Proposition L)} : 𝓢 ⟹! Γ ↔ 𝓢 ⟹₂! Γ.toFinset := by
  constructor
  · rintro ⟨d⟩; exact ⟨by simpa using Derivation.toDerivation2 𝓢 d⟩
  · rintro ⟨d⟩; exact ⟨.wk d.toDerivation (by intro x; simp)⟩

def provable_iff_derivable2 {φ} : 𝓢 ⊢ φ ↔ 𝓢 ⊢!₂! φ := derivable_iff_derivable2

end derivation2

end LO.FirstOrder
