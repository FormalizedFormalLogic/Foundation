import Foundation.IntFO.Basic.Rew

namespace LO.FirstOrder

abbrev Sequentᵢ (L : Language) := List (SyntacticFormulaᵢ L)

open Semiformulaᵢ

variable {L : Language} {T : Theory L}

def shiftsᵢ (Δ : List (SyntacticSemiformulaᵢ L n)) :
  List (SyntacticSemiformulaᵢ L n) := Δ.map Rew.shift.homᵢ

scoped postfix:max "⁺" => shiftsᵢ

@[simp] lemma mem_shiftsᵢ_iff {φ : SyntacticSemiformulaᵢ L n} {Δ : List (SyntacticSemiformulaᵢ L n)} :
    Rew.shift.homᵢ φ ∈ Δ⁺ ↔ φ ∈ Δ :=
  List.mem_map_of_injective Rew.shift.homᵢ_injective

@[simp] lemma shiftsᵢ_ss (Δ Γ : List (SyntacticSemiformulaᵢ L n)) :
    Δ⁺ ⊆ Γ⁺ ↔ Δ ⊆ Γ := List.map_subset_iff _ Rew.shift.homᵢ_injective

@[simp] lemma shiftsᵢ_cons (φ : SyntacticSemiformulaᵢ L n) (Δ : List (SyntacticSemiformulaᵢ L n)) :
    (φ :: Δ)⁺ = Rew.shift.homᵢ φ :: Δ⁺ := by simp [shiftsᵢ]

@[simp] lemma shiftsᵢ_nil : ([] : Sequentᵢ L)⁺ = [] := by rfl

lemma shiftsᵢ_union (Δ Γ : List (SyntacticSemiformulaᵢ L n)) :
    (Δ ++ Γ)⁺ = Δ⁺ ++ Γ⁺ := by simp [shiftsᵢ]

@[simp] lemma shiftsᵢ_emb (Γ : List (Semisentenceᵢ L n)) :
    (Γ.map Rew.emb.homᵢ)⁺ = Γ.map Rew.emb.homᵢ := by
  simp [shiftsᵢ, Function.comp_def, ←Rew.homᵢ_comp_app]

inductive LJ (T : Theoryᵢ L) : Sequentᵢ L → Option (SyntacticFormulaᵢ L) → Type _
| axiom {φ}     : φ ∈ T → LJ T [] (some φ)
| verum (Γ) : LJ T Γ (some ⊤)
| falsum (Γ Δ) : LJ T (⊥ :: Γ) Δ
| andLeft₁ : LJ T (φ :: Γ) Δ → LJ T (φ ⋏ ψ :: Γ) Δ
| andLeft₂ : LJ T (ψ :: Γ) Δ → LJ T (φ ⋏ ψ :: Γ) Δ
| andRight : LJ T Γ (some φ) → LJ T Γ (some ψ) → LJ T Γ (some (φ ⋏ ψ))
| orLeft : LJ T (φ :: Γ) Δ → LJ T (ψ :: Γ) Δ → LJ T (φ ⋎ ψ :: Γ) Δ
| cut : LJ T Γ (some φ) → LJ T (φ :: Γ) Δ → LJ T Γ Δ

notation Γ:45 " ⊢ᵢ[" T "] " φ:46 => LJ T Γ φ

abbrev LJ₀ (Γ : Sequentᵢ L) (φ : SyntacticFormulaᵢ L) : Type _ := Γ ⊢ᵢ[∅] φ

infix:45 " ⊢ᵢ " => LJ₀

end LO.FirstOrder
