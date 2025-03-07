import Foundation.Arithmetization.Vorspiel.Vorspiel

namespace Function

variable {σ α β : Sort*}

def Graphᵥ (f : (Fin k → α) → α) : (Fin (k + 1) → α) → Prop := fun v ↦ v 0 = f (v ·.succ)

def Graph (f : α → σ) : σ → α → Prop := fun y x ↦ y = f x

def Graph₂ (f : α → β → σ) : σ → α → β → Prop := fun y x₁ x₂ ↦ y = f x₁ x₂

def Graph₃ (f : α → β → γ → σ) : σ → α → β → γ → Prop := fun y x₁ x₂ x₃ ↦ y = f x₁ x₂ x₃

def Graph₄ (f : α → β → γ → δ → σ) : σ → α → β → γ → δ → Prop := fun y x₁ x₂ x₃ x₄ ↦ y = f x₁ x₂ x₃ x₄

def Graph₅ (f : α → β → γ → δ → ε → σ) : σ → α → β → γ → δ → ε → Prop := fun y x₁ x₂ x₃ x₄ x₅ ↦ y = f x₁ x₂ x₃ x₄ x₅

lemma Graph.eq {f : α → σ} {y x} (h : Graph f y x) : f x = y := h.symm

lemma Graph.iff_left (f : α → σ) {y x} : f x = y ↔ Graph f y x := by simp [Graph, eq_comm]

lemma Graph.iff_right (f : α → σ) {y x} : y = f x ↔ Graph f y x := by simp [Graph]

lemma Graph₂.eq {f : α → β → σ} {y x₁ x₂} (h : Graph₂ f y x₁ x₂) : f x₁ x₂ = y := h.symm

lemma Graph₂.iff_left (f : α → β → σ) {y x₁ x₂} : f x₁ x₂ = y ↔ Graph₂ f y x₁ x₂ := by simp [Graph₂, eq_comm]

lemma Graph₂.iff_right (f : α → β → σ) {y x₁ x₂} : y = f x₁ x₂ ↔ Graph₂ f y x₁ x₂ := by simp [Graph₂]

lemma Graph₃.eq {f : α → β → γ → σ} {y x₁ x₂ x₃} (h : Graph₃ f y x₁ x₂ x₃) : f x₁ x₂ x₃ = y := h.symm

lemma Graph₃.iff_left (f : α → β → γ → σ) {y x₁ x₂ x₃} : f x₁ x₂ x₃ = y ↔ Graph₃ f y x₁ x₂ x₃ := by simp [Graph₃, eq_comm]

lemma Graph₃.iff_right (f : α → β → γ → σ) {y x₁ x₂ x₃} : y = f x₁ x₂ x₃ ↔ Graph₃ f y x₁ x₂ x₃ := by simp [Graph₃]

end Function
