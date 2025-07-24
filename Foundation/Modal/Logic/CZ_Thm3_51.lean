import Foundation.Modal.Logic.Extension
import Foundation.Modal.Entailment.K
import Foundation.Meta.ClProver

section

variable {α β} {l : List α}

lemma List.exists_of_range (h : a ∈ List.map f (List.range n)) : ∃ i < n, a = f i := by
  obtain ⟨i, ⟨hi, rfl⟩⟩ := List.exists_of_mem_map h;
  use i;
  constructor;
  . simpa using hi;
  . simp;

end



namespace LO.Modal

open LO.Entailment LO.Modal.Entailment

variable {α} [DecidableEq α] {L : Logic α} [Entailment.K L] {Γ : Set (Formula α)} {φ ψ : Formula α}

def Formula.boxlt (n : ℕ) (φ : Formula α) := List.range (n + 1) |>.map (λ i => □^[i] φ) |>.conj₂

notation:90 "□^≤[" n "]" φ => Formula.boxlt n φ

/-- Chagrov & Zakharyaschev, Theorem 3.51 -/
theorem modal_deduction_theorem : (insert ψ Γ) *⊢[L]! φ ↔ ∃ n, Γ *⊢[L]! (□^≤[n] ψ) ➝ φ := by sorry;

/-- Jeřábek, Fact 2.7 -/
lemma modal_deduction_theorem' : Γ *⊢[L]! φ ↔ ∃ Δ : Finset (Formula α), ∃ n, ↑Δ ⊆ Γ ∧ L ⊢! (□^≤[n] Δ.conj) ➝ φ := by
  constructor;
  . intro h;
    obtain ⟨Δ, hΔ₁, hΔ₂⟩ := Context.provable_iff_finset.mp h;
    have : L ⊢! Δ.conj ➝ φ := FConj_DT.mpr hΔ₂;
    have : ∅ *⊢[L]! Δ.conj ➝ φ := Context.of! this;
    obtain ⟨n, h⟩ : ∃ n, ∅ *⊢[L]! (□^≤[n]Δ.conj) ➝ φ := modal_deduction_theorem.mp $ Context.deductInv! this;
    use Δ, n;
    constructor;
    . assumption;
    . exact Context.emptyPrf! h;
  . rintro ⟨Δ, n, hΔ, h⟩;
    have : L ⊢! Δ.conj ➝ φ := Context.emptyPrf! $ Context.deduct! $ modal_deduction_theorem.mpr ⟨n, Context.of! (Γ := ∅) h⟩;
    have : ↑Δ *⊢[L]! φ := FConj_DT.mp this;
    apply Context.weakening! hΔ this;

lemma global_nec (h : Γ *⊢[L]! φ) : Γ *⊢[L]! □φ := by
  obtain ⟨Δ, n, hΔ, h⟩ := modal_deduction_theorem'.mp h;
  apply modal_deduction_theorem'.mpr;
  use Δ, n + 1;
  constructor;
  . assumption;
  . have : L ⊢! (□□^≤[n]Δ.conj) ➝ □φ := box_regularity! h;
    apply C!_trans ?_ this;
    apply C!_trans ?_ collect_box_conj!;
    apply CConj₂Conj₂!_of_provable;
    intro ψ hψ;
    obtain ⟨ξ, hξ, rfl⟩ := List.exists_box_of_mem_box hψ;
    apply FiniteContext.by_axm!;
    obtain ⟨i, hi, rfl⟩ := List.exists_of_range hξ;
    simp only [List.mem_map, List.mem_range];
    use i + 1;
    constructor;
    . omega;
    . simp;

end LO.Modal
