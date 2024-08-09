import Arithmetization.ISigmaOne.Bit

/-!

# $\Sigma_n \lor \Pi_n$-Induction

-/

noncomputable section

namespace LO.Arith

open FirstOrder FirstOrder.Arith

variable {V : Type*} [Zero V] [One V] [Add V] [Mul V] [LT V]


variable (m : ℕ) [Fact (1 ≤ m)] [V ⊧ₘ* 𝐈𝐍𝐃𝚺 m]

lemma induction_sigma_or_pi {P Q : V → Prop} (hP : (𝚺, m)-Predicate P) (hQ : (𝚷, m)-Predicate Q)
    (zero : P 0 ∨ Q 0) (succ : ∀ x, P x ∨ Q x → P (x + 1) ∨ Q (x + 1)) : ∀ x, P x ∨ Q x := by
  haveI : V ⊧ₘ* 𝐈𝚺₁ := mod_iSigma_of_le (show 1 ≤ m from Fact.out)
  intro a
  have : ∃ p < exp (a + 1), ∀ x ≤ a, x ∈ p ↔ P x := by
    simpa [lt_succ_iff_le] using finset_comprehension hP (a + 1)
  rcases this with ⟨p, _, hp⟩
  have : ∃ q < exp (a + 1), ∀ x ≤ a, x ∈ q ↔ Q x := by
    simpa [lt_succ_iff_le] using finset_comprehension hQ (a + 1)
  rcases this with ⟨q, _, hq⟩
  have : ∀ x ≤ a, x ∈ p ∨ x ∈ q := by
    intro x hx
    induction x using induction_iSigmaOne
    · clear hp hq zero succ
      definability
    case zero => simpa [hp, hq] using zero
    case succ x ih =>
      have hx' : x ≤ a := le_trans le_self_add hx
      have : P x ∨ Q x := by simpa [hp x hx', hq x hx'] using ih hx'
      simpa [hp (x + 1) hx, hq (x + 1) hx] using succ x this
  have := this a (by rfl)
  simpa [hp, hq] using this

lemma order_induction_sigma_or_pi {P Q : V → Prop} (hP : (𝚺, m)-Predicate P) (hQ : (𝚷, m)-Predicate Q)
    (ind : ∀ x, (∀ y < x, P y ∨ Q y) → P x ∨ Q x) : ∀ x, P x ∨ Q x := by
  haveI : V ⊧ₘ* 𝐈𝚺₁ := mod_iSigma_of_le (show 1 ≤ m from Fact.out)
  intro a
  have : ∃ p < exp (a + 1), ∀ x ≤ a, x ∈ p ↔ P x := by
    simpa [lt_succ_iff_le] using finset_comprehension hP (a + 1)
  rcases this with ⟨p, _, hp⟩
  have : ∃ q < exp (a + 1), ∀ x ≤ a, x ∈ q ↔ Q x := by
    simpa [lt_succ_iff_le] using finset_comprehension hQ (a + 1)
  rcases this with ⟨q, _, hq⟩
  have : ∀ x ≤ a, x ∈ p ∨ x ∈ q := by
    intro x hx
    induction x using order_induction_iSigmaOne
    · clear hp hq ind
      apply LO.FirstOrder.Arith.Definable.imp
      · simp_all only [SigmaPiDelta.alt_sigma, Fin.isValue]
        apply LO.FirstOrder.Arith.Definable.comp₂_infer
        · simp_all only [zero_add, Fin.isValue, DefinableFunction.var]
        · simp_all only [zero_add, DefinableFunction.const]
      · simp_all only [Fin.isValue]
        apply LO.FirstOrder.Arith.Definable.or
        · apply LO.FirstOrder.Arith.Definable.comp₂_infer
          · simp_all only [zero_add, Fin.isValue, DefinableFunction.var]
          · simp_all only [zero_add, DefinableFunction.const]
        · apply LO.FirstOrder.Arith.Definable.comp₂_infer
          · simp_all only [zero_add, Fin.isValue, DefinableFunction.var]
          · simp_all only [zero_add, DefinableFunction.const]
    case ind z ih =>
      have : P z ∨ Q z :=
        ind z (fun y hy ↦ by
          have hya : y ≤ a := le_trans (le_of_lt hy) hx
          have : y ∈ p ∨ y ∈ q := ih y hy hya
          simpa [hp, hq, hya] using this)
      simpa [hp, hq, hx] using this
  simpa [hp, hq] using this a (by rfl)

end LO.Arith

end
