module

public import Foundation.FirstOrder.SetTheory.Basic.Misc
public import Foundation.FirstOrder.Syntax.Classical.BoundingHierarchy

@[expose] public section

namespace FFL.FirstOrder.Bounding.Hierarchy

open FFL.FirstOrder.SetTheory
open scoped FFL.FirstOrder.Bounding

variable {ξ : Type*}

lemma setTheory_sigma₁_induction
    {P : (n : ℕ) → SetTheorySemiformula ξ n → Prop}
    (hVerum : ∀ n, P n ⊤)
    (hFalsum : ∀ n, P n ⊥)
    (hEQ : ∀ n t₁ t₂, P n (.rel Language.Eq.eq ![t₁, t₂]))
    (hNEQ : ∀ n t₁ t₂, P n (.nrel Language.Eq.eq ![t₁, t₂]))
    (hMem : ∀ n t₁ t₂, P n (.rel Language.Mem.mem ![t₁, t₂]))
    (hNMem : ∀ n t₁ t₂, P n (.nrel Language.Mem.mem ![t₁, t₂]))
    (hAnd : ∀ n φ ψ,
      ℬ[∈, ℒₛₑₜ].Hierarchy 𝚺 1 φ → ℬ[∈, ℒₛₑₜ].Hierarchy 𝚺 1 ψ →
      P n φ → P n ψ → P n (φ ⋏ ψ))
    (hOr : ∀ n φ ψ,
      ℬ[∈, ℒₛₑₜ].Hierarchy 𝚺 1 φ → ℬ[∈, ℒₛₑₜ].Hierarchy 𝚺 1 ψ →
      P n φ → P n ψ → P n (φ ⋎ ψ))
    (hBall : ∀ n t φ, ℬ[∈, ℒₛₑₜ].Hierarchy 𝚺 1 φ → P (n + 1) φ →
      P n (∀¹[“#0 ∈ !!(Rew.bShift t)”] φ))
    (hExs : ∀ n φ, ℬ[∈, ℒₛₑₜ].Hierarchy 𝚺 1 φ →
      P (n + 1) φ → P n (∃¹ φ))
    (n φ) : ℬ[∈, ℒₛₑₜ].Hierarchy 𝚺 1 φ → P n φ :=
  Hierarchy.sigma₁_induction
    (ℬ := ℬ[∈, ℒₛₑₜ]) (P := P)
    hVerum hFalsum
    (by
      intro n k r v
      cases r
      · change P n (.rel Language.Eq.eq v)
        simpa [←Matrix.fun_eq_vec_two] using hEQ n (v 0) (v 1)
      · change P n (.rel Language.Mem.mem v)
        simpa [←Matrix.fun_eq_vec_two] using hMem n (v 0) (v 1))
    (by
      intro n k r v
      cases r
      · change P n (.nrel Language.Eq.eq v)
        simpa [←Matrix.fun_eq_vec_two] using hNEQ n (v 0) (v 1)
      · change P n (.nrel Language.Mem.mem v)
        simpa [←Matrix.fun_eq_vec_two] using hNMem n (v 0) (v 1))
    hAnd hOr
    (by
      intro R hR n t φ hφ hp
      obtain rfl := Set.mem_singleton_iff.mp hR
      simpa [Semiformula.Operator.mem_def] using hBall n t φ hφ hp)
    hExs
    (by
      intro R hR n t
      obtain rfl := Set.mem_singleton_iff.mp hR
      simpa [Semiformula.Operator.mem_def] using hMem (n + 1) #0 (Rew.bShift t))
    n φ

lemma setTheory_sigma₁_induction' {n φ}
    (hp : ℬ[∈, ℒₛₑₜ].Hierarchy 𝚺 1 φ)
    {P : (n : ℕ) → SetTheorySemiformula ξ n → Prop}
    (hVerum : ∀ n, P n ⊤)
    (hFalsum : ∀ n, P n ⊥)
    (hEQ : ∀ n t₁ t₂, P n (.rel Language.Eq.eq ![t₁, t₂]))
    (hNEQ : ∀ n t₁ t₂, P n (.nrel Language.Eq.eq ![t₁, t₂]))
    (hMem : ∀ n t₁ t₂, P n (.rel Language.Mem.mem ![t₁, t₂]))
    (hNMem : ∀ n t₁ t₂, P n (.nrel Language.Mem.mem ![t₁, t₂]))
    (hAnd : ∀ n φ ψ,
      ℬ[∈, ℒₛₑₜ].Hierarchy 𝚺 1 φ → ℬ[∈, ℒₛₑₜ].Hierarchy 𝚺 1 ψ →
      P n φ → P n ψ → P n (φ ⋏ ψ))
    (hOr : ∀ n φ ψ,
      ℬ[∈, ℒₛₑₜ].Hierarchy 𝚺 1 φ → ℬ[∈, ℒₛₑₜ].Hierarchy 𝚺 1 ψ →
      P n φ → P n ψ → P n (φ ⋎ ψ))
    (hBall : ∀ n t φ, ℬ[∈, ℒₛₑₜ].Hierarchy 𝚺 1 φ → P (n + 1) φ →
      P n (∀¹[“#0 ∈ !!(Rew.bShift t)”] φ))
    (hExs : ∀ n φ, ℬ[∈, ℒₛₑₜ].Hierarchy 𝚺 1 φ →
      P (n + 1) φ → P n (∃¹ φ)) :
    P n φ :=
  setTheory_sigma₁_induction hVerum hFalsum hEQ hNEQ hMem hNMem hAnd hOr hBall hExs
    n φ hp

end FFL.FirstOrder.Bounding.Hierarchy

end
