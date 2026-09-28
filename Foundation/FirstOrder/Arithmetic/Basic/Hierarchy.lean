module

public import Foundation.FirstOrder.Syntax.Classical.Padding
public import Foundation.FirstOrder.Arithmetic.Basic.Model
public import Foundation.FirstOrder.Syntax.Classical.BoundingHierarchy

@[expose] public section

namespace FFL.FirstOrder.Bounding.Hierarchy

open FFL.FirstOrder.Arithmetic

variable {L : Language} [L.LT] {ξ : Type*}

lemma arithmetic_ball {Γ s n} {φ : Semiformula L ξ (n + 1)}
    {t : Semiterm L ξ (n + 1)} :
    t.Positive → ℬ[<, L].Hierarchy Γ s φ →
      ℬ[<, L].Hierarchy Γ s (∀¹[“x. x < !!t”] φ) :=
  Hierarchy.ball (R := Semiformula.Operator.LT.lt) (by rfl)

lemma arithmetic_bexs {Γ s n} {φ : Semiformula L ξ (n + 1)}
    {t : Semiterm L ξ (n + 1)} :
    t.Positive → ℬ[<, L].Hierarchy Γ s φ →
      ℬ[<, L].Hierarchy Γ s (∃¹[“x. x < !!t”] φ) :=
  Hierarchy.bexs (R := Semiformula.Operator.LT.lt) (by rfl)

@[simp] lemma arithmetic_ball_iff {Γ s n} {φ : Semiformula L ξ (n + 1)}
    {t : Semiterm L ξ (n + 1)} (ht : t.Positive) :
    ℬ[<, L].Hierarchy Γ s (∀¹[“x. x < !!t”] φ) ↔ ℬ[<, L].Hierarchy Γ s φ :=
  Hierarchy.ball_iff (R := Semiformula.Operator.LT.lt) (by rfl) ht

@[simp] lemma arithmetic_bexs_iff {Γ s n} {φ : Semiformula L ξ (n + 1)}
    {t : Semiterm L ξ (n + 1)} (ht : t.Positive) :
    ℬ[<, L].Hierarchy Γ s (∃¹[“x. x < !!t”] φ) ↔ ℬ[<, L].Hierarchy Γ s φ :=
  Hierarchy.bexs_iff (R := Semiformula.Operator.LT.lt) (by rfl) ht

@[simp] lemma arithmetic_ballLT_iff {Γ s n} {φ : Semiformula L ξ (n + 1)}
    {t : Semiterm L ξ n} :
    ℬ[<, L].Hierarchy Γ s (φ.ballLT t) ↔ ℬ[<, L].Hierarchy Γ s φ := by
  simp [Semiformula.ballLT]

@[simp] lemma arithmetic_bexsLT_iff {Γ s n} {φ : Semiformula L ξ (n + 1)}
    {t : Semiterm L ξ n} :
    ℬ[<, L].Hierarchy Γ s (φ.bexsLT t) ↔ ℬ[<, L].Hierarchy Γ s φ := by
  simp [Semiformula.bexsLT]

@[simp] lemma arithmetic_ballLTSucc_iff [L.Zero] [L.One] [L.Add] {Γ s n}
    {φ : Semiformula L ξ (n + 1)} {t : Semiterm L ξ n} :
    ℬ[<, L].Hierarchy Γ s (φ.ballLTSucc t) ↔ ℬ[<, L].Hierarchy Γ s φ := by
  simp [Semiformula.ballLTSucc]

@[simp] lemma arithmetic_bexsLTSucc_iff [L.Zero] [L.One] [L.Add] {Γ s n}
    {φ : Semiformula L ξ (n + 1)} {t : Semiterm L ξ n} :
    ℬ[<, L].Hierarchy Γ s (φ.bexsLTSucc t) ↔ ℬ[<, L].Hierarchy Γ s φ := by
  simp [Semiformula.bexsLTSucc]

section LOR

lemma arithmetic_sigma₁_induction
    {P : (n : ℕ) → ArithmeticSemiformula ξ n → Prop}
    (hVerum : ∀ n, P n ⊤)
    (hFalsum : ∀ n, P n ⊥)
    (hEQ : ∀ n t₁ t₂, P n (.rel Language.Eq.eq ![t₁, t₂]))
    (hNEQ : ∀ n t₁ t₂, P n (.nrel Language.Eq.eq ![t₁, t₂]))
    (hLT : ∀ n t₁ t₂, P n (.rel Language.LT.lt ![t₁, t₂]))
    (hNLT : ∀ n t₁ t₂, P n (.nrel Language.LT.lt ![t₁, t₂]))
    (hAnd : ∀ n φ ψ,
      ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1 φ → ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1 ψ →
      P n φ → P n ψ → P n (φ ⋏ ψ))
    (hOr : ∀ n φ ψ,
      ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1 φ → ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1 ψ →
      P n φ → P n ψ → P n (φ ⋎ ψ))
    (hBall : ∀ n t φ, ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1 φ → P (n + 1) φ →
      P n (∀¹[“#0 < !!(Rew.bShift t)”] φ))
    (hExs : ∀ n φ, ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1 φ → P (n + 1) φ → P n (∃¹ φ))
    (n φ) : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1 φ → P n φ :=
  Hierarchy.sigma₁_induction
    (ℬ := ℬ[<, ℒₒᵣ]) (P := P)
    hVerum hFalsum
    (by
      intro n k r v
      cases r
      · change P n (.rel Language.Eq.eq v)
        simpa [←Matrix.fun_eq_vec_two] using hEQ n (v 0) (v 1)
      · change P n (.rel Language.LT.lt v)
        simpa [←Matrix.fun_eq_vec_two] using hLT n (v 0) (v 1))
    (by
      intro n k r v
      cases r
      · change P n (.nrel Language.Eq.eq v)
        simpa [←Matrix.fun_eq_vec_two] using hNEQ n (v 0) (v 1)
      · change P n (.nrel Language.LT.lt v)
        simpa [←Matrix.fun_eq_vec_two] using hNLT n (v 0) (v 1))
    hAnd hOr
    (by
      intro R hR n t φ hφ hp
      obtain rfl := Set.mem_singleton_iff.mp hR
      simpa [Semiformula.Operator.lt_def] using hBall n t φ hφ hp)
    hExs
    (by
      intro R hR n t
      obtain rfl := Set.mem_singleton_iff.mp hR
      simpa [Semiformula.Operator.lt_def] using hLT (n + 1) #0 (Rew.bShift t))
    n φ

lemma arithmetic_sigma₁_induction' {n φ}
    (hp : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1 φ)
    {P : (n : ℕ) → ArithmeticSemiformula ξ n → Prop}
    (hVerum : ∀ n, P n ⊤)
    (hFalsum : ∀ n, P n ⊥)
    (hEQ : ∀ n t₁ t₂, P n (.rel Language.Eq.eq ![t₁, t₂]))
    (hNEQ : ∀ n t₁ t₂, P n (.nrel Language.Eq.eq ![t₁, t₂]))
    (hLT : ∀ n t₁ t₂, P n (.rel Language.LT.lt ![t₁, t₂]))
    (hNLT : ∀ n t₁ t₂, P n (.nrel Language.LT.lt ![t₁, t₂]))
    (hAnd : ∀ n φ ψ,
      ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1 φ → ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1 ψ →
      P n φ → P n ψ → P n (φ ⋏ ψ))
    (hOr : ∀ n φ ψ,
      ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1 φ → ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1 ψ →
      P n φ → P n ψ → P n (φ ⋎ ψ))
    (hBall : ∀ n t φ, ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1 φ → P (n + 1) φ →
      P n (∀¹[“#0 < !!(Rew.bShift t)”] φ))
    (hExs : ∀ n φ, ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1 φ → P (n + 1) φ → P n (∃¹ φ)) :
    P n φ :=
  arithmetic_sigma₁_induction hVerum hFalsum hEQ hNEQ hLT hNLT hAnd hOr hBall hExs n φ hp

end LOR

end FFL.FirstOrder.Bounding.Hierarchy

namespace FFL.FirstOrder.Bounding.Closure

variable {ξ : Type*}

lemma arithmetic_induction {P : (n : ℕ) → ArithmeticSemiformula ξ n → Prop}
    (hVerum : ∀ n, P n ⊤)
    (hFalsum : ∀ n, P n ⊥)
    (hEQ : ∀ n t₁ t₂, P n (.rel Language.Eq.eq ![t₁, t₂]))
    (hNEQ : ∀ n t₁ t₂, P n (.nrel Language.Eq.eq ![t₁, t₂]))
    (hLT : ∀ n t₁ t₂, P n (.rel Language.LT.lt ![t₁, t₂]))
    (hNLT : ∀ n t₁ t₂, P n (.nrel Language.LT.lt ![t₁, t₂]))
    (hAnd : ∀ n φ ψ, ℬ[<, ℒₒᵣ].Closure φ → ℬ[<, ℒₒᵣ].Closure ψ →
      P n φ → P n ψ → P n (φ ⋏ ψ))
    (hOr : ∀ n φ ψ, ℬ[<, ℒₒᵣ].Closure φ → ℬ[<, ℒₒᵣ].Closure ψ →
      P n φ → P n ψ → P n (φ ⋎ ψ))
    (hBall : ∀ n t φ, ℬ[<, ℒₒᵣ].Closure φ → P (n + 1) φ →
      P n (∀¹[“#0 < !!(Rew.bShift t)”] φ))
    (hBex : ∀ n t φ, ℬ[<, ℒₒᵣ].Closure φ → P (n + 1) φ →
      P n (∃¹[“#0 < !!(Rew.bShift t)”] φ))
    (n φ) : ℬ[<, ℒₒᵣ].Closure φ → P n φ := by
  intro h;
  induction h with
  | verum n => exact hVerum n;
  | falsum n => exact hFalsum n;
  | rel r v =>
    cases r <;> rw [Matrix.fun_eq_vec_two v];
    exacts [hEQ _ _ _, hLT _ _ _];
  | nrel r v =>
    cases r <;> rw [Matrix.fun_eq_vec_two v];
    exacts [hNEQ _ _ _, hNLT _ _ _];
  | and hp hq ihp ihq => exact hAnd _ _ _ hp hq ihp ihq;
  | or hp hq ihp ihq => exact hOr _ _ _ hp hq ihp ihq;
  | ball hR ht hp ih =>
    obtain rfl := Set.mem_singleton_iff.mp hR;
    obtain ⟨t, rfl⟩ := Rew.positive_iff.mp ht;
    exact hBall _ t _ hp ih;
  | bexs hR ht hp ih =>
    obtain rfl := Set.mem_singleton_iff.mp hR;
    obtain ⟨t, rfl⟩ := Rew.positive_iff.mp ht;
    exact hBex _ t _ hp ih;

lemma arithmetic_induction_open {P : (n : ℕ) → ArithmeticSemiformula ξ n → Prop}
    (hOpen : ∀ n φ, Semiformula.Open φ → P n φ)
    (hAnd : ∀ n φ ψ, ℬ[<, ℒₒᵣ].Closure φ → ℬ[<, ℒₒᵣ].Closure ψ →
      P n φ → P n ψ → P n (φ ⋏ ψ))
    (hOr : ∀ n φ ψ, ℬ[<, ℒₒᵣ].Closure φ → ℬ[<, ℒₒᵣ].Closure ψ →
      P n φ → P n ψ → P n (φ ⋎ ψ))
    (hBall : ∀ n t φ, ℬ[<, ℒₒᵣ].Closure φ → P (n + 1) φ →
      P n (∀¹[“#0 < !!(Rew.bShift t)”] φ))
    (hBex : ∀ n t φ, ℬ[<, ℒₒᵣ].Closure φ → P (n + 1) φ →
      P n (∃¹[“#0 < !!(Rew.bShift t)”] φ))
    (n φ) : ℬ[<, ℒₒᵣ].Closure φ → P n φ :=
  arithmetic_induction
    (fun _ ↦ hOpen _ _ (by simp))
    (fun _ ↦ hOpen _ _ (by simp))
    (fun _ _ _ ↦ hOpen _ _ (by simp))
    (fun _ _ _ ↦ hOpen _ _ (by simp))
    (fun _ _ _ ↦ hOpen _ _ (by simp))
    (fun _ _ _ ↦ hOpen _ _ (by simp))
    hAnd hOr hBall hBex n φ

end FFL.FirstOrder.Bounding.Closure

namespace FFL.FirstOrder

abbrev ArithmeticTheory.SoundOnHierarchy (T : ArithmeticTheory) (Γ : Polarity) (k : ℕ) :=
  T.SoundOn (ℬ[<, ℒₒᵣ].Hierarchy Γ k)

lemma ArithmeticTheory.soundOnHierarchy (T : ArithmeticTheory) (Γ : Polarity) (k : ℕ)
    [T.SoundOnHierarchy Γ k] {σ : ArithmeticSentence} :
    T ⊢ σ → ℬ[<, ℒₒᵣ].Hierarchy Γ k σ → ℕ↓[ℒₒᵣ] ⊧ σ := SoundOn.sound

instance (T : ArithmeticTheory) [T.SoundOnHierarchy 𝚺 1] : Entailment.Consistent T :=
  T.consistent_of_sound (ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1) (by simp)

instance (T : ArithmeticTheory) [T.SoundOnHierarchy 𝚷 2] : Entailment.Consistent T :=
  T.consistent_of_sound (ℬ[<, ℒₒᵣ].Hierarchy 𝚷 2) (by simp)

end FFL.FirstOrder
