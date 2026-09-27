module

public import Foundation.FirstOrder.Incompleteness.ProvabilityAbstraction.Reflection
public import Foundation.ProvabilityLogic.GL.Arithmetic
public import Foundation.ProvabilityLogic.GL.FiniteLocalReflection

/-!
# Collapsing finitely many local reflection instances

If `T` derives `σ` from finitely many local reflection instances `𝔅 τᵢ 🡒 τᵢ`, then it derives `σ`
from the instances at the sentences `ρ₀ := σ`, `ρᵢ₊₁ := ρᵢ ⋎ 𝔅 ρᵢ`, which depend on `σ` alone.

## References

- [Bek99, Lemma 4.2]
- [Bek99, Lemma 5.2]
-/

@[expose] public section

namespace FFL.FirstOrder.ProvabilityAbstraction.Provability

open FFL.Entailment FFL.ProvabilityLogic FFL.ProvabilityLogic.FiniteLocalReflection

variable {L : Language} [L.ReferenceableBy L] {T₀ T : Theory L} (𝔅 : Provability T₀ T)

def collapseSeq (σ : Sentence L) : ℕ → Sentence L
  | 0 => σ
  | i + 1 => collapseSeq σ i ⋎ 𝔅 (collapseSeq σ i)

variable [L.DecidableEq] [T₀ ⪯ T] [𝔅.HBL] [Diagonalization T₀] {m : ℕ}

theorem collapse_localReflection {σ : Sentence L} {τ : Fin (m + 1) → Sentence L}
    (h : T ⊢ (⩕ i, 𝔅.refl (τ i)) 🡒 σ) :
    T ⊢ (⩕ i : Fin (m + 1), 𝔅.refl (𝔅.collapseSeq σ i)) 🡒 σ := by
  let f : Realization (Option (Fin (m + 1))) L := ⟨fun o ↦ o.elim σ τ⟩
  have hH : T ⊢ (hyp m).interpret f 𝔅 :=
    C_trans (right_Uconj_intro _ _ fun i ↦ interpret_conj_left <| List.mem_ofFn.mpr ⟨i, rfl⟩) h;
  have hG : T ⊢ (hyp m 🡒 □hyp m 🡒 reflection m 🡒 #none).interpret f 𝔅 :=
    WeakerThan.pbl <| Logic.GL.arithmetical_soundness (𝔅 := 𝔅) (collapse_mem m);
  have hR : T ⊢ (⩕ i : Fin (m + 1), 𝔅.refl (𝔅.collapseSeq σ i)) 🡒 (reflection m).interpret f 𝔅 := by
    have e : ∀ i, T ⊢ (seq (#none) i).interpret f 𝔅 🡘 𝔅.collapseSeq σ i := by
      intro i;
      induction i with
      | zero => exact E_id;
      | succ i ih =>
        simp only [seq, collapseSeq, Formula.interpret];
        cl_prover [ih, WeakerThan.pbl (𝓣 := T) (𝔅.ext ih)];
    apply interpret_conj_right;
    intro B hB;
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hB;
    apply C_trans (left_Uconj_intro _ i);
    simp only [Formula.interpret];
    cl_prover [e i, WeakerThan.pbl (𝓣 := T) (𝔅.ext (e i))];
  exact C_trans hR <| hG ⨀ hH ⨀ WeakerThan.pbl (𝔅.D1 hH);

theorem iterate_bot_of_refutable_localReflection {τ : Fin (m + 1) → Sentence L}
    (h : T ⊢ ∼⩕ i, 𝔅.refl (τ i)) : T ⊢ 𝔅^[m + 1] ⊥ := by
  have e : ∀ i, T ⊢ 𝔅.collapseSeq ⊥ i 🡘 𝔅^[i] ⊥ := by
    intro i;
    induction i with
    | zero => exact E_id;
    | succ i ih =>
      have hb : T ⊢ 𝔅 (𝔅.collapseSeq ⊥ i) 🡘 𝔅^[i + 1] ⊥ := by
        rw [Function.iterate_succ_apply']; exact WeakerThan.pbl (𝓣 := T) (𝔅.ext ih);
      simp only [collapseSeq];
      cl_prover [ih, hb, boxBot_monotone (𝔅 := 𝔅) (Nat.le_succ i)];
  have hr : T ⊢ ∼𝔅^[m + 1] ⊥ 🡒 ⩕ i : Fin (m + 1), 𝔅.refl (𝔅.collapseSeq ⊥ i) :=
    right_Uconj_intro _ _ fun i ↦ by
      have : T ⊢ 𝔅.collapseSeq ⊥ i ⋎ 𝔅 (𝔅.collapseSeq ⊥ i) 🡘 𝔅^[i + 1] ⊥ := e (i + 1);
      cl_prover [this, boxBot_monotone (𝔅 := 𝔅) i.isLt];
  have := 𝔅.collapse_localReflection (σ := ⊥) (τ := τ) (by cl_prover [h]);
  cl_prover [this, hr];

end FFL.FirstOrder.ProvabilityAbstraction.Provability

end
