module

public import Foundation.FirstOrder.Arithmetic.Schema.DeltaInduction
public import Foundation.FirstOrder.Arithmetic.Collection.Equiv

/-!
# The `Δ` induction schemes between `𝗜𝚺 n` and `𝗕𝚺(n + 1)`

A $\Delta_{n + 1}$ predicate of a model of `𝗕𝚺(n + 1)` is at once the existential quantification
of a $\Pi_n$ relation and the complement of another such, and it obeys successor induction. In
the other direction, a $\Sigma_n$ formula and its negation are equivalent to an admissible pair for
the `Δ` induction axiom, so `𝗜𝚫 (n + 1)` proves `𝗜𝚺 n`.

## References

- [Sla04, §1.2]
- [Sla04, §2.1]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL.FirstOrder.Bounding (HierarchySymbol)

namespace FFL.FirstOrder.Arithmetic

open _root_.FFL.Entailment

variable {V : Type*} [ORingStructure V] {n : ℕ}

section models

variable {P : V → Prop} {Q R : V → V → Prop}

private lemma definablePred_lt_or_witness_below [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] (hQ : 𝚷ᴬ_[n].DefinableRel Q)
    (a b : V) : 𝚷ᴬ_[n].DefinablePred fun x ↦ a < x ∨ ∃ y < b, Q x y := by
  have h₁ : 𝚷ᴬ_[n].Definable fun v : Fin 1 → V ↦ a < v 0 :=
    .of_iff
      (HierarchySymbol.Definable.retractiont (n := 1)
        (inferInstance : 𝚷ᴬ_[n].DefinableRel (LT.lt : V → V → Prop)) ![&a, #0])
      (by intro v; simp)
  have h₂ : 𝚷ᴬ_[n].Definable
      fun v : Fin 1 → V ↦ ∃ y < (&b : ArithmeticSemiterm V 1).val v id, Q (v 0) y := by
    apply HierarchySymbol.Definable.arithmetic_bexs
    exact .of_iff (hQ.retraction ![1, 0]) (by intro w; simp)
  exact (h₁.or h₂).of_iff (by intro v; simp)

lemma succ_induction_of_complementary_exists_pi [V↓[ℒₒᵣ] ⊧* 𝗕𝚺(n + 1)]
    (hQ : 𝚷ᴬ_[n].DefinableRel Q) (hR : 𝚷ᴬ_[n].DefinableRel R) (hPQ : ∀ x, P x ↔ ∃ w, Q x w)
    (hPR : ∀ x, ¬P x ↔ ∃ w, R x w) (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x := by
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* 𝗕𝚺(n + 1))
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺ n := models_IBroadSigma_of_models_BSigma_succ
  have : V↓[ℒₒᵣ] ⊧* 𝗕𝚷 n :=
    have : 𝗕𝚷 n ⪯ 𝗕𝚺 (n + 1) := CollectionOnPrenexHierarchy_weakerThan_BSigma_succ 𝚷 n
    models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* 𝗕𝚺(n + 1))
  intro a
  by_contra ha
  have hQR : 𝚷ᴬ_[n].DefinableRel fun x y ↦ Q x y ∨ R x y := .of_iff (hQ.or hR) (by intro v; simp)
  obtain ⟨b, hb⟩ := CollectionOnPrenexHierarchy.collection_of_definable (Γ := 𝚷) hQR (a + 1) <| by
    intro x _
    by_cases hx : P x
    · exact ((hPQ x).mp hx).imp fun w hw ↦ Or.inl hw
    · exact ((hPR x).mp hx).imp fun w hw ↦ Or.inr hw
  have h : ∀ x < a + 1, P x → ∃ y < b, Q x y := by
    intro x hx hPx
    obtain ⟨y, hy, hQy | hRy⟩ := hb x hx
    · exact ⟨y, hy, hQy⟩
    · exact absurd hPx ((hPR x).mpr ⟨y, hRy⟩)
  have key : ∀ x, a < x ∨ ∃ y < b, Q x y := by
    apply InductionOnHierarchy.succ_induction 𝚷 n (definablePred_lt_or_witness_below hQ a b)
    · exact Or.inr (h 0 (lt_of_le_of_lt (by simp) (lt_add_one a)) zero)
    · rintro x (hx | ⟨y, -, hy⟩)
      · exact Or.inl (lt_trans hx (lt_add_one x))
      · rcases lt_or_ge a (x + 1) with hax | hax
        · exact Or.inl hax
        · exact Or.inr <|
            h (x + 1) (lt_of_le_of_lt hax (lt_add_one a)) (succ x ((hPQ x).mpr ⟨y, hy⟩))
  obtain hy | ⟨y, -, hy⟩ := key a
  · exact absurd hy (lt_irrefl a)
  · exact ha ((hPQ a).mpr ⟨y, hy⟩)

end models

section theorems

private lemma models_DeltaInductionScheme_of_definablePred
    {C : ArithmeticSemiformula ℕ 1 → Prop} [V↓[ℒₒᵣ] ⊧* 𝗕𝚺(n + 1)]
    (hC : ∀ {φ : ArithmeticSemiformula ℕ 1}, C φ → ∀ f : ℕ → V,
      𝚺ᴬ_[n + 1].DefinablePred fun x : V ↦ φ.Eval ![x] f) :
    V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ ∪ DeltaInductionScheme C := by
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* 𝗕𝚺(n + 1))
  have h₀ : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* 𝗕𝚺(n + 1))
  have : V↓[ℒₒᵣ] ⊧* 𝗕𝚷 n :=
    have : 𝗕𝚷 n ⪯ 𝗕𝚺 (n + 1) := CollectionOnPrenexHierarchy_weakerThan_BSigma_succ 𝚷 n
    models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* 𝗕𝚺(n + 1))
  apply Semantics.ModelsSet.union_iff.mpr
  and_intros
  · exact h₀
  · apply Semantics.ModelsSet.setOf_iff.mpr
    rintro _ ⟨φ, ψ, hφ, hψ, rfl⟩
    apply (models_deltaInd_iff φ ψ).mpr
    intro f heq zero succ
    obtain ⟨Q, hQ, hQiff⟩ := exists_pi_definableRel_iff (hC hφ f)
    obtain ⟨R, hR, hRiff⟩ := exists_pi_definableRel_iff (hC hψ f)
    exact succ_induction_of_complementary_exists_pi hQ hR hQiff
      (fun x ↦ by rw [heq x, not_not]; exact hRiff x) zero succ

lemma models_IDelta_of_models_BSigma_succ (n : ℕ) (V : Type*) [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗕𝚺(n + 1)] : V↓[ℒₒᵣ] ⊧* 𝗜𝚫(n + 1) :=
  models_DeltaInductionScheme_of_definablePred fun hφ f ↦
    Bounding.definablePred_of_hierarchy hφ.hierarchy f

theorem IDelta_weakerThan_BSigma (n : ℕ) : 𝗜𝚫(n + 1) ⪯ 𝗕𝚺(n + 1) :=
  weakerThan_of_models.{0} _ _ fun V _ _ ↦ models_IDelta_of_models_BSigma_succ n V

lemma models_IDeltaOnBroadHierarchy_of_models_BSigma_succ (n : ℕ) (V : Type*) [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗕𝚺(n + 1)] : V↓[ℒₒᵣ] ⊧* 𝗜𝚫⁺(n + 1) :=
  models_DeltaInductionScheme_of_definablePred fun hφ f ↦ Bounding.definablePred_of_hierarchy hφ f

theorem IDeltaOnBroadHierarchy_weakerThan_BSigma (n : ℕ) : 𝗜𝚫⁺(n + 1) ⪯ 𝗕𝚺(n + 1) :=
  weakerThan_of_models.{0} _ _ fun V _ _ ↦
    models_IDeltaOnBroadHierarchy_of_models_BSigma_succ n V

private lemma models_ISigma_of_models_IDelta_succ (n : ℕ) (V : Type*) [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚫 (n + 1)] : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 n := by
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := models_of_ss (U := 𝗜𝚫 (n + 1)) inferInstance Set.subset_union_left
  have hPA : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := mod_paMinus_of_ISigma (s := 0)
  suffices V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ (ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚺 n) by
    simpa [ISigma, InductionOnPrenexHierarchy, Semantics.ModelsSet.union_iff] using ⟨hPA, this⟩
  simp only [InductionScheme]
  apply Semantics.ModelsSet.setOf_iff.mpr
  rintro _ ⟨φ, hφ, rfl⟩
  obtain ⟨φ', hφ', Hφ⟩ := hφ.exists_eval_iff_of_lt 𝚺 (Nat.lt_succ_self n)
  obtain ⟨ψ, hψ, Hψ⟩ := hφ.neg.exists_eval_iff_of_lt 𝚺 (Nat.lt_succ_self n)
  have hax : V↓[ℒₒᵣ] ⊧ (.univCl (deltaInd φ' ψ) : ArithmeticSentence) :=
    models_of_mem (T := 𝗜𝚫 (n + 1)) (Set.mem_union_right _
      (mem_DeltaInductionScheme_of_mem hφ' hψ))
  suffices ∀ f : ℕ → V, φ.Eval ![0] f → (∀ x, φ.Eval ![x] f → φ.Eval ![x + 1] f) →
      ∀ x, φ.Eval ![x] f by
    simpa [models_iff, Semiformula.eval_univCl, succInd, Semiformula.eval_substs,
      Matrix.constant_eq_singleton] using this
  intro f zero succ x
  have := (models_deltaInd_iff φ' ψ).mp hax f (fun x ↦ by rw [← Hφ V, ← Hψ V]; simp)
    ((Hφ V _ f).mp (by simpa using zero))
    (fun x hx ↦ (Hφ V _ f).mp <| succ x <| (Hφ V _ f).mpr hx) x
  exact (Hφ V _ f).mpr this

theorem ISigma_weakerThan_IDelta_succ (n : ℕ) : 𝗜𝚺n ⪯ 𝗜𝚫 (n + 1) :=
  weakerThan_of_models.{0} _ _ fun V _ _ ↦ models_ISigma_of_models_IDelta_succ n V

end theorems

end FFL.FirstOrder.Arithmetic
