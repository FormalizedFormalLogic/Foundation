module

public import Foundation.FirstOrder.Arithmetic.Collection.Equivalence

/-!
# The induction scheme `𝗜𝚺 n` from the collection scheme `𝗕𝚺 (n + 1)`

## References

- [HP98, Lemma I.2.15]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open _root_.FFL.Entailment

variable {V : Type*} [ORingStructure V] {n : ℕ}

section models

private lemma definable_step {Q : V → V → Prop} (hQ : 𝚷-[n].DefinableRel Q) :
    𝚷-[n + 1].DefinableRel fun x w ↦ (¬∃ z, Q x z) ∨ Q (x + 1) w := by
  have hex : 𝚺-[n + 1].DefinablePred fun x ↦ ∃ z, Q x z := by
    apply HierarchySymbol.Definable.exs;
    exact HierarchySymbol.Definable.of_iff
      ((hQ.of_lt (s := n + 1) (Γ := 𝚺) (by simp)).retraction ![1, 0]) (by intro w; simp);
  apply HierarchySymbol.Definable.or;
  . exact HierarchySymbol.Definable.of_iff (hex.notSigma.retraction ![0]) (by intro v; simp);
  . exact HierarchySymbol.Definable.of_iff
      (HierarchySymbol.Definable.retractiont 2 (hQ.of_lt (s := n + 1) (Γ := 𝚷) (by simp))
        ![‘#0 + 1’, #1]) (by intro v; simp);

private lemma definable_bounded {Q : V → V → Prop} (hQ : 𝚷-[n].DefinableRel Q) (a u : V) :
    𝚷-[n].DefinablePred fun x ↦ ∃ y < u, Q x y ∨ a < x := by
  have hlt : 𝚷-[n].Definable fun w : Fin 2 → V ↦ a < w 1 :=
    HierarchySymbol.Definable.of_iff
      (HierarchySymbol.Definable.retractiont 2
        (inferInstance : 𝚷-[n].DefinableRel (LT.lt : V → V → Prop)) ![&a, #1])
      (by intro w; simp);
  have h : 𝚷-[n].Definable
      fun v : Fin 1 → V ↦ ∃ y < (&u : ArithmeticSemiterm V 1).val v id, Q (v 0) y ∨ a < v 0 := by
    apply HierarchySymbol.Definable.bexs;
    exact HierarchySymbol.Definable.of_iff ((hQ.retraction ![1, 0]).or hlt) (by intro w; simp);
  exact h.of_iff (by intro v; simp);

variable [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 n]

lemma succ_induction_of_exists_pi
    (hcol : ∀ ψ : ArithmeticSemiformula ℕ 2, Hierarchy 𝚷 (n + 1) ψ →
      V↓[ℒₒᵣ] ⊧ (.univCl (collectionAxiom ψ) : ArithmeticSentence))
    {P : V → Prop} {Q : V → V → Prop} (hQ : 𝚷-[n].DefinableRel Q) (hPQ : ∀ x, P x ↔ ∃ w, Q x w)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x := by
  intro a;
  obtain ⟨v, hv⟩ := exists_bound_of_definable hcol (definable_step hQ) a <| by
    intro x _;
    by_cases hx : ∃ z, Q x z;
    . exact ((hPQ (x + 1)).mp (succ x ((hPQ x).mpr hx))).imp fun w hw ↦ Or.inr hw;
    . exact ⟨0, Or.inl hx⟩;
  obtain ⟨w₀, hw₀⟩ := (hPQ 0).mp zero;
  have hpos : (0 : V) < max v (w₀ + 1) :=
    lt_of_lt_of_le (lt_of_le_of_lt (by simp) (lt_add_one w₀)) (le_max_right v (w₀ + 1));
  have key : ∀ x, ∃ y < max v (w₀ + 1), Q x y ∨ a < x := by
    apply InductionOnHierarchy.succ_induction 𝚷 n (definable_bounded hQ a _)
      ⟨w₀, lt_of_lt_of_le (lt_add_one w₀) (le_max_right v (w₀ + 1)), Or.inl hw₀⟩;
    rintro x ⟨y, -, hy | hy⟩;
    . by_cases hxa : x < a;
      . obtain ⟨z, hzv, hz | hz⟩ := hv x hxa;
        . exact absurd ⟨y, hy⟩ hz;
        . exact ⟨z, lt_of_lt_of_le hzv (le_max_left v (w₀ + 1)), Or.inl hz⟩;
      . exact ⟨0, hpos, Or.inr (lt_of_le_of_lt (not_lt.mp hxa) (lt_add_one x))⟩;
    . exact ⟨0, hpos, Or.inr (lt_trans hy (lt_add_one x))⟩;
  obtain ⟨y, -, hy | hy⟩ := key a;
  . exact (hPQ a).mpr ⟨y, hy⟩;
  . exact absurd hy (lt_irrefl a);

end models

section theorems

private lemma models_ISigma_succ [V↓[ℒₒᵣ] ⊧* 𝗕𝚺 (n + 2)] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 n] :
    V↓[ℒₒᵣ] ⊧* 𝗜𝚺 (n + 1) := by
  have hPA : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (T := 𝗣𝗔⁻) (U := 𝗕𝚺 (n + 2)) inferInstance;
  have : V↓[ℒₒᵣ] ⊧* 𝗕𝚷 n := models_of_ss inferInstance
    ((CollectionOnHierarchy_subset_BSigma_succ 𝚷 n).trans
      (CollectionOnHierarchy_subset_mono (Nat.le_succ (n + 1))));
  have hcol : ∀ ψ : ArithmeticSemiformula ℕ 2, Hierarchy 𝚷 (n + 1) ψ →
      V↓[ℒₒᵣ] ⊧ (.univCl (collectionAxiom ψ) : ArithmeticSentence) := fun _ hψ ↦
    models_of_mem (T := 𝗕𝚺 (n + 2))
      (Set.mem_union_right _ (mem_CollectionScheme_of_mem (hψ.accum 𝚺)));
  suffices V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ (Hierarchy 𝚺 (n + 1)) by
    simpa [ISigma, InductionOnHierarchy, Semantics.ModelsSet.union_iff] using ⟨hPA, this⟩;
  simp only [InductionScheme];
  apply Semantics.ModelsSet.setOf_iff.mpr;
  rintro _ ⟨φ, hφ, rfl⟩;
  suffices ∀ f : ℕ → V, φ.Eval ![0] f → (∀ x, φ.Eval ![x] f → φ.Eval ![x + 1] f) →
      ∀ x, φ.Eval ![x] f by
    simpa [models_iff, Semiformula.eval_univCl, succInd, Semiformula.eval_substs,
      Matrix.constant_eq_singleton] using this;
  intro f;
  obtain ⟨χ, hχ, hiff⟩ := exists_pi_eval_iff hφ f;
  exact succ_induction_of_exists_pi hcol (definableRel_of_hierarchy hχ f) hiff;

lemma models_ISigma_of_models_BSigma_succ :
    ∀ (n : ℕ) (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗕𝚺 (n + 1)], V↓[ℒₒᵣ] ⊧* 𝗜𝚺 n := by
  intro n;
  induction n with
  | zero => intro V _ _; exact models_of_subtheory (T := 𝗜𝚺₀) (U := 𝗕𝚺 1) inferInstance;
  | succ n ih =>
    intro V _ _;
    have : V↓[ℒₒᵣ] ⊧* 𝗕𝚺 (n + 1) :=
      models_of_ss inferInstance (CollectionOnHierarchy_subset_mono (Nat.le_succ (n + 1)));
    have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 n := ih V;
    exact models_ISigma_succ;

theorem ISigma_weakerThan_BSigma_succ (n : ℕ) : 𝗜𝚺 n ⪯ 𝗕𝚺 (n + 1) :=
  weakerThan_of_models.{0} _ _ fun V _ _ ↦ models_ISigma_of_models_BSigma_succ n V

end theorems

end FFL.FirstOrder.Arithmetic
