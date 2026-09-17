module

public import Foundation.FirstOrder.Arithmetic.Schemata

/-!
# Equivalence of the least number schemes `𝗟𝚺`, `𝗟𝚷` with `𝗜𝚺`

## References

- [HP98, Theorem I.2.4, Lemma I.2.8, Lemma I.2.12]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open _root_.FFL.Entailment

section models

variable {V : Type*} [ORingStructure V]

namespace LeastNumberScheme

variable {C : ArithmeticSemiformula ℕ 1 → Prop} [V↓[ℒₒᵣ] ⊧* LeastNumberScheme C]

private lemma leastNumber_eval {φ : ArithmeticSemiformula ℕ 1} (hφ : C φ) (v : ℕ → V) :
    (∃ x, φ.Eval ![x] v) → ∃ z, φ.Eval ![z] v ∧ ∀ x < z, ¬φ.Eval ![x] v := by
  have : V↓[ℒₒᵣ] ⊧ .univCl (leastNumber φ) :=
    Theory.models (T := LeastNumberScheme C) V (by simpa using mem_LeastNumberScheme_of_mem hφ);
  revert v;
  simpa [models_iff, Semiformula.eval_univCl, leastNumber, Semiformula.eval_substs,
    Matrix.constant_eq_singleton] using this;

lemma least_number {P : V → Prop}
    (hP : ∃ e : ℕ → V, ∃ φ : ArithmeticSemiformula ℕ 1, C φ ∧ ∀ x, P x ↔ φ.Eval ![x] e)
    {x} (h : P x) : ∃ y, P y ∧ ∀ z < y, ¬P z := by
  rcases hP with ⟨e, φ, Cφ, hφ⟩;
  simpa [← hφ] using leastNumber_eval (V := V) Cφ e ⟨x, (hφ x).mp h⟩;

end LeastNumberScheme

namespace LeastNumberOnHierarchy

variable (Γ : Polarity) (s : ℕ) [V↓[ℒₒᵣ] ⊧* 𝗟 Γ s]

instance : V↓[ℒₒᵣ] ⊧* LeastNumberScheme (Hierarchy Γ s) := models_of_subtheory ‹V↓[ℒₒᵣ] ⊧* 𝗟 Γ s›

lemma least_number {P : V → Prop} (hP : Γ-[s].DefinablePred P) {x} (h : P x) :
    ∃ y, P y ∧ ∀ z < y, ¬P z :=
  LeastNumberScheme.least_number (P := P) (C := Hierarchy Γ s) (by
    classical
    rcases hP with ⟨φ, hp⟩;
    have : Inhabited V := Classical.inhabited_of_nonempty';
    use φ.val.enumerateFVar, (Rew.rewriteMap φ.val.idxOfFVar) ▹ φ.val;
    and_intros;
    · simp;
    · intro x;
      simp [Semiformula.eval_rewriteMap, hp.df.iff]
  ) h

lemma succ_induction {P : V → Prop} (hP : Γ.alt-[s].DefinablePred P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x := by
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory ‹V↓[ℒₒᵣ] ⊧* 𝗟 Γ s›;
  have : V↓[ℒₒᵣ] ⊧* 𝗤 := models_of_subtheory this;
  by_contra! hcon;
  obtain ⟨a, ha⟩ := hcon;
  obtain ⟨y, hy, hmin⟩ := least_number Γ s (P := fun x ↦ ¬P x) (by
    apply Arithmetic.HierarchySymbol.Definable.not;
    simpa [SigmaPiDelta.alt_coe];
  ) ha;
  push Not at hmin;
  obtain ⟨z, rfl⟩ := Arithmetic.exists_succ_of_ne_zero <|
    show y ≠ 0 by
    rintro rfl;
    contradiction;
  apply hy;
  apply succ;
  apply hmin;
  apply lt_succ_iff_le.mpr;
  apply le_rfl;

lemma models_alt : V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗 Γ.alt s := by
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory ‹V↓[ℒₒᵣ] ⊧* 𝗟 Γ s›;
  suffices V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ (Hierarchy Γ.alt s) by
    simpa [InductionOnHierarchy, Semantics.ModelsSet.union_iff] using ⟨‹_›, this⟩;
  simp only [InductionScheme];
  apply Semantics.ModelsSet.setOf_iff.mpr;
  rintro _ ⟨φ, hφ, rfl⟩;
  suffices ∀ v : ℕ → V, φ.Eval ![0] v → (∀ x, φ.Eval ![x] v → φ.Eval ![x + 1] v) →
      ∀ x, φ.Eval ![x] v by
    simpa [models_iff, Semiformula.eval_univCl, succInd, Semiformula.eval_substs,
      Matrix.constant_eq_singleton] using this;
  intro v;
  exact succ_induction Γ s (definablePred_of_hierarchy hφ v);

end LeastNumberOnHierarchy

variable (s : ℕ)

lemma models_LeastNumberOnHierarchy_of_ISigma (Γ : Polarity) (s : ℕ) [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s] :
    V↓[ℒₒᵣ] ⊧* 𝗟 Γ s := by
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory ‹V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s›;
  suffices V↓[ℒₒᵣ] ⊧* LeastNumberScheme (Hierarchy Γ s) by
    simpa [LeastNumberOnHierarchy, Semantics.ModelsSet.union_iff] using ⟨‹_›, this⟩;
  simp only [LeastNumberScheme];
  apply Semantics.ModelsSet.setOf_iff.mpr;
  rintro _ ⟨φ, hφ, rfl⟩;
  suffices ∀ v : ℕ → V, (∃ x, φ.Eval ![x] v) → ∃ z, φ.Eval ![z] v ∧ ∀ x < z, ¬φ.Eval ![x] v by
    simpa [models_iff, Semiformula.eval_univCl, leastNumber, Semiformula.eval_substs,
      Matrix.constant_eq_singleton] using this;
  intro v ⟨x, hx⟩;
  exact InductionOnHierarchy.least_number Γ s (definablePred_of_hierarchy hφ v) hx;

instance models_LSigma_of_ISigma [V↓[ℒₒᵣ] ⊧* 𝗜𝚺s] : V↓[ℒₒᵣ] ⊧* 𝗟𝚺s :=
  models_LeastNumberOnHierarchy_of_ISigma 𝚺 s

instance models_LPi_of_ISigma [V↓[ℒₒᵣ] ⊧* 𝗜𝚺s] : V↓[ℒₒᵣ] ⊧* 𝗟𝚷s :=
  models_LeastNumberOnHierarchy_of_ISigma 𝚷 s

instance models_IPi_of_LSigma [V↓[ℒₒᵣ] ⊧* 𝗟𝚺s] : V↓[ℒₒᵣ] ⊧* 𝗜𝚷s :=
  LeastNumberOnHierarchy.models_alt 𝚺 s

instance models_ISigma_of_LPi [V↓[ℒₒᵣ] ⊧* 𝗟𝚷s] : V↓[ℒₒᵣ] ⊧* 𝗜𝚺s :=
  LeastNumberOnHierarchy.models_alt 𝚷 s

end models

section theorems

theorem ISigma_equiv_IPi (s : ℕ) : 𝗜𝚺 s ≊ 𝗜𝚷 s :=
  equiv_of_models.{0, 0} (fun _ _ _ ↦ inferInstance) (fun _ _ _ ↦ inferInstance)

theorem LSigma_equiv_ISigma (s : ℕ) : 𝗟𝚺 s ≊ 𝗜𝚺 s :=
  equiv_of_models.{0, 0} (fun _ _ _ ↦ inferInstance) (fun _ _ _ ↦ inferInstance)

theorem LPi_equiv_ISigma (s : ℕ) : 𝗟𝚷 s ≊ 𝗜𝚺 s :=
  equiv_of_models.{0, 0} (fun _ _ _ ↦ inferInstance) (fun _ _ _ ↦ inferInstance)

end theorems

end FFL.FirstOrder.Arithmetic
