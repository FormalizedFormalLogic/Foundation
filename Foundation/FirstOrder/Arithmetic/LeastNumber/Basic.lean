module

public import Foundation.FirstOrder.Arithmetic.Schemata

/-!
# The least number schemes `𝗟𝚺` and `𝗟𝚷`

## References

- [HP98, §I.2(a), I.2.3, Theorem I.2.4, Lemma I.2.8, Lemma I.2.12]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open _root_.FFL.Entailment

section axioms

def LeastNumberScheme (Γ : ArithmeticSemiformula ℕ 1 → Prop) : ArithmeticTheory :=
  { ψ | ∃ φ : ArithmeticSemiformula ℕ 1, Γ φ ∧ ψ = .univCl (leastNumber φ) }

abbrev LeastNumberOnHierarchy (Γ : Polarity) (n : ℕ) : ArithmeticTheory :=
  𝗣𝗔⁻ ∪ LeastNumberScheme (Arithmetic.Hierarchy Γ n)

prefix:max "𝗟 " => LeastNumberOnHierarchy

abbrev LSigma (n : ℕ) : ArithmeticTheory := 𝗟 𝚺 n

prefix:max "𝗟𝚺" => LSigma

abbrev LPi (n : ℕ) : ArithmeticTheory := 𝗟 𝚷 n

prefix:max "𝗟𝚷" => LPi

variable {C C' : ArithmeticSemiformula ℕ 1 → Prop} {Γ : Polarity}

lemma LeastNumberScheme_subset (h : ∀ {φ : ArithmeticSemiformula ℕ 1}, C φ → C' φ) :
    LeastNumberScheme C ⊆ LeastNumberScheme C' := by
  rintro _ ⟨φ, hφ, rfl⟩; exact ⟨φ, h hφ, rfl⟩;

lemma mem_LeastNumberScheme_of_mem {φ : ArithmeticSemiformula ℕ 1} (hφ : C φ) :
    .univCl (leastNumber φ) ∈ LeastNumberScheme C := ⟨φ, hφ, rfl⟩

lemma LeastNumberOnHierarchy_subset_mono {n₁ n₂} (h : n₁ ≤ n₂) : 𝗟 Γ n₁ ⊆ 𝗟 Γ n₂ :=
  Set.union_subset_union_right _ (LeastNumberScheme_subset (fun H ↦ H.mono h))

lemma LeastNumberOnHierarchy_weakerThan_of_le {n₁ n₂} (h : n₁ ≤ n₂) : 𝗟 Γ n₁ ⪯ 𝗟 Γ n₂ :=
  WeakerThan.ofSubset (LeastNumberOnHierarchy_subset_mono h)

instance (Γ : Polarity) (n : ℕ) : 𝗣𝗔⁻ ⪯ 𝗟 Γ n := WeakerThan.ofSubset Set.subset_union_left

instance (Γ : Polarity) (n : ℕ) : 𝗘𝗤 ℒₒᵣ ⪯ 𝗟 Γ n :=
  WeakerThan.trans (inferInstance : 𝗘𝗤 ℒₒᵣ ⪯ 𝗣𝗔⁻) inferInstance

end axioms

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

variable (Γ : Polarity) (m : ℕ) [V↓[ℒₒᵣ] ⊧* 𝗟 Γ m]

instance : V↓[ℒₒᵣ] ⊧* LeastNumberScheme (Hierarchy Γ m) := models_of_subtheory ‹V↓[ℒₒᵣ] ⊧* 𝗟 Γ m›

lemma least_number {P : V → Prop} (hP : Γ-[m].DefinablePred P) {x} (h : P x) :
    ∃ y, P y ∧ ∀ z < y, ¬P z :=
  LeastNumberScheme.least_number (P := P) (C := Hierarchy Γ m) (by
    classical
    rcases hP with ⟨φ, hp⟩;
    have : Inhabited V := Classical.inhabited_of_nonempty';
    use φ.val.enumerateFVar, (Rew.rewriteMap φ.val.idxOfFVar) ▹ φ.val;
    and_intros;
    . simp;
    . intro x;
      simp [Semiformula.eval_rewriteMap, hp.df.iff]
  ) h

lemma succ_induction {P : V → Prop} (hP : Γ.alt-[m].DefinablePred P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x := by
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory ‹V↓[ℒₒᵣ] ⊧* 𝗟 Γ m›;
  have : V↓[ℒₒᵣ] ⊧* 𝗤 := models_of_subtheory this;
  by_contra! hcon;
  obtain ⟨a, ha⟩ := hcon;
  obtain ⟨y, hy, hmin⟩ := least_number Γ m (P := fun x ↦ ¬P x) (by
    apply Arithmetic.HierarchySymbol.Definable.not;
    simpa [SigmaPiDelta.alt_coe];
  ) ha;
  push Not at hmin;
  obtain ⟨z, rfl⟩ := Arithmetic.exists_succ_of_ne_zero $
    show y ≠ 0 by
    rintro rfl;
    contradiction;
  apply hy;
  apply succ;
  apply hmin;
  apply lt_succ_iff_le.mpr;
  apply le_rfl;

end LeastNumberOnHierarchy

variable (n : ℕ)

instance models_LSigma_of_ISigma [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 n] : V↓[ℒₒᵣ] ⊧* 𝗟𝚺 n := by
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory ‹V↓[ℒₒᵣ] ⊧* 𝗜𝚺 n›;
  suffices V↓[ℒₒᵣ] ⊧* LeastNumberScheme (Hierarchy 𝚺 n) by
    simpa [LSigma, LeastNumberOnHierarchy, Semantics.ModelsSet.union_iff] using ⟨‹_›, this⟩;
  simp only [LeastNumberScheme];
  refine Semantics.ModelsSet.setOf_iff.mpr ?_;
  rintro _ ⟨φ, hφ, rfl⟩;
  suffices ∀ v : ℕ → V, (∃ x, φ.Eval ![x] v) → ∃ z, φ.Eval ![z] v ∧ ∀ x < z, ¬φ.Eval ![x] v by
    simpa [models_iff, Semiformula.eval_univCl, leastNumber, Semiformula.eval_substs,
      Matrix.constant_eq_singleton] using this;
  intro v ⟨x, hx⟩;
  exact InductionOnHierarchy.least_number 𝚺 n (definablePred_of_hierarchy hφ v) hx;

instance models_LPi_of_ISigma [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 n] : V↓[ℒₒᵣ] ⊧* 𝗟𝚷 n := by
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory ‹V↓[ℒₒᵣ] ⊧* 𝗜𝚺 n›;
  suffices V↓[ℒₒᵣ] ⊧* LeastNumberScheme (Hierarchy 𝚷 n) by
    simpa [LPi, LeastNumberOnHierarchy, Semantics.ModelsSet.union_iff] using ⟨‹_›, this⟩;
  simp only [LeastNumberScheme];
  refine Semantics.ModelsSet.setOf_iff.mpr ?_;
  rintro _ ⟨φ, hφ, rfl⟩;
  suffices ∀ v : ℕ → V, (∃ x, φ.Eval ![x] v) → ∃ z, φ.Eval ![z] v ∧ ∀ x < z, ¬φ.Eval ![x] v by
    simpa [models_iff, Semiformula.eval_univCl, leastNumber, Semiformula.eval_substs,
      Matrix.constant_eq_singleton] using this;
  intro v ⟨x, hx⟩;
  exact InductionOnHierarchy.least_number 𝚷 n (definablePred_of_hierarchy hφ v) hx;

instance models_IPi_of_LSigma [V↓[ℒₒᵣ] ⊧* 𝗟𝚺 n] : V↓[ℒₒᵣ] ⊧* 𝗜𝚷 n := by
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory ‹V↓[ℒₒᵣ] ⊧* 𝗟𝚺 n›;
  suffices V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ (Hierarchy 𝚷 n) by
    simpa [IPi, InductionOnHierarchy, Semantics.ModelsSet.union_iff] using ⟨‹_›, this⟩;
  simp only [InductionScheme];
  refine Semantics.ModelsSet.setOf_iff.mpr ?_;
  rintro _ ⟨φ, hφ, rfl⟩;
  suffices ∀ v : ℕ → V, φ.Eval ![0] v → (∀ x, φ.Eval ![x] v → φ.Eval ![x + 1] v) →
      ∀ x, φ.Eval ![x] v by
    simpa [models_iff, Semiformula.eval_univCl, succInd, Semiformula.eval_substs,
      Matrix.constant_eq_singleton] using this;
  intro v;
  exact LeastNumberOnHierarchy.succ_induction 𝚺 n (definablePred_of_hierarchy hφ v);

instance models_ISigma_of_LPi [V↓[ℒₒᵣ] ⊧* 𝗟𝚷 n] : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 n := by
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory ‹V↓[ℒₒᵣ] ⊧* 𝗟𝚷 n›;
  suffices V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ (Hierarchy 𝚺 n) by
    simpa [ISigma, InductionOnHierarchy, Semantics.ModelsSet.union_iff] using ⟨‹_›, this⟩;
  simp only [InductionScheme];
  refine Semantics.ModelsSet.setOf_iff.mpr ?_;
  rintro _ ⟨φ, hφ, rfl⟩;
  suffices ∀ v : ℕ → V, φ.Eval ![0] v → (∀ x, φ.Eval ![x] v → φ.Eval ![x + 1] v) →
      ∀ x, φ.Eval ![x] v by
    simpa [models_iff, Semiformula.eval_univCl, succInd, Semiformula.eval_substs,
      Matrix.constant_eq_singleton] using this;
  intro v;
  exact LeastNumberOnHierarchy.succ_induction 𝚷 n (definablePred_of_hierarchy hφ v);

end models

section theorems

theorem ISigma_equiv_IPi (n : ℕ) : 𝗜𝚺 n ≊ 𝗜𝚷 n := Equiv.antisymm_iff.mpr ⟨
  weakerThan_of_models.{0} _ _ fun _ _ _ ↦ inferInstance,
  weakerThan_of_models.{0} _ _ fun _ _ _ ↦ inferInstance
⟩

theorem LSigma_equiv_ISigma (n : ℕ) : 𝗟𝚺 n ≊ 𝗜𝚺 n := Equiv.antisymm_iff.mpr ⟨
  weakerThan_of_models.{0} _ _ fun _ _ _ ↦ inferInstance,
  weakerThan_of_models.{0} _ _ fun _ _ _ ↦ inferInstance
⟩

theorem LPi_equiv_ISigma (n : ℕ) : 𝗟𝚷 n ≊ 𝗜𝚺 n := Equiv.antisymm_iff.mpr ⟨
  weakerThan_of_models.{0} _ _ fun _ _ _ ↦ inferInstance,
  weakerThan_of_models.{0} _ _ fun _ _ _ ↦ inferInstance
⟩

end theorems

end FFL.FirstOrder.Arithmetic
