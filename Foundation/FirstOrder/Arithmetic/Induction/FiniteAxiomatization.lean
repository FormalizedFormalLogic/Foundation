module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.PartialTruth.Disquotation
public import Foundation.FirstOrder.Arithmetic.Induction.Equiv

/-!
# Finite axiomatizability of `𝗜𝚺 n`

`𝗣𝗔⁻` together with the finite theory `tarski`, a single instance of the $\Sigma_{n + 1}$
induction scheme and a single instance of the $\Sigma_{n + 1}$ collection scheme, both stated with
the partial satisfaction `hierarchicalSatisfactionDef 𝚺 (n + 1)`, is a finite theory equivalent to
`𝗜𝚺 (n + 1)`; hence `𝗜𝚺 n` is finitely axiomatizable for `n ≥ 1`.

## References

- [HP98, Theorem I.2.52]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open Bootstrapping
open _root_.FFL.Entailment

namespace ISigma

variable {n : ℕ}

noncomputable def indFormula (n : ℕ) : ArithmeticSemiformula ℕ 1 :=
  “x. ∃ ev, !adjoinDef.val ev x &1 ∧ !(hierarchicalSatisfactionDef 𝚺 (n + 1)) &0 ev”

@[simp]
lemma hierarchy_indFormula : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 (n + 1) (indFormula n) := by
  simp [indFormula, hierarchicalSatisfactionDef, hierarchicalSatisfaction,
    (hierarchicalSatisfaction' 𝚺 n).sigma_prop]

noncomputable def indSentence (n : ℕ) : ArithmeticSentence := .univCl (succInd (indFormula n))

noncomputable def collFormula (n : ℕ) : ArithmeticSemiformula ℕ 2 :=
  “x y. ∃ ev₀, !adjoinDef.val ev₀ x &1 ∧
    ∃ ev, !adjoinDef.val ev y ev₀ ∧ !(hierarchicalSatisfactionDef 𝚺 (n + 1)) &0 ev”

@[simp]
lemma hierarchy_collFormula : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 (n + 1) (collFormula n) := by
  simp [collFormula, hierarchicalSatisfactionDef, hierarchicalSatisfaction,
    (hierarchicalSatisfaction' 𝚺 n).sigma_prop]

noncomputable def collSentence (n : ℕ) : ArithmeticSentence :=
  .univCl (collectionAxiom (collFormula n))

noncomputable def finiteAxiomatization (n : ℕ) : ArithmeticTheory :=
  𝗣𝗔⁻ ∪ tarski ∪ {indSentence n, collSentence n}

@[simp]
lemma finiteAxiomatization_finite : (finiteAxiomatization n).Finite :=
  (PeanoMinus.finite.union tarski_finite).union ((Set.finite_singleton _).insert _)

@[simp]
lemma peanoMinus_subset_finiteAxiomatization : 𝗣𝗔⁻ ⊆ finiteAxiomatization n :=
  Set.subset_union_left.trans Set.subset_union_left

lemma tarski_mem_finiteAxiomatization {σ : ArithmeticSentence} (h : σ ∈ tarski) :
    σ ∈ finiteAxiomatization n := Set.mem_union_left _ (Set.mem_union_right _ h)

@[simp]
lemma indSentence_mem_finiteAxiomatization : indSentence n ∈ finiteAxiomatization n :=
  Set.mem_union_right _ (Set.mem_insert _ _)

@[simp]
lemma collSentence_mem_finiteAxiomatization : collSentence n ∈ finiteAxiomatization n :=
  Set.mem_union_right _ (Set.mem_insert_of_mem _ rfl)

instance : 𝗘𝗤 ℒₒᵣ ⪯ finiteAxiomatization n :=
  WeakerThan.trans (𝓣 := 𝗣𝗔⁻) inferInstance
    (Axiomatized.le_of_subset peanoMinus_subset_finiteAxiomatization)

section eval

variable {M : Type*} [ORingStructure M]

@[simp]
lemma eval_indFormula (x : M) (g : ℕ → M) :
    (indFormula n).Eval ![x] g ↔
      ∃ ev, Reading.Adjoin ev x (g 1) ∧ Reading.HierarchicalSatisfaction 𝚺 (n + 1) (g 0) ev := by
  simp [indFormula, Reading.Adjoin, Reading.HierarchicalSatisfaction]

@[simp]
lemma eval_collFormula (x y : M) (g : ℕ → M) :
    (collFormula n).Eval ![x, y] g ↔ ∃ ev₀, Reading.Adjoin ev₀ x (g 1) ∧
        ∃ ev, Reading.Adjoin ev y ev₀ ∧ Reading.HierarchicalSatisfaction 𝚺 (n + 1) (g 0) ev := by
  simp [collFormula, Reading.Adjoin, Reading.HierarchicalSatisfaction]

end eval

theorem provable_finiteAxiomatization (n : ℕ) : 𝗜𝚺 (n + 1) ⊢* finiteAxiomatization n := by
  rintro σ ((hσ | hσ) | rfl | rfl)
  · exact by_axm (Set.mem_union_left _ hσ)
  · exact WeakerThan.pbl (h := ISigma_weakerThan_of_le (by omega)) (ISigma1.provable_tarski hσ)
  · exact WeakerThan.pbl (h := InductionOnBroadHierarchy_weakerThan_InductionOnHierarchy 𝚺 (n + 1))
      (by_axm (Set.mem_union_right _ (mem_InductionScheme_of_mem hierarchy_indFormula)))
  · have h : 𝗕⁺ 𝚺 (n + 1) ⪯ 𝗜𝚺 (n + 1) := weakerThan_of_models.{0} _ _ fun _ _ _ ↦ inferInstance
    exact WeakerThan.pbl (h := h)
      (by_axm (Set.mem_union_right _ (mem_CollectionScheme_of_mem hierarchy_collFormula)))

section models

open Reading

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* finiteAxiomatization n]

include n in
lemma models_peanoMinus : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ :=
  Semantics.ModelsSet.of_subset' (peanoMinus_subset_finiteAxiomatization (n := n))

include n in
lemma models_tarski : ∀ σ ∈ tarski, M↓[ℒₒᵣ] ⊧ σ := fun _ hσ ↦
  Semantics.ModelsSet.models _ (tarski_mem_finiteAxiomatization (n := n) hσ)

private lemma exists_assignment_eval_indFormula (φ : Prenex 𝚺 (n + 1) ℕ 1) (f : ℕ → M) :
    ∃ g : ℕ → M, ∀ x : M, (indFormula n).Eval ![x] g ↔ φ.val.Eval ![x] f := by
  have := models_peanoMinus (n := n) (M := M);
  have hM := models_tarski (n := n) (M := M);
  set ψ := φ.rew (φ.val.paramSubst ![#0]);
  obtain ⟨e₀, he₀⟩ := exists_codes hM (fun i : Fin φ.val.fvSup ↦ f i);
  use ((⌜ψ.matrix.val⌝ : ℕ) : M) :>ₙ fun _ ↦ e₀;
  intro x;
  have H {ev : M} (hadj : Adjoin ev x e₀) :=
    hierarchicalSatisfaction_quote_reading hM (Γ := 𝚺) ψ.matrix.bounded _ ev
      (codes_cons hM he₀ hadj);
  have hψ : M ⊧/(x :> fun i : Fin φ.val.fvSup ↦ f i) ψ.val ↔ φ.val.Eval ![x] f := by
    simp only [ψ, Prenex.val_rew];
    exact Semiformula.eval_toSemisentence_one φ.val x f;
  simp only [eval_indFormula, Nat.cases_zero, Nat.cases_succ];
  constructor;
  · rintro ⟨ev, hadj, hsat⟩;
    exact hψ.mp ((H hadj).mp hsat);
  · intro h;
    obtain ⟨ev, hadj⟩ := read_adjoinTotal hM x e₀;
    exact ⟨ev, hadj, (H hadj).mpr (hψ.mpr h)⟩;

private lemma exists_assignment_eval_collFormula (φ : Prenex 𝚺 (n + 1) ℕ 2) (f : ℕ → M) :
    ∃ g : ℕ → M, ∀ x y : M, (collFormula n).Eval ![x, y] g ↔ φ.val.Eval ![x, y] f := by
  have := models_peanoMinus (n := n) (M := M);
  have hM := models_tarski (n := n) (M := M);
  set ψ := φ.rew (φ.val.paramSubst ![#1, #0]);
  obtain ⟨e₀, he₀⟩ := exists_codes hM (fun i : Fin φ.val.fvSup ↦ f i);
  use ((⌜ψ.matrix.val⌝ : ℕ) : M) :>ₙ fun _ ↦ e₀;
  intro x y;
  have H {ev₀ ev : M} (hadj₀ : Adjoin ev₀ x e₀) (hadj : Adjoin ev y ev₀) :=
    hierarchicalSatisfaction_quote_reading hM (Γ := 𝚺) ψ.matrix.bounded _ ev
      (codes_cons hM (codes_cons hM he₀ hadj₀) hadj);
  have hψ : M ⊧/(y :> x :> fun i : Fin φ.val.fvSup ↦ f i) ψ.val ↔ φ.val.Eval ![x, y] f := by
    simp only [ψ, Prenex.val_rew];
    exact Semiformula.eval_toSemisentence_two φ.val x y f;
  simp only [eval_collFormula, Nat.cases_zero, Nat.cases_succ];
  constructor;
  · rintro ⟨ev₀, hadj₀, ev, hadj, hsat⟩;
    exact hψ.mp ((H hadj₀ hadj).mp hsat);
  · intro h;
    obtain ⟨ev₀, hadj₀⟩ := read_adjoinTotal hM x e₀;
    obtain ⟨ev, hadj⟩ := read_adjoinTotal hM y ev₀;
    exact ⟨ev₀, hadj₀, ev, hadj, (H hadj₀ hadj).mpr (hψ.mpr h)⟩;

lemma succ_induction_prenex (φ : Prenex 𝚺 (n + 1) ℕ 1) (f : ℕ → M) (zero : φ.val.Eval ![0] f)
    (succ : ∀ x, φ.val.Eval ![x] f → φ.val.Eval ![x + 1] f) : ∀ x, φ.val.Eval ![x] f := by
  have hInd : M↓[ℒₒᵣ] ⊧ indSentence n :=
    Semantics.ModelsSet.models _ indSentence_mem_finiteAxiomatization;
  have hind : ∀ g : ℕ → M, (indFormula n).Eval ![0] g →
      (∀ x, (indFormula n).Eval ![x] g → (indFormula n).Eval ![x + 1] g) →
      ∀ x, (indFormula n).Eval ![x] g := by
    simpa [indSentence, models_iff, Semiformula.eval_univCl, succInd, Semiformula.eval_substs,
      Matrix.constant_eq_singleton, -eval_indFormula] using hInd;
  obtain ⟨g, hg⟩ := exists_assignment_eval_indFormula φ f;
  intro x;
  exact (hg x).mp <|
    hind g ((hg 0).mpr zero) (fun y hy ↦ (hg (y + 1)).mpr (succ y ((hg y).mp hy))) x;

lemma collection_prenex (φ : Prenex 𝚺 (n + 1) ℕ 2) (f : ℕ → M) (a : M)
    (h : ∀ x < a, ∃ y, φ.val.Eval ![x, y] f) : ∃ b, ∀ x < a, ∃ y < b, φ.val.Eval ![x, y] f := by
  have hColl : M↓[ℒₒᵣ] ⊧ collSentence n :=
    Semantics.ModelsSet.models _ collSentence_mem_finiteAxiomatization;
  obtain ⟨g, hg⟩ := exists_assignment_eval_collFormula φ f;
  obtain ⟨b, hb⟩ := (models_collectionAxiom_iff (collFormula n)).mp hColl g a
    fun x hx ↦ (h x hx).imp fun y hy ↦ (hg x y).mpr hy;
  use b;
  intro x hx;
  obtain ⟨y, hyb, hy⟩ := hb x hx;
  exact ⟨y, hyb, (hg x y).mp hy⟩;

private lemma models_IBroadSigma_of {s : ℕ}
    (H : ∀ φ : ArithmeticSemiformula ℕ 1, ℬ[<, ℒₒᵣ].Hierarchy 𝚺 s φ →
      ∃ φ' : Prenex 𝚺 (n + 1) ℕ 1, ∀ (e : Fin 1 → M) (f : ℕ → M),
        φ'.val.Eval e f ↔ φ.Eval e f) :
    M↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺ s := by
  have hPA := models_peanoMinus (n := n) (M := M);
  suffices M↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ (ℬ[<, ℒₒᵣ].Hierarchy 𝚺 s) by
    simpa [InductionOnBroadHierarchy, Semantics.ModelsSet.union_iff] using ⟨hPA, this⟩;
  apply Semantics.ModelsSet.setOf_iff.mpr;
  rintro _ ⟨φ, hφ, rfl⟩;
  suffices ∀ f : ℕ → M, φ.Eval ![0] f → (∀ x, φ.Eval ![x] f → φ.Eval ![x + 1] f) →
      ∀ x, φ.Eval ![x] f by
    simpa [models_iff, Semiformula.eval_univCl, succInd, Semiformula.eval_substs,
      Matrix.constant_eq_singleton] using this;
  intro f;
  obtain ⟨φ', hφ'⟩ := H φ hφ;
  simpa only [hφ'] using succ_induction_prenex φ' f;

private lemma models_CollectionOnBroadHierarchy_of [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀] {Γ : Polarity} {s : ℕ}
    (H : ∀ φ : ArithmeticSemiformula ℕ 2, ℬ[<, ℒₒᵣ].Hierarchy Γ s φ →
      ∃ φ' : Prenex 𝚺 (n + 1) ℕ 2, ∀ (e : Fin 2 → M) (f : ℕ → M),
        φ'.val.Eval e f ↔ φ.Eval e f) :
    M↓[ℒₒᵣ] ⊧* 𝗕⁺ Γ s := by
  apply Semantics.ModelsSet.union_iff.mpr;
  and_intros;
  · assumption;
  · apply Semantics.ModelsSet.setOf_iff.mpr;
    rintro _ ⟨φ, hφ, rfl⟩;
    apply (models_collectionAxiom_iff φ).mpr;
    intro f;
    obtain ⟨φ', hφ'⟩ := H φ hφ;
    simpa only [hφ'] using collection_prenex φ' f;

omit [M↓[ℒₒᵣ] ⊧* finiteAxiomatization n] in
private lemma exists_prenex_of_zero {k : ℕ} {Γ : Polarity} {φ : ArithmeticSemiformula ℕ k}
    (hφ : ℬ[<, ℒₒᵣ].Hierarchy Γ 0 φ) :
    ∃ φ' : Prenex 𝚺 (n + 1) ℕ k, ∀ (e : Fin k → M) (f : ℕ → M), φ'.val.Eval e f ↔ φ.Eval e f :=
  ⟨.ofΔ₀ ⟨φ, Bounding.Hierarchy.zero_iff_bounded.mp hφ⟩ 𝚺 (n + 1), fun e _ ↦
    Prenex.models_ofΔ₀ _ e⟩

include n in
private lemma models_ISigmaZero : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ :=
  have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺ 0 := models_IBroadSigma_of (n := n) fun _ hφ ↦ exists_prenex_of_zero hφ
  inferInstance

private lemma models_BPi : ∀ j ≤ n, M↓[ℒₒᵣ] ⊧* 𝗕𝚷 j := by
  have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := models_ISigmaZero (n := n);
  intro j hj;
  induction j with
  | zero =>
    exact models_of_ss
      (models_CollectionOnBroadHierarchy_of (n := n) fun _ hφ ↦ exists_prenex_of_zero hφ)
      CollectionOnHierarchy_subset_CollectionOnBroadHierarchy;
  | succ j ih =>
    have : M↓[ℒₒᵣ] ⊧* 𝗕𝚷 j := ih (by omega);
    apply models_of_ss (models_CollectionOnBroadHierarchy_of (n := n) ?_)
      CollectionOnHierarchy_subset_CollectionOnBroadHierarchy;
    intro φ hφ;
    obtain ⟨φ₁, h₁⟩ := Prenex.models_exists_prenex (Γ' := 𝚺) hφ;
    obtain ⟨φ₂, h₂⟩ := Prenex.exists_models_iff_of_le (V := M) (s' := n + 1) (by omega) φ₁.altUp;
    exact ⟨φ₂, fun e f ↦ (h₂ e f).trans ((Prenex.models_altUp φ₁ e).trans (h₁ M e f).symm)⟩;

lemma models_ISigma : M↓[ℒₒᵣ] ⊧* 𝗜𝚺 (n + 1) := by
  have : M↓[ℒₒᵣ] ⊧* 𝗕𝚷 n := models_BPi n le_rfl;
  have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺ (n + 1) := models_IBroadSigma_of fun φ hφ ↦ by
    obtain ⟨φ', hφ'⟩ := Prenex.models_exists_prenex (Γ' := 𝚺) hφ;
    exact ⟨φ', fun e f ↦ (hφ' M e f).symm⟩;
  infer_instance

end models

theorem finiteAxiomatization_equiv (n : ℕ) : finiteAxiomatization n ≊ 𝗜𝚺 (n + 1) :=
  Equiv.antisymm ⟨WeakerThan.ofAxm! (provable_finiteAxiomatization n),
    weakerThan_of_models.{0} _ _ fun _ _ _ ↦ models_ISigma⟩

theorem finiteAxiomatizable (hn : 1 ≤ n) : FiniteAxiomatizable (𝗜𝚺 n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn;
  exact ⟨finiteAxiomatization m, by simp, finiteAxiomatization_equiv m⟩

end ISigma

end FFL.FirstOrder.Arithmetic
