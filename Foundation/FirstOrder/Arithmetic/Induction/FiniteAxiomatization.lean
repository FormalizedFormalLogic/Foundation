module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.PartialTruth.Disquotation

/-!
# Finite axiomatizability of `𝗜𝚺 n`

`𝗣𝗔⁻` together with the finite theory `tarski` and a single instance of the $\Sigma_{n + 1}$
induction scheme stated with the partial satisfaction `prenexSatisfied 𝚺 (n + 1)` is a finite
theory equivalent to `𝗜𝚺 (n + 1)`; hence `𝗜𝚺 n` is finitely axiomatizable for `n ≥ 1`.

## References

- [HP98]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open Bootstrapping
open _root_.FFL.Entailment

namespace ISigma

variable {n : ℕ}

noncomputable def indFormula (n : ℕ) : ArithmeticSemiformula ℕ 1 :=
  “x. ∃ ev, !adjoinDef.val ev x &1 ∧ !(prenexSatisfied' 𝚺 n).val ev &0”

@[simp]
lemma hierarchy_indFormula : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 (n + 1) (indFormula n) := by
  simp [indFormula, (prenexSatisfied' 𝚺 n).sigma_prop]

noncomputable def indSentence (n : ℕ) : ArithmeticSentence := .univCl (succInd (indFormula n))

noncomputable def finiteAxiomatization (n : ℕ) : ArithmeticTheory :=
  𝗣𝗔⁻ ∪ tarski ∪ {indSentence n}

@[simp]
lemma finiteAxiomatization_finite : (finiteAxiomatization n).Finite :=
  (PeanoMinus.finite.union tarski_finite).union (Set.finite_singleton _)

@[simp]
lemma peanoMinus_subset_finiteAxiomatization : 𝗣𝗔⁻ ⊆ finiteAxiomatization n :=
  Set.subset_union_left.trans Set.subset_union_left

lemma tarski_mem_finiteAxiomatization {σ : ArithmeticSentence} (h : σ ∈ tarski) :
    σ ∈ finiteAxiomatization n := Set.mem_union_left _ (Set.mem_union_right _ h)

@[simp]
lemma indSentence_mem_finiteAxiomatization : indSentence n ∈ finiteAxiomatization n :=
  Set.mem_union_right _ rfl

instance : 𝗘𝗤 ℒₒᵣ ⪯ finiteAxiomatization n :=
  WeakerThan.trans (𝓣 := 𝗣𝗔⁻) inferInstance
    (Axiomatized.le_of_subset peanoMinus_subset_finiteAxiomatization)

section eval

variable {V : Type*} [ORingStructure V]

@[simp]
lemma eval_indFormula (x : V) (g : ℕ → V) :
    (indFormula n).Eval ![x] g ↔
      ∃ ev, Reading.Adjoin ev x (g 1) ∧ Reading.PrenexSatisfied 𝚺 (n + 1) ev (g 0) := by
  simp [indFormula, Reading.Adjoin, Reading.PrenexSatisfied]

private lemma models_succInd_iff (φ : ArithmeticSemiformula ℕ 1) :
    V↓[ℒₒᵣ] ⊧ .univCl (succInd φ) ↔ ∀ f : ℕ → V, φ.Eval ![0] f →
      (∀ x, φ.Eval ![x] f → φ.Eval ![x + 1] f) → ∀ x, φ.Eval ![x] f := by
  simp [models_iff, Semiformula.eval_univCl, succInd, Semiformula.eval_substs]

end eval

theorem provable_finiteAxiomatization (n : ℕ) : 𝗜𝚺 (n + 1) ⊢* finiteAxiomatization n := by
  rintro σ ((hσ | hσ) | rfl);
  · exact by_axm (Set.mem_union_left _ hσ);
  · exact WeakerThan.pbl (h := ISigma_weakerThan_of_le (by omega)) (ISigma1.provable_tarski hσ);
  · exact WeakerThan.pbl (h := InductionOnHierarchy_weakerThan_InductionOnPrenexHierarchy 𝚺 (n + 1))
      (by_axm (Set.mem_union_right _ (mem_InductionScheme_of_mem hierarchy_indFormula)));

section models

open Reading

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* finiteAxiomatization n]

include n in
lemma models_peanoMinus : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ :=
  Semantics.ModelsSet.of_subset' (peanoMinus_subset_finiteAxiomatization (n := n))

include n in
lemma models_tarski : ∀ σ ∈ tarski, V↓[ℒₒᵣ] ⊧ σ := fun _ hσ ↦
  Semantics.ModelsSet.models _ (tarski_mem_finiteAxiomatization (n := n) hσ)

private lemma exists_assignment_eval_indFormula (φ : ℬ[<, ℒₒᵣ].Prenex 𝚺 (n + 1) ℕ 1)
    (f : ℕ → V) :
    ∃ g : ℕ → V, ∀ x : V, (indFormula n).Eval ![x] g ↔ φ.val.Eval ![x] f := by
  have := models_peanoMinus (n := n) (V := V);
  have hV := models_tarski (n := n) (V := V);
  set ψ := φ.rew (φ.val.paramSubst ![#0]);
  obtain ⟨e₀, he₀⟩ := exists_codes hV (fun i : Fin φ.val.fvSup ↦ f i);
  use ((⌜ψ.matrix.val⌝ : ℕ) : V) :>ₙ fun _ ↦ e₀;
  intro x;
  have hψ : V ⊧/(x :> fun i : Fin φ.val.fvSup ↦ f i) ψ.val ↔ φ.val.Eval ![x] f :=
    (φ.val_rew _).symm ▸ Semiformula.eval_toSemisentence_one φ.val x f;
  have H {ev : V} (hadj : Adjoin ev x e₀) :=
    (prenexSatisfied_quote_reading hV (Γ := 𝚺) ψ.matrix.bounded _ ev
      (codes_cons hV he₀ hadj)).trans hψ;
  apply (eval_indFormula x _).trans;
  constructor;
  · rintro ⟨ev, hadj, hsat⟩;
    exact (H hadj).mp hsat;
  · intro h;
    obtain ⟨ev, hadj⟩ := read_adjoinTotal hV x e₀;
    exact ⟨ev, hadj, (H hadj).mpr h⟩;

lemma models_ISigma : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 (n + 1) := by
  apply Semantics.ModelsSet.union_iff.mpr;
  and_intros;
  · exact models_peanoMinus (n := n);
  · apply Semantics.ModelsSet.setOf_iff.mpr;
    rintro _ ⟨_, ⟨φ, rfl⟩, rfl⟩;
    apply (models_succInd_iff _).mpr;
    intro f zero succ x;
    have hInd : V↓[ℒₒᵣ] ⊧ indSentence n :=
      Semantics.ModelsSet.models _ indSentence_mem_finiteAxiomatization;
    obtain ⟨g, hg⟩ := exists_assignment_eval_indFormula φ f;
    exact (hg x).mp <| (models_succInd_iff _).mp hInd g ((hg 0).mpr zero)
      (fun y hy ↦ (hg (y + 1)).mpr (succ y ((hg y).mp hy))) x;

end models

theorem finiteAxiomatization_equiv (n : ℕ) : finiteAxiomatization n ≊ 𝗜𝚺 (n + 1) :=
  Equiv.antisymm ⟨WeakerThan.ofAxm! (provable_finiteAxiomatization n),
    weakerThan_of_models.{0} _ _ fun _ _ _ ↦ models_ISigma⟩

theorem finiteAxiomatizable (hn : 1 ≤ n) : FiniteAxiomatizable (𝗜𝚺 n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn;
  exact ⟨finiteAxiomatization m, by simp, finiteAxiomatization_equiv m⟩;

end ISigma

end FFL.FirstOrder.Arithmetic
