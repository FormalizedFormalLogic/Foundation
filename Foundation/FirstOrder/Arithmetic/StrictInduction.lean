module

public import Foundation.FirstOrder.Arithmetic.Collection.Equiv
public import Foundation.FirstOrder.Arithmetic.LeastNumber.Basic

/-!
# Induction over the strict and the broad hierarchy agree

Induction for the strict hierarchy proves collection, and collection turns every formula of the
broad class into a strict one, so `𝗜𝗡𝗗 Γ s` and `𝗜𝗡𝗗⁺ Γ s` are the same theory. The least number
schemata collapse the same way.

## References

- [HP98, Theorem I.2.4, Lemma I.2.9, Lemma I.2.11, Lemma I.2.12(2)]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open _root_.FFL.Entailment

variable {V : Type*} [ORingStructure V] {Γ : Polarity} {s k : ℕ}
         {P : V → Prop} {Q R : V → V → Prop}

/-! ### Strict definitions of definable relations -/

/-- Every `Γ-[s]`-definable relation on `V` is definable by a strict `Γ-[s]` formula. -/
def StrictlyDefinable (V : Type*) [ORingStructure V] (s : ℕ) : Prop :=
  ∀ {Γ : Polarity} {R : V → V → Prop}, Γ-[s].DefinableRel R → StrictDefinableRel Γ s R

/-- - [HP98, Lemma I.2.9] -/
lemma strictlyDefinable_of_models_IBroadSigma (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺s] :
    StrictlyDefinable V s := by
  rcases s with _ | t;
  . rintro Γ R ⟨φ, hφ⟩;
    exact ⟨φ.val, StrictHierarchy.zero_iff.mpr (Hierarchy.zero_iff.mp φ.polarity_prop),
      fun v ↦ hφ.iff⟩;
  . intro Γ R hR;
    have : V↓[ℒₒᵣ] ⊧* 𝗕𝚺 (t + 1) := IBroadSigma.models_BSigma_succ;
    exact StrictDefinable.of_definable (Γ' := 𝚺) hR;

lemma models_ISigmaZero_of_models_InductionOnHierarchy (V : Type*) [ORingStructure V]
    (Γ : Polarity) (s : ℕ) [V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗 Γ s] : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ :=
  models_of_ss inferInstance (ISigmaZero_subset_InductionOnHierarchy Γ s)

/-! ### Successor induction over the strict hierarchy -/

/-- The existential quantification of a `𝚷-[s]`-definable relation is defined by a strict
`𝚺-[s + 1]` formula. -/
private lemma exists_strictHierarchy_sigma_eval (hD : StrictlyDefinable V s)
    (hQ : 𝚷-[s].DefinableRel Q) (hPQ : ∀ x, P x ↔ ∃ w, Q x w) :
    ∃ (φ : ArithmeticSemiformula ℕ 1) (f : ℕ → V),
      StrictHierarchy 𝚺 (s + 1) φ ∧ ∀ x, P x ↔ φ.Eval ![x] f := by
  obtain ⟨f, χ, hχ, hiff⟩ := (hD (Γ := 𝚷) hQ).exists_eval_iff;
  refine ⟨∃¹ (χ ⇜ ![#1, #0]), f, (StrictHierarchy.ofAlt (Γ := 𝚺) (hχ.rew _)).exs, fun x ↦ ?_⟩;
  rw [hPQ x, Semiformula.eval_ex];
  refine exists_congr fun w ↦
    Iff.trans (show Q x w ↔ χ.Eval ![x, w] f by simpa using hiff ![x, w]) ?_;
  simp [Semiformula.eval_substs];

/-- The universal quantification of a `𝚺-[s]`-definable relation is defined by a strict
`𝚷-[s + 1]` formula. -/
private lemma exists_strictHierarchy_pi_eval (hD : StrictlyDefinable V s)
    (hQ : 𝚺-[s].DefinableRel Q) (hPQ : ∀ x, P x ↔ ∀ w, Q x w) :
    ∃ (φ : ArithmeticSemiformula ℕ 1) (f : ℕ → V),
      StrictHierarchy 𝚷 (s + 1) φ ∧ ∀ x, P x ↔ φ.Eval ![x] f := by
  obtain ⟨f, χ, hχ, hiff⟩ := (hD (Γ := 𝚺) hQ).exists_eval_iff;
  refine ⟨∀¹ (χ ⇜ ![#1, #0]), f, (StrictHierarchy.ofAlt (Γ := 𝚷) (hχ.rew _)).all, fun x ↦ ?_⟩;
  rw [hPQ x, Semiformula.eval_all];
  refine forall_congr' fun w ↦
    Iff.trans (show Q x w ↔ χ.Eval ![x, w] f by simpa using hiff ![x, w]) ?_;
  simp [Semiformula.eval_substs];

private lemma succ_induction_exists_pi_of_sigma [V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗 𝚺 (s + 1)]
    (hD : StrictlyDefinable V s) (hQ : 𝚷-[s].DefinableRel Q) (hPQ : ∀ x, P x ↔ ∃ w, Q x w)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x :=
  have ⟨φ, f, hφ, hiff⟩ := exists_strictHierarchy_sigma_eval hD hQ hPQ
  InductionScheme.succ_induction (C := Arithmetic.StrictHierarchy 𝚺 (s + 1))
    ⟨f, φ, hφ, hiff⟩ zero succ

lemma succ_induction_forall_sigma [V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗 𝚷 (s + 1)] (hD : StrictlyDefinable V s)
    (hQ : 𝚺-[s].DefinableRel Q) (hPQ : ∀ x, P x ↔ ∀ w, Q x w)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x :=
  have ⟨φ, f, hφ, hiff⟩ := exists_strictHierarchy_pi_eval hD hQ hPQ
  InductionScheme.succ_induction (C := Arithmetic.StrictHierarchy 𝚷 (s + 1))
    ⟨f, φ, hφ, hiff⟩ zero succ

/-- - [HP98, Lemma I.2.12(2)] -/
private lemma neg_succ_induction [V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗 𝚷 (s + 1)] (hD : StrictlyDefinable V s)
    (hQ : 𝚺-[s].DefinableRel Q) (hPQ : ∀ x, P x ↔ ∀ w, Q x w)
    (nzero : ¬P 0) (nsucc : ∀ x, ¬P x → ¬P (x + 1)) : ∀ x, ¬P x := by
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ :=
    models_of_ss (U := 𝗜𝗡𝗗 𝚷 (s + 1)) inferInstance Set.subset_union_left;
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := models_ISigmaZero_of_models_InductionOnHierarchy V 𝚷 (s + 1);
  have : 𝚺-[s].DefinableRel Q := hQ;
  by_contra A;
  obtain ⟨a, ha⟩ : ∃ x, P x := by simpa using A;
  have key : ∀ x, x ≤ a → P (a - x) := by
    refine succ_induction_forall_sigma hD (P := fun x ↦ x ≤ a → P (a - x))
      (Q := fun x w ↦ x ≤ a → Q (a - x) w) ?_ ?_ ?_ ?_;
    . apply HierarchySymbol.Definable.imp;
      . apply HierarchySymbol.Definable.bcomp₂ (by definability) (by definability);
      . apply HierarchySymbol.Definable.bcomp₂ (by definability) (by definability);
    . intro x;
      rw [imp_congr_right fun _ ↦ hPQ (a - x)];
      exact imp_forall_iff;
    . intro _; simpa using ha;
    . intro x ih hx;
      have h : P (a - x) := ih (le_of_add_le_left hx);
      refine (not_imp_not.mp <| nsucc (a - (x + 1))) ?_;
      rw [← Arithmetic.sub_sub, sub_add_self_of_le];
      . exact h;
      . exact le_tsub_of_add_le_left hx;
  exact nzero (by simpa using key a le_rfl);

/-- - [HP98, Lemma I.2.12(2)] -/
private lemma succ_induction_exists_pi_of_pi [V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗 𝚷 (s + 1)]
    (hD : StrictlyDefinable V s) (hQ : 𝚷-[s].DefinableRel Q) (hPQ : ∀ x, P x ↔ ∃ w, Q x w)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x := by
  have h := neg_succ_induction (P := fun x ↦ ¬P x) (Q := fun x w ↦ ¬Q x w) hD
    (HierarchySymbol.Definable.not (Γ := 𝚺) hQ) (fun x ↦ by simp [hPQ x])
    (by simpa using zero) (fun x hx ↦ by simpa using succ x (by simpa using hx));
  intro x;
  simpa using h x;

lemma succ_induction_exists_pi (Γ : Polarity) [V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗 Γ (s + 1)]
    (hD : StrictlyDefinable V s) (hQ : 𝚷-[s].DefinableRel Q) (hPQ : ∀ x, P x ↔ ∃ w, Q x w)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x := by
  rcases Γ with _ | _;
  . exact succ_induction_exists_pi_of_sigma hD hQ hPQ zero succ;
  . exact succ_induction_exists_pi_of_pi hD hQ hPQ zero succ;

/-! ### Collection from induction over the strict hierarchy -/

/-- - [HP98, Lemma I.2.11] -/
lemma exists_bound_of_definable_pi (Γ : Polarity) [V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗 Γ (s + 1)]
    (hD : StrictlyDefinable V s) (hR : 𝚷-[s].DefinableRel R) (a : V)
    (h : ∀ x < a, ∃ u, R x u) : ∃ w, ∀ x < a, ∃ u ≤ w, R x u := by
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ :=
    models_of_ss (U := 𝗜𝗡𝗗 Γ (s + 1)) inferInstance Set.subset_union_left;
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := models_ISigmaZero_of_models_InductionOnHierarchy V Γ (s + 1);
  have hbdd : 𝚷-[s].DefinableRel fun y w ↦ ∀ x < y, x < a → ∃ u ≤ w, R x u := by
    have h₁ : 𝚷-[s].Definable fun w : Fin 4 → V ↦ R (w 1) (w 0) := hR.retraction ![1, 0];
    have h₂ : 𝚷-[s].Definable fun w : Fin 3 → V ↦ ∃ u ≤ w 2, R (w 0) u :=
      (HierarchySymbol.Definable.bexs' (P := fun v u ↦ R (v 0) u) h₁
        (#2 : ArithmeticSemiterm V 3)).of_iff (by intro w; simp);
    have hlt : 𝚺-[s].Definable fun w : Fin 3 → V ↦ w 0 < a :=
      HierarchySymbol.Definable.of_iff
        (HierarchySymbol.Definable.retractiont 3
          (inferInstance : 𝚺-[s].DefinableRel (LT.lt : V → V → Prop)) ![#0, &a])
        (by intro w; simp);
    have h₃ : 𝚷-[s].Definable fun w : Fin 3 → V ↦ w 0 < a → ∃ u ≤ w 2, R (w 0) u :=
      HierarchySymbol.Definable.imp hlt h₂;
    exact (HierarchySymbol.Definable.ball (P := fun v x ↦ x < a → ∃ u ≤ v 1, R x u) h₃
      (#0 : ArithmeticSemiterm V 2)).of_iff (by intro v; simp);
  have key : ∀ y : V, ∃ w, ∀ x < y, x < a → ∃ u ≤ w, R x u := by
    refine succ_induction_exists_pi Γ hD hbdd (fun _ ↦ Iff.rfl) ⟨0, by simp⟩ ?_;
    rintro y ⟨w, hw⟩;
    rcases lt_or_ge y a with hya | hya;
    . obtain ⟨u₀, hu₀⟩ := h y hya;
      refine ⟨max w u₀, ?_⟩;
      intro x hx _;
      rcases le_iff_lt_or_eq.mp (Arithmetic.lt_succ_iff_le.mp hx) with hx | rfl;
      . obtain ⟨u, hu, hu'⟩ := hw x hx (lt_trans hx hya);
        exact ⟨u, le_trans hu (le_max_left w u₀), hu'⟩;
      . exact ⟨u₀, le_max_right w u₀, hu₀⟩;
    . refine ⟨w, ?_⟩;
      intro x hx hxa;
      rcases le_iff_lt_or_eq.mp (Arithmetic.lt_succ_iff_le.mp hx) with hx | rfl;
      . exact hw x hx hxa;
      . exact absurd hxa (not_lt.mpr hya);
  obtain ⟨w, hw⟩ := key (a + 1);
  exact ⟨w, fun x hx ↦ hw x (lt_trans hx (lt_add_one a)) hx⟩;

/-- - [HP98, Lemma I.2.11] -/
lemma models_BPi_of_strictlyDefinable (Γ : Polarity) [V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗 Γ (s + 1)]
    (hD : StrictlyDefinable V s) : V↓[ℒₒᵣ] ⊧* 𝗕𝚷 s := by
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := models_ISigmaZero_of_models_InductionOnHierarchy V Γ (s + 1);
  apply Semantics.ModelsSet.union_iff.mpr;
  and_intros;
  . assumption;
  . refine models_of_ss (CollectionScheme.models_of_collection (Γ := 𝚷) ?_)
      (CollectionScheme_subset (·.hierarchy));
    intro R hR a h;
    obtain ⟨w, hw⟩ := exists_bound_of_definable_pi Γ hD hR a h;
    exact ⟨w + 1, fun x hx ↦ (hw x hx).imp fun u hu ↦
      ⟨Arithmetic.lt_succ_iff_le.mpr hu.1, hu.2⟩⟩;

/-! ### The two induction schemes agree -/

/-- - [HP98, Theorem I.2.4] -/
private lemma models_IBroadSigma_succ_of_strictlyDefinable (Γ : Polarity)
    [V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗 Γ (s + 1)] (hD : StrictlyDefinable V s) : V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺ (s + 1) := by
  have hPA : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ :=
    models_of_ss (U := 𝗜𝗡𝗗 Γ (s + 1)) inferInstance Set.subset_union_left;
  have : V↓[ℒₒᵣ] ⊧* 𝗕𝚷 s := models_BPi_of_strictlyDefinable Γ hD;
  suffices V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ (Hierarchy 𝚺 (s + 1)) by
    simpa [InductionOnBroadHierarchy, Semantics.ModelsSet.union_iff] using ⟨hPA, this⟩;
  simp only [InductionScheme];
  apply Semantics.ModelsSet.setOf_iff.mpr;
  rintro _ ⟨φ, hφ, rfl⟩;
  suffices ∀ f : ℕ → V, φ.Eval ![0] f → (∀ x, φ.Eval ![x] f → φ.Eval ![x + 1] f) →
      ∀ x, φ.Eval ![x] f by
    simpa [models_iff, Semiformula.eval_univCl, succInd, Semiformula.eval_substs,
      Matrix.constant_eq_singleton] using this;
  intro f;
  obtain ⟨Q, hQ, hiff⟩ := exists_pi_definableRel_iff (definablePred_of_hierarchy hφ f);
  exact succ_induction_exists_pi Γ hD hQ hiff;

private lemma models_IBroadSigma_of_models_InductionOnHierarchy_sigma :
    ∀ (s : ℕ) (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗 𝚺 s], V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺s := by
  intro s;
  induction s with
  | zero => intro V _ _; exact models_of_ss inferInstance IBroadSigmaZero_subset_ISigmaZero;
  | succ t ih =>
    intro V _ _;
    have : V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗 𝚺 t :=
      models_of_ss inferInstance (InductionOnHierarchy_subset_mono (Nat.le_succ t));
    have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺t := ih V;
    exact models_IBroadSigma_succ_of_strictlyDefinable 𝚺
      (strictlyDefinable_of_models_IBroadSigma V);

/-- Every model of `𝗜𝗡𝗗 Γ s` is a model of `𝗜𝚺⁺ s`.
- [HP98, Theorem I.2.4] -/
lemma models_IBroadSigma_of_models_InductionOnHierarchy (Γ : Polarity) (s : ℕ) (V : Type*)
    [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗 Γ s] : V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺s := by
  rcases s with _ | t;
  . exact models_of_ss inferInstance
      (IBroadSigmaZero_subset_ISigmaZero.trans (ISigmaZero_subset_InductionOnHierarchy Γ 0));
  . have : V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗 𝚺 t :=
      models_of_ss inferInstance (InductionOnHierarchy_subset_of_lt (Γ' := Γ) (Nat.lt_succ_self t));
    have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺t := models_IBroadSigma_of_models_InductionOnHierarchy_sigma t V;
    exact models_IBroadSigma_succ_of_strictlyDefinable Γ
      (strictlyDefinable_of_models_IBroadSigma V);

instance models_IBroadSigma_of_models_ISigma [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s] : V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺s :=
  models_IBroadSigma_of_models_InductionOnHierarchy 𝚺 s V

instance models_InductionOnBroadHierarchy_of_models_InductionOnHierarchy
    [V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗 Γ s] : V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗⁺ Γ s :=
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺s := models_IBroadSigma_of_models_InductionOnHierarchy Γ s V
  inferInstance

/-- Induction for the broad hierarchy follows from induction for the strict one.
- [HP98, Theorem I.2.4] -/
@[instance]
theorem InductionOnBroadHierarchy_weakerThan_InductionOnHierarchy (Γ : Polarity) (s : ℕ) :
    𝗜𝗡𝗗⁺ Γ s ⪯ 𝗜𝗡𝗗 Γ s :=
  weakerThan_of_models.{0} _ _ fun _ _ _ ↦ inferInstance

/-- - [HP98, Theorem I.2.4] -/
theorem InductionOnHierarchy_equiv_InductionOnBroadHierarchy (Γ : Polarity) (s : ℕ) :
    𝗜𝗡𝗗 Γ s ≊ 𝗜𝗡𝗗⁺ Γ s :=
  Equiv.antisymm_iff.mpr
    ⟨inferInstance, InductionOnBroadHierarchy_weakerThan_InductionOnHierarchy Γ s⟩

theorem ISigma_equiv_IBroadSigma (s : ℕ) : 𝗜𝚺 s ≊ 𝗜𝚺⁺ s :=
  InductionOnHierarchy_equiv_InductionOnBroadHierarchy 𝚺 s

theorem IPi_equiv_IBroadPi (s : ℕ) : 𝗜𝚷 s ≊ 𝗜𝚷⁺ s :=
  InductionOnHierarchy_equiv_InductionOnBroadHierarchy 𝚷 s

theorem ISigma_equiv_IPi (s : ℕ) : 𝗜𝚺 s ≊ 𝗜𝚷 s :=
  ((ISigma_equiv_IBroadSigma s).trans (IBroadSigma_equiv_IBroadPi s)).trans
    (IPi_equiv_IBroadPi s).symm

instance models_InductionOnHierarchy_of_models_ISigma [V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗 𝚺 s] :
    V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗 Γ s :=
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺s := models_IBroadSigma_of_models_InductionOnHierarchy 𝚺 s V
  models_of_ss (inferInstance : V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗⁺ Γ s)
    InductionOnHierarchy_subset_InductionOnBroadHierarchy

instance models_InductionOnHierarchy_of_models_IPi [V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗 𝚷 s] :
    V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗 Γ s :=
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺s := models_IBroadSigma_of_models_InductionOnHierarchy 𝚷 s V
  models_of_ss (inferInstance : V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗⁺ Γ s)
    InductionOnHierarchy_subset_InductionOnBroadHierarchy

/-! ### Collection below the strict induction schemata -/

@[instance]
theorem BSigma_weakerThan_ISigma : 𝗕𝚺 (s + 1) ⪯ 𝗜𝚺 (s + 1) :=
  WeakerThan.trans BSigma_weakerThan_IBroadSigma
    (InductionOnBroadHierarchy_weakerThan_InductionOnHierarchy 𝚺 (s + 1))

@[instance]
theorem BSigma_weakerThan_ISigma_succ : 𝗕𝚺 s ⪯ 𝗜𝚺 (s + 1) :=
  WeakerThan.trans (CollectionOnHierarchy_weakerThan_of_le (Nat.le_succ s)) BSigma_weakerThan_ISigma

@[instance]
theorem ISigma_weakerThan_BSigma_succ : 𝗜𝚺 s ⪯ 𝗕𝚺 (s + 1) :=
  WeakerThan.trans (InductionOnHierarchy_weakerThan_InductionOnBroadHierarchy 𝚺 s)
    IBroadSigma_weakerThan_BSigma_succ

/-! ### The least number schemata over the strict hierarchy -/

section leastNumber

/-- Successor induction from the least number principle: the negation of a strict `Γ.alt-[s]`
formula is strict `Γ-[s]`. -/
lemma LeastNumberOnHierarchy.succ_induction (Γ : Polarity) (s : ℕ) [V↓[ℒₒᵣ] ⊧* 𝗟 Γ s]
    {φ : ArithmeticSemiformula ℕ 1} (hφ : StrictHierarchy Γ.alt s φ) (f : ℕ → V)
    (zero : φ.Eval ![0] f) (succ : ∀ x, φ.Eval ![x] f → φ.Eval ![x + 1] f) :
    ∀ x, φ.Eval ![x] f := by
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_ss (U := 𝗟 Γ s) inferInstance Set.subset_union_left;
  have : V↓[ℒₒᵣ] ⊧* LeastNumberScheme (Arithmetic.StrictHierarchy Γ s) :=
    models_of_ss (U := 𝗟 Γ s) inferInstance Set.subset_union_right;
  by_contra! hcon;
  obtain ⟨a, ha⟩ := hcon;
  obtain ⟨y, hy, hmin⟩ := LeastNumberScheme.least_number
    (C := Arithmetic.StrictHierarchy Γ s) (P := fun x ↦ ¬φ.Eval ![x] f)
    ⟨f, ∼φ, by simpa using hφ, by simp⟩ ha;
  obtain ⟨z, rfl⟩ := Arithmetic.exists_succ_of_ne_zero <| show y ≠ 0 by rintro rfl; exact hy zero;
  exact hy (succ z (by simpa using hmin z (by simp)));

lemma models_InductionOnHierarchy_of_models_LeastNumberOnHierarchy (Γ : Polarity) (s : ℕ)
    [V↓[ℒₒᵣ] ⊧* 𝗟 Γ s] : V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗 Γ.alt s := by
  have hPA : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_ss (U := 𝗟 Γ s) inferInstance Set.subset_union_left;
  suffices V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ (Arithmetic.StrictHierarchy Γ.alt s) by
    simpa [InductionOnHierarchy, Semantics.ModelsSet.union_iff] using ⟨hPA, this⟩;
  simp only [InductionScheme];
  apply Semantics.ModelsSet.setOf_iff.mpr;
  rintro _ ⟨φ, hφ, rfl⟩;
  suffices ∀ f : ℕ → V, φ.Eval ![0] f → (∀ x, φ.Eval ![x] f → φ.Eval ![x + 1] f) →
      ∀ x, φ.Eval ![x] f by
    simpa [models_iff, Semiformula.eval_univCl, succInd, Semiformula.eval_substs,
      Matrix.constant_eq_singleton] using this;
  intro f;
  exact LeastNumberOnHierarchy.succ_induction Γ s hφ f;

lemma models_LeastNumberOnHierarchy_of_models_ISigma (V : Type*) [ORingStructure V]
    (Γ : Polarity) (s : ℕ) [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 s] : V↓[ℒₒᵣ] ⊧* 𝗟 Γ s :=
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺s := models_IBroadSigma_of_models_InductionOnHierarchy 𝚺 s V
  models_of_ss (models_LeastNumberOnBroadHierarchy_of_IBroadSigma Γ s)
    (Set.union_subset_union_right _ (LeastNumberScheme_subset (·.hierarchy)))

/-- The least number scheme for the strict hierarchy is `𝗜𝚺 s`.
- [HP98, Theorem I.2.4] -/
theorem LSigma_equiv_ISigma (s : ℕ) : 𝗟𝚺 s ≊ 𝗜𝚺 s :=
  Equiv.antisymm_iff.mpr
    ⟨weakerThan_of_models.{0} _ _ fun V _ _ ↦ models_LeastNumberOnHierarchy_of_models_ISigma V 𝚺 s,
      weakerThan_of_models.{0} _ _ fun V _ _ ↦
        have : V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗 𝚷 s :=
          models_InductionOnHierarchy_of_models_LeastNumberOnHierarchy 𝚺 s
        have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺⁺s := models_IBroadSigma_of_models_InductionOnHierarchy 𝚷 s V
        mod_ISigma_of_IBroadSigma⟩

theorem LPi_equiv_ISigma (s : ℕ) : 𝗟𝚷 s ≊ 𝗜𝚺 s :=
  Equiv.antisymm_iff.mpr
    ⟨weakerThan_of_models.{0} _ _ fun V _ _ ↦ models_LeastNumberOnHierarchy_of_models_ISigma V 𝚷 s,
      weakerThan_of_models.{0} _ _ fun _ _ _ ↦
        models_InductionOnHierarchy_of_models_LeastNumberOnHierarchy 𝚷 s⟩

theorem LSigma_equiv_LBroadSigma (s : ℕ) : 𝗟𝚺 s ≊ 𝗟𝚺⁺ s :=
  ((LSigma_equiv_ISigma s).trans (ISigma_equiv_IBroadSigma s)).trans
    (LBroadSigma_equiv_IBroadSigma s).symm

theorem LPi_equiv_LBroadPi (s : ℕ) : 𝗟𝚷 s ≊ 𝗟𝚷⁺ s :=
  ((LPi_equiv_ISigma s).trans (ISigma_equiv_IBroadSigma s)).trans
    (LBroadPi_equiv_IBroadSigma s).symm

end leastNumber

end FFL.FirstOrder.Arithmetic
