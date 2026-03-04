module

public import Foundation.FirstOrder.Arithmetic.PeanoMinus.Functions
public import Foundation.FirstOrder.Arithmetic.TA.Basic

@[expose] public section
/-!
# Induction schemata of Arithmetic
-/

namespace LO.FirstOrder.Arithmetic

section axioms

variable {L : Language} [L.ORing] {ξ : Type*} [DecidableEq ξ]

def succInd {ξ} (φ : Semiformula L ξ 1) : Formula L ξ := “!φ 0 → (∀ x, !φ x → !φ (x + 1)) → ∀ x, !φ x”

def orderInd {ξ} (φ : Semiformula L ξ 1) : Formula L ξ := “(∀ x, (∀ y < x, !φ y) → !φ x) → ∀ x, !φ x”

def leastNumber {ξ} (φ : Semiformula L ξ 1) : Formula L ξ := “(∃ x, !φ x) → ∃ z, !φ z ∧ ∀ x < z, ¬!φ x”

variable (L)

def InductionScheme (Γ : Semiformula L ℕ 1 → Prop) : Theory L :=
  { ψ | ∃ φ : Semiformula L ℕ 1, Γ φ ∧ ψ = .univCl (succInd φ) }

abbrev IOpen : ArithmeticTheory := 𝗣𝗔⁻ + InductionScheme ℒₒᵣ Semiformula.Open

notation "𝗜𝗢𝗽𝗲𝗻" => IOpen

abbrev InductionOnHierarchy (Γ : Polarity) (k : ℕ) : ArithmeticTheory := 𝗣𝗔⁻ + InductionScheme ℒₒᵣ (Arithmetic.Hierarchy Γ k)

prefix:max "𝗜𝗡𝗗 " => InductionOnHierarchy

abbrev ISigma (k : ℕ) : ArithmeticTheory := 𝗜𝗡𝗗 𝚺 k

prefix:max "𝗜𝚺" => ISigma

notation "𝗜𝚺₀" => ISigma 0

abbrev IPi (k : ℕ) : ArithmeticTheory := 𝗜𝗡𝗗 𝚷 k

prefix:max "𝗜𝚷" => IPi

notation "𝗜𝚷₀" => IPi 0

notation "𝗜𝚺₁" => ISigma 1

notation "𝗜𝚷₁" => IPi 1

abbrev Peano : ArithmeticTheory := 𝗣𝗔⁻ + InductionScheme ℒₒᵣ Set.univ

notation "𝗣𝗔" => Peano

variable {L}

variable {C C' : ArithmeticSemiformula ℕ 1 → Prop}

lemma InductionScheme_subset (h : ∀ {φ : ArithmeticSemiformula ℕ 1},  C φ → C' φ) : InductionScheme ℒₒᵣ C ⊆ InductionScheme ℒₒᵣ C' := by
  intro _; simp only [InductionScheme, Set.mem_setOf_eq, forall_exists_index, and_imp]; rintro φ hp rfl; exact ⟨φ, h hp, rfl⟩

lemma ISigma_subset_mono {s₁ s₂} (h : s₁ ≤ s₂) : 𝗜𝚺 s₁ ⊆ 𝗜𝚺 s₂ :=
  Set.union_subset_union_right _ (InductionScheme_subset (fun H ↦ H.mono h))

lemma ISigma_weakerThan_of_le {s₁ s₂} (h : s₁ ≤ s₂) : 𝗜𝚺 s₁ ⪯ 𝗜𝚺 s₂ :=
  Entailment.WeakerThan.ofSubset (ISigma_subset_mono h)

instance : 𝗘𝗤 ⪯ 𝗜𝗡𝗗 Γ n := Entailment.WeakerThan.trans (inferInstanceAs (𝗘𝗤 ⪯ 𝗣𝗔⁻)) inferInstance

instance : 𝗘𝗤 ⪯ 𝗜𝗢𝗽𝗲𝗻 := Entailment.WeakerThan.trans (inferInstanceAs (𝗘𝗤 ⪯ 𝗣𝗔⁻)) inferInstance

instance : 𝗜𝗢𝗽𝗲𝗻 ⪯ 𝗜𝗡𝗗 Γ n :=
  Entailment.WeakerThan.ofSubset <| Set.union_subset_union_right _  <| InductionScheme_subset Arithmetic.Hierarchy.of_open

instance : 𝗜𝚺₀ ⪯ 𝗜𝚺₁ := ISigma_weakerThan_of_le (by decide)

instance : 𝗜𝚺i ⪯ 𝗣𝗔 :=
  Entailment.WeakerThan.ofSubset <| Set.union_subset_union_right _  <| InductionScheme_subset (by intros; trivial)

lemma mem_InductionScheme_of_mem {φ : ArithmeticSemiformula ℕ 1} (hp : C φ) :
    .univCl (succInd φ) ∈ InductionScheme ℒₒᵣ C := by
  simpa [InductionScheme] using ⟨φ, hp, rfl⟩

lemma mem_IOpen_of_qfree {φ : ArithmeticSemiformula ℕ 1} (hp : φ.Open) :
    .univCl (succInd φ) ∈ InductionScheme ℒₒᵣ Semiformula.Open := by
  exact ⟨φ, hp, rfl⟩

instance : 𝗣𝗔⁻ ⪯ 𝗜𝗢𝗽𝗲𝗻 := inferInstance

instance : 𝗜𝗢𝗽𝗲𝗻 ⪯ 𝗜𝚺₀ := inferInstance

instance : 𝗜𝚺₁ ⪯ 𝗣𝗔 := inferInstance

end axioms

section models

variable {V : Type*} [ORingStructure V]

namespace InductionScheme

variable {C : ArithmeticSemiformula ℕ 1 → Prop} [V ⊧ₘ* InductionScheme ℒₒᵣ C]

private lemma induction_eval {φ : ArithmeticSemiformula ℕ 1} (hp : C φ) (v) :
    Semiformula.Evalm V ![0] v φ →
    (∀ x, Semiformula.Evalm V ![x] v φ → Semiformula.Evalm V ![x + 1] v φ) →
    ∀ x, Semiformula.Evalm V ![x] v φ := by
  have : V ⊧ₘ .univCl (succInd φ) :=
    ModelsTheory.models (T := InductionScheme _ C) V (by simpa using mem_InductionScheme_of_mem hp)
  revert v
  simpa [models_iff, Semiformula.eval_univCl, succInd, Semiformula.eval_substs,
    Semiformula.eval_rew_q Rew.toS, Function.comp, Matrix.constant_eq_singleton] using this

@[elab_as_elim]
lemma succ_induction {P : V → Prop}
    (hP : ∃ e : ℕ → V, ∃ φ : ArithmeticSemiformula ℕ 1, C φ ∧ ∀ x, P x ↔ Semiformula.Evalm V ![x] e φ) :
    P 0 → (∀ x, P x → P (x + 1)) → ∀ x, P x := by
  rcases hP with ⟨e, φ, Cp, hp⟩; simpa [←hp] using induction_eval (V := V) Cp e

end InductionScheme

namespace InductionOnHierarchy

section

variable (Γ : Polarity) (m : ℕ) [V ⊧ₘ* 𝗜𝗡𝗗 Γ m]

instance : V ⊧ₘ* InductionScheme ℒₒᵣ (Hierarchy Γ m) := models_of_subtheory <| inferInstanceAs (V ⊧ₘ* 𝗜𝗡𝗗 Γ m)

lemma succ_induction {P : V → Prop} (hP : Γ-[m].DefinablePred P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x :=
  haveI : V ⊧ₘ* 𝗣𝗔⁻ := models_of_subtheory <| inferInstanceAs (V ⊧ₘ* 𝗜𝗡𝗗 Γ m)
  InductionScheme.succ_induction (P := P) (C := Hierarchy Γ m) (by
    rcases hP with ⟨φ, hp⟩
    haveI : Inhabited V := Classical.inhabited_of_nonempty'
    exact ⟨φ.val.enumarateFVar, (Rew.rewriteMap φ.val.idxOfFVar) ▹ φ.val, by simp,
      by intro x; simp [Semiformula.eval_rewriteMap, hp.df.iff]⟩)
    zero succ

lemma order_induction {P : V → Prop} (hP : Γ-[m].DefinablePred P)
    (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x := by
  haveI : V ⊧ₘ* 𝗣𝗔⁻ := models_of_subtheory <| inferInstanceAs (V ⊧ₘ* 𝗜𝗡𝗗 Γ m)
  suffices ∀ x, ∀ y < x, P y by
    intro x; exact this (x + 1) x (by simp only [lt_add_iff_pos_right, lt_one_iff_eq_zero])
  intro x; induction x using succ_induction
  · exact Γ
  · exact m
  · suffices Γ-[m].DefinablePred fun x ↦ ∀ y < x, P y by exact this
    exact HierarchySymbol.Definable.ball_blt (by simp) (hP.retraction ![0])
  case zero => simp
  case succ x IH =>
    intro y hxy
    rcases show y < x ∨ y = x from lt_or_eq_of_le (le_iff_lt_succ.mpr hxy) with (lt | rfl)
    · exact IH y lt
    · exact ind y IH
  case inst => infer_instance

private lemma neg_succ_induction {P : V → Prop} (hP : Γ-[m].DefinablePred P)
    (nzero : ¬P 0) (nsucc : ∀ x, ¬P x → ¬P (x + 1)) : ∀ x, ¬P x := by
  haveI : V ⊧ₘ* 𝗣𝗔⁻ := models_of_subtheory <| inferInstanceAs (V ⊧ₘ* 𝗜𝗡𝗗 Γ m)
  by_contra A
  have : ∃ x, P x := by simpa using A
  rcases this with ⟨a, ha⟩
  have : ∀ x ≤ a, P (a - x) := by
    intro x; induction x using succ_induction
    · exact Γ
    · exact m
    · suffices Γ-[m].DefinablePred fun x ↦ x ≤ a → P (a - x) by exact this
      apply HierarchySymbol.Definable.imp
      · apply HierarchySymbol.Definable.bcomp₂ (by definability) (by definability)
      · apply HierarchySymbol.Definable.bcomp₁ (by definability)
    case zero =>
      intro _; simpa using ha
    case succ x IH =>
      intro hx
      have : P (a - x) := IH (le_of_add_le_left hx)
      exact (not_imp_not.mp <| nsucc (a - (x + 1))) (by
        rw [←Arithmetic.sub_sub, sub_add_self_of_le]
        · exact this
        · exact le_tsub_of_add_le_left hx)
    case inst => infer_instance
  have : P 0 := by simpa using this a (by rfl)
  contradiction

instance models_InductionScheme_alt : V ⊧ₘ* InductionScheme ℒₒᵣ (Arithmetic.Hierarchy Γ.alt m) := by
  suffices
      ∀ (φ : ArithmeticSemiformula ℕ 1), Hierarchy Γ.alt m φ →
      ∀ (f : ℕ → V),
        Semiformula.Evalm V ![0] f φ →
        (∀ x, Semiformula.Evalm V ![x] f φ → Semiformula.Evalm V ![x + 1] f φ) →
        ∀ x, Semiformula.Evalm V ![x] f φ by
    simp only [InductionScheme, Semantics.ModelsSet.setOf_iff, forall_exists_index, and_imp]
    rintro _ φ hφ rfl
    simpa [models_iff, Semiformula.eval_univCl, succInd, Semiformula.eval_rew_q,
        Semiformula.eval_substs, Function.comp, Matrix.constant_eq_singleton]
    using this φ hφ
  intro φ hp v
  simpa using
    neg_succ_induction Γ m (P := fun x ↦ ¬Semiformula.Evalm V ![x] v φ)
      (.mkPolarity (∼(Rew.rewriteMap v ▹ φ)) (by simpa using hp)
      (by intro x; simp [←Matrix.fun_eq_vec_one, Semiformula.eval_rewriteMap]))

instance models_alt : V ⊧ₘ* 𝗜𝗡𝗗 Γ.alt m := by
  haveI : V ⊧ₘ* 𝗣𝗔⁻ := models_of_subtheory <| inferInstanceAs (V ⊧ₘ* 𝗜𝗡𝗗 Γ m)
  simp only [InductionOnHierarchy, ModelsTheory.add_iff]; constructor <;> infer_instance

lemma least_number {P : V → Prop} (hP : Γ-[m].DefinablePred P)
    {x} (h : P x) : ∃ y, P y ∧ ∀ z < y, ¬P z := by
  haveI : V ⊧ₘ* 𝗣𝗔⁻ := models_of_subtheory <| inferInstanceAs (V ⊧ₘ* 𝗜𝗡𝗗 Γ m)
  by_contra A
  have A : ∀ z, P z → ∃ w < z, P w := by simpa using A
  have : ∀ z, ∀ w < z, ¬P w := by
    intro z
    induction z using succ_induction
    · exact Γ.alt
    · exact m
    · suffices Γ.alt-[m].DefinablePred fun z ↦ ∀ w < z, ¬P w by exact this
      apply HierarchySymbol.Definable.ball_blt (by definability)
      apply HierarchySymbol.Definable.not
      apply HierarchySymbol.Definable.bcomp₁ (hP := by simpa using hP) (by definability)
    case zero => simp
    case succ x IH =>
      intro w hx hw
      rcases le_iff_lt_or_eq.mp (lt_succ_iff_le.mp hx) with (hx | rfl)
      · exact IH w hx hw
      · have : ∃ v < w, P v := A w hw
        rcases this with ⟨v, hvw, hv⟩
        exact IH v hvw hv
    case inst => infer_instance
  exact this (x + 1) x (by simp) h

end

section

variable (Γ : SigmaPiDelta) (m : ℕ) [V ⊧ₘ* 𝗜𝗡𝗗 𝚺 m]

lemma succ_induction_sigma {P : V → Prop} (hP : Γ-[m].DefinablePred P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x :=
  match Γ with
  | 𝚺 => succ_induction 𝚺 m hP zero succ
  | 𝚷 =>
    haveI : V ⊧ₘ* 𝗜𝗡𝗗 𝚷 m := models_alt 𝚺 m
    succ_induction 𝚷 m hP zero succ
  | 𝚫 => succ_induction 𝚺 m hP.of_delta zero succ

lemma order_induction_sigma {P : V → Prop} (hP : Γ-[m].DefinablePred P)
    (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x :=
  match Γ with
  | 𝚺 => order_induction 𝚺 m hP ind
  | 𝚷 =>
    haveI : V ⊧ₘ* 𝗜𝗡𝗗 𝚷 m := models_alt 𝚺 m
    order_induction 𝚷 m hP ind
  | 𝚫 => order_induction 𝚺 m hP.of_delta ind

lemma least_number_sigma {P : V → Prop} (hP : Γ-[m].DefinablePred P)
    {x} (h : P x) : ∃ y, P y ∧ ∀ z < y, ¬P z :=
  match Γ with
  | 𝚺 => least_number 𝚺 m hP h
  | 𝚷 =>
    haveI : V ⊧ₘ* 𝗜𝗡𝗗 𝚷 m := models_alt 𝚺 m
    least_number 𝚷 m hP h
  | 𝚫 => least_number 𝚺 m hP.of_delta h

end

instance [V ⊧ₘ* 𝗜𝗡𝗗 𝚺 m] : V ⊧ₘ* 𝗜𝗡𝗗 Γ m := by
  rcases Γ
  · infer_instance
  · exact models_alt 𝚺 m

instance [V ⊧ₘ* 𝗜𝗡𝗗 𝚷 m] : V ⊧ₘ* 𝗜𝗡𝗗 Γ m := by
  rcases Γ
  · exact models_alt 𝚷 m
  · infer_instance

lemma mod_ISigma_of_le {n₁ n₂} (h : n₁ ≤ n₂) [V ⊧ₘ* 𝗜𝚺 n₂] : V ⊧ₘ* 𝗜𝚺 n₁ :=
  ModelsTheory.of_ss inferInstance (ISigma_subset_mono h)

instance [V ⊧ₘ* 𝗜𝚺₁] : V ⊧ₘ* 𝗜𝚺₀ := mod_ISigma_of_le (show 0 ≤ 1 from by simp)

instance [V ⊧ₘ* 𝗜𝚺n] : V ⊧ₘ* 𝗜𝚷n := inferInstance

instance [V ⊧ₘ* 𝗜𝚷n] : V ⊧ₘ* 𝗜𝚺n := inferInstance

lemma models_ISigma_iff_models_IPi {n} : V ⊧ₘ* 𝗜𝚺 n ↔ V ⊧ₘ* 𝗜𝚷 n :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩

instance [V ⊧ₘ* 𝗜𝚺 n] : V ⊧ₘ* 𝗜𝗡𝗗 Γ n :=
  match Γ with
  | 𝚺 => inferInstance
  | 𝚷 => inferInstance

end InductionOnHierarchy

@[elab_as_elim] lemma ISigma0.succ_induction [V ⊧ₘ* 𝗜𝚺₀]
    {P : V → Prop} (hP : 𝚺₀.DefinablePred P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x :=
  InductionOnHierarchy.succ_induction 𝚺 0 hP zero succ

@[elab_as_elim] lemma ISigma1.sigma1_succ_induction [V ⊧ₘ* 𝗜𝚺₁]
    {P : V → Prop} (hP : 𝚺₁-Predicate P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x :=
  InductionOnHierarchy.succ_induction 𝚺 1 hP zero succ

@[elab_as_elim] lemma ISigma1.pi1_succ_induction [V ⊧ₘ* 𝗜𝚺₁]
    {P : V → Prop} (hP : 𝚷₁-Predicate P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x :=
  InductionOnHierarchy.succ_induction 𝚷 1 hP zero succ

@[elab_as_elim] lemma ISigma0.order_induction [V ⊧ₘ* 𝗜𝚺₀]
    {P : V → Prop} (hP : 𝚺₀-Predicate P)
    (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x :=
  InductionOnHierarchy.order_induction 𝚺 0 hP ind

@[elab_as_elim] lemma ISigma1.sigma1_order_induction [V ⊧ₘ* 𝗜𝚺₁]
    {P : V → Prop} (hP : 𝚺₁-Predicate P)
    (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x :=
  InductionOnHierarchy.order_induction 𝚺 1 hP ind

@[elab_as_elim] lemma ISigma1.pi1_order_induction [V ⊧ₘ* 𝗜𝚺₁]
    {P : V → Prop} (hP : 𝚷₁-Predicate P)
    (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x :=
  InductionOnHierarchy.order_induction 𝚷 1 hP ind

lemma ISigma0.least_number [V ⊧ₘ* 𝗜𝚺₀] {P : V → Prop} (hP : 𝚺₀-Predicate P)
    {x} (h : P x) : ∃ y, P y ∧ ∀ z < y, ¬P z :=
  InductionOnHierarchy.least_number 𝚺 0 hP h

@[elab_as_elim] lemma ISigma1.succ_induction [V ⊧ₘ* 𝗜𝚺₁] (Γ)
    {P : V → Prop} (hP : Γ-[1]-Predicate P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x :=
  InductionOnHierarchy.succ_induction_sigma Γ 1 hP zero succ

@[elab_as_elim] lemma ISigma1.order_induction [V ⊧ₘ* 𝗜𝚺₁] (Γ)
    {P : V → Prop} (hP : Γ-[1]-Predicate P)
    (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x :=
  InductionOnHierarchy.order_induction_sigma Γ 1 hP ind

instance [V ⊧ₘ* 𝗜𝗢𝗽𝗲𝗻] : V ⊧ₘ* 𝗣𝗔⁻ := models_of_subtheory <| inferInstanceAs (V ⊧ₘ* 𝗜𝗢𝗽𝗲𝗻)

instance [V ⊧ₘ* 𝗜𝚺₀] : V ⊧ₘ* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory <| inferInstanceAs (V ⊧ₘ* 𝗜𝚺₀)

instance [V ⊧ₘ* 𝗜𝚺₁] : V ⊧ₘ* 𝗜𝚺₀ := inferInstance

def mod_ISigma_of_le {n₁ n₂} (h : n₁ ≤ n₂) [V ⊧ₘ* 𝗜𝚺 n₂] : V ⊧ₘ* 𝗜𝚺 n₁ :=
  ModelsTheory.of_ss inferInstance (ISigma_subset_mono h)

end models

lemma models_succInd (φ : ArithmeticSemiformula ℕ 1) : ℕ ⊧ₘ (succInd φ).univCl := by
  suffices
    ∀ f : ℕ → ℕ,
      Semiformula.Evalm ℕ ![0] f φ →
      (∀ x, Semiformula.Evalm ℕ ![x] f φ → Semiformula.Evalm ℕ ![x + 1] f φ) →
        ∀ x, Semiformula.Evalm ℕ ![x] f φ by
    simpa [Semiformula.eval_univCl, succInd, models_iff, Matrix.constant_eq_singleton, Semiformula.eval_substs]
  intro e hzero hsucc x; induction' x with x ih
  · exact hzero
  · exact hsucc x ih

instance models_ISigma (Γ k) : ℕ ⊧ₘ* 𝗜𝗡𝗗 Γ k := by
  simp only [ModelsTheory.add_iff, PeanoMinus.instModelsTheoryNat, InductionScheme,
    Semantics.ModelsSet.setOf_iff, forall_exists_index, and_imp, true_and]
  rintro _ φ _ rfl; simp [models_succInd]

instance models_ISigmaZero : ℕ ⊧ₘ* 𝗜𝚺₀ := inferInstance

instance models_ISigmaOne : ℕ ⊧ₘ* 𝗜𝚺₁ := inferInstance

instance models_Peano : ℕ ⊧ₘ* 𝗣𝗔 := by
  simp only [Peano, InductionScheme, ModelsTheory.add_iff, PeanoMinus.instModelsTheoryNat,
    Semantics.ModelsSet.setOf_iff, forall_exists_index, and_imp, true_and]
  rintro _ φ _ rfl; simp [models_succInd]

instance : Entailment.Consistent (𝗜𝗡𝗗 Γ k) := (𝗜𝗡𝗗 Γ k).consistent_of_sound (Eq ⊥) rfl

instance : Entailment.Consistent 𝗣𝗔 := 𝗣𝗔.consistent_of_sound (Eq ⊥) rfl

instance : 𝗣𝗔 ⪯ 𝗧𝗔 := inferInstance

instance (T : ArithmeticTheory) [𝗣𝗔⁻ ⪯ T] : 𝗥₀ ⪯ T :=
  Entailment.WeakerThan.trans (inferInstanceAs (𝗥₀ ⪯ 𝗣𝗔⁻)) inferInstance

instance (T : ArithmeticTheory) [𝗜𝚺₀ ⪯ T] : 𝗣𝗔⁻ ⪯ T :=
  Entailment.WeakerThan.trans (inferInstanceAs (𝗣𝗔⁻ ⪯ 𝗜𝚺₀)) inferInstance

instance (T : ArithmeticTheory) [𝗜𝚺₁ ⪯ T] : 𝗣𝗔⁻ ⪯ T :=
  Entailment.WeakerThan.trans (inferInstanceAs (𝗣𝗔⁻ ⪯ 𝗜𝚺₁)) inferInstance

instance (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] : 𝗣𝗔⁻ ⪯ T :=
  Entailment.WeakerThan.trans (inferInstanceAs (𝗣𝗔⁻ ⪯ 𝗣𝗔)) inferInstance

end LO.FirstOrder.Arithmetic
