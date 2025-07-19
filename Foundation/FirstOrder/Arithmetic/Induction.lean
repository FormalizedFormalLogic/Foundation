import Foundation.FirstOrder.Arithmetic.Definability
import Foundation.FirstOrder.PeanoMinus.Functions
import Foundation.FirstOrder.TrueArithmetic.Basic

/-!
# Induction schemata of Arithmetic

-/

namespace LO

open FirstOrder

variable {L : Language} [L.ORing] {ξ : Type*} [DecidableEq ξ]

namespace FirstOrder

def succInd {ξ} (φ : Semiformula L ξ 1) : Formula L ξ := “!φ 0 → (∀ x, !φ x → !φ (x + 1)) → ∀ x, !φ x”

def orderInd {ξ} (φ : Semiformula L ξ 1) : Formula L ξ := “(∀ x, (∀ y < x, !φ y) → !φ x) → ∀ x, !φ x”

def leastNumber {ξ} (φ : Semiformula L ξ 1) : Formula L ξ := “(∃ x, !φ x) → ∃ z, !φ z ∧ ∀ x < z, ¬!φ x”

end FirstOrder

variable (L)

def InductionScheme (Γ : Semiformula L ℕ 1 → Prop) : Theory L :=
  { ψ | ∃ φ : Semiformula L ℕ 1, Γ φ ∧ ψ = succInd φ }

abbrev IOpen : ArithmeticTheory := 𝐏𝐀⁻ + InductionScheme ℒₒᵣ Semiformula.Open

notation "𝐈Open" => IOpen

abbrev InductionOnHierarchy (Γ : Polarity) (k : ℕ) : ArithmeticTheory := 𝐏𝐀⁻ + InductionScheme ℒₒᵣ (Arithmetic.Hierarchy Γ k)

prefix:max "𝐈𝐍𝐃 " => InductionOnHierarchy

abbrev ISigma (k : ℕ) : ArithmeticTheory := 𝐈𝐍𝐃 𝚺 k

prefix:max "𝐈𝚺" => ISigma

notation "𝐈𝚺₀" => ISigma 0

abbrev IPi (k : ℕ) : ArithmeticTheory := 𝐈𝐍𝐃 𝚷 k

prefix:max "𝐈𝚷" => IPi

notation "𝐈𝚷₀" => IPi 0

notation "𝐈𝚺₁" => ISigma 1

notation "𝐈𝚷₁" => IPi 1

abbrev Peano : ArithmeticTheory := 𝐏𝐀⁻ + InductionScheme ℒₒᵣ Set.univ

notation "𝐏𝐀" => Peano

variable {L}

variable {C C' : Semiformula ℒₒᵣ ℕ 1 → Prop}

lemma InductionScheme_subset (h : ∀ {φ : Semiformula ℒₒᵣ ℕ 1},  C φ → C' φ) : InductionScheme ℒₒᵣ C ⊆ InductionScheme ℒₒᵣ C' := by
  intro _; simp only [InductionScheme, Set.mem_setOf_eq, forall_exists_index, and_imp]; rintro φ hp rfl; exact ⟨φ, h hp, rfl⟩

lemma ISigma_subset_mono {s₁ s₂} (h : s₁ ≤ s₂) : 𝐈𝚺 s₁ ⊆ 𝐈𝚺 s₂ :=
  Set.union_subset_union_right _ (InductionScheme_subset (fun H ↦ H.mono h))

lemma ISigma_weakerThan_of_le {s₁ s₂} (h : s₁ ≤ s₂) : 𝐈𝚺 s₁ ⪯ 𝐈𝚺 s₂ :=
  Entailment.WeakerThan.ofSubset (ISigma_subset_mono h)

instance : 𝐏𝐀⁻ ⪯ 𝐈𝐍𝐃 Γ n := Entailment.WeakerThan.ofSubset (by simp [InductionOnHierarchy, Theory.add_def])

instance : 𝐄𝐐 ⪯ 𝐈𝐍𝐃 Γ n := Entailment.WeakerThan.trans (inferInstanceAs (𝐄𝐐 ⪯ 𝐏𝐀⁻)) inferInstance

instance : 𝐄𝐐 ⪯ 𝐈Open := Entailment.WeakerThan.trans (inferInstanceAs (𝐄𝐐 ⪯ 𝐏𝐀⁻)) inferInstance

instance : 𝐈Open ⪯ 𝐈𝐍𝐃 Γ n :=
  Entailment.WeakerThan.ofSubset <| Set.union_subset_union_right _  <| InductionScheme_subset Arithmetic.Hierarchy.of_open

instance : 𝐈𝚺₀ ⪯ 𝐈𝚺₁ :=
  ISigma_weakerThan_of_le (by decide)

instance : 𝐈𝚺i ⪯ 𝐏𝐀 :=
  Entailment.WeakerThan.ofSubset <| Set.union_subset_union_right _  <| InductionScheme_subset (by intros; trivial)

lemma mem_InductionScheme_of_mem {φ : Semiformula ℒₒᵣ ℕ 1} (hp : C φ) :
    succInd φ ∈ InductionScheme ℒₒᵣ C := by
  simpa [InductionScheme] using ⟨φ, hp, rfl⟩

lemma mem_IOpen_of_qfree {φ : Semiformula ℒₒᵣ ℕ 1} (hp : φ.Open) :
    succInd φ ∈ InductionScheme ℒₒᵣ Semiformula.Open := by
  exact ⟨φ, hp, rfl⟩

instance : 𝐏𝐀⁻ ⪯ 𝐈Open := inferInstance

instance : 𝐈Open ⪯ 𝐈𝚺₀ := inferInstance

instance : 𝐈𝚺₁ ⪯ 𝐏𝐀 := inferInstance

end LO

namespace LO

open FirstOrder Arithmetic PeanoMinus

variable {V : Type*} [ORingStruc V]

namespace InductionScheme

variable {C : Semiformula ℒₒᵣ ℕ 1 → Prop} [V ⊧ₘ* InductionScheme ℒₒᵣ C]

private lemma induction_eval {φ : Semiformula ℒₒᵣ ℕ 1} (hp : C φ) (v) :
    Semiformula.Evalm V ![0] v φ →
    (∀ x, Semiformula.Evalm V ![x] v φ → Semiformula.Evalm V ![x + 1] v φ) →
    ∀ x, Semiformula.Evalm V ![x] v φ := by
  have : V ⊧ₘ succInd φ :=
    ModelsTheory.models (T := InductionScheme _ C) V (by simpa using mem_InductionScheme_of_mem hp)
  revert v
  simpa [models_iff, succInd, Semiformula.eval_substs, Semiformula.eval_rew_q Rew.toS, Function.comp, Matrix.constant_eq_singleton] using this

@[elab_as_elim]
lemma succ_induction {P : V → Prop}
    (hP : ∃ e : ℕ → V, ∃ φ : Semiformula ℒₒᵣ ℕ 1, C φ ∧ ∀ x, P x ↔ Semiformula.Evalm V ![x] e φ) :
    P 0 → (∀ x, P x → P (x + 1)) → ∀ x, P x := by
  rcases hP with ⟨e, φ, Cp, hp⟩; simpa [←hp] using induction_eval (V := V) Cp e

end InductionScheme

namespace InductionOnHierarchy

section

variable (Γ : Polarity) (m : ℕ) [V ⊧ₘ* 𝐈𝐍𝐃 Γ m]

instance : V ⊧ₘ* InductionScheme ℒₒᵣ (Hierarchy Γ m) := models_of_subtheory <| inferInstanceAs (V ⊧ₘ* 𝐈𝐍𝐃 Γ m)

lemma succ_induction {P : V → Prop} (hP : Γ-[m].BoldfacePred P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x :=
  haveI : V ⊧ₘ* 𝐏𝐀⁻ := models_of_subtheory <| inferInstanceAs (V ⊧ₘ* 𝐈𝐍𝐃 Γ m)
  InductionScheme.succ_induction (P := P) (C := Hierarchy Γ m) (by
    rcases hP with ⟨φ, hp⟩
    haveI : Inhabited V := Classical.inhabited_of_nonempty'
    exact ⟨φ.val.enumarateFVar, (Rew.rewriteMap φ.val.idxOfFVar) ▹ φ.val, by simp,
      by  intro x; simp [Semiformula.eval_rewriteMap]
          have : (Semiformula.Evalm V ![x] fun x ↦ φ.val.enumarateFVar (φ.val.idxOfFVar x)) φ.val ↔ (Semiformula.Evalm V ![x] id) φ.val :=
            Semiformula.eval_iff_of_funEqOn _ (by
              intro x hx; simp [Semiformula.enumarateFVar_idxOfFVar (Semiformula.mem_fvarList_iff_fvar?.mpr hx)])
          simp [this, hp.df.iff]⟩)
    zero succ

lemma order_induction {P : V → Prop} (hP : Γ-[m].BoldfacePred P)
    (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x := by
  haveI : V ⊧ₘ* 𝐏𝐀⁻ := models_of_subtheory <| inferInstanceAs (V ⊧ₘ* 𝐈𝐍𝐃 Γ m)
  suffices ∀ x, ∀ y < x, P y by
    intro x; exact this (x + 1) x (by simp only [lt_add_iff_pos_right, lt_one_iff_eq_zero])
  intro x; induction x using succ_induction
  · exact Γ
  · exact m
  · suffices Γ-[m].BoldfacePred fun x ↦ ∀ y < x, P y by exact this
    exact HierarchySymbol.Boldface.ball_blt (by simp) (hP.retraction ![0])
  case zero => simp
  case succ x IH =>
    intro y hxy
    rcases show y < x ∨ y = x from lt_or_eq_of_le (le_iff_lt_succ.mpr hxy) with (lt | rfl)
    · exact IH y lt
    · exact ind y IH
  case inst => infer_instance

private lemma neg_succ_induction {P : V → Prop} (hP : Γ-[m].BoldfacePred P)
    (nzero : ¬P 0) (nsucc : ∀ x, ¬P x → ¬P (x + 1)) : ∀ x, ¬P x := by
  haveI : V ⊧ₘ* 𝐏𝐀⁻ := models_of_subtheory <| inferInstanceAs (V ⊧ₘ* 𝐈𝐍𝐃 Γ m)
  by_contra A
  have : ∃ x, P x := by simpa using A
  rcases this with ⟨a, ha⟩
  have : ∀ x ≤ a, P (a - x) := by
    intro x; induction x using succ_induction
    · exact Γ
    · exact m
    · suffices Γ-[m].BoldfacePred fun x ↦ x ≤ a → P (a - x) by exact this
      apply HierarchySymbol.Boldface.imp
      · apply HierarchySymbol.Boldface.bcomp₂ (by definability) (by definability)
      · apply HierarchySymbol.Boldface.bcomp₁ (by definability)
    case zero =>
      intro _; simpa using ha
    case succ x IH =>
      intro hx
      have : P (a - x) := IH (le_of_add_le_left hx)
      exact (not_imp_not.mp <| nsucc (a - (x + 1))) (by
        rw [←PeanoMinus.sub_sub, sub_add_self_of_le]
        · exact this
        · exact le_tsub_of_add_le_left hx)
    case inst => infer_instance
  have : P 0 := by simpa using this a (by rfl)
  contradiction

instance models_InductionScheme_alt : V ⊧ₘ* InductionScheme ℒₒᵣ (Arithmetic.Hierarchy Γ.alt m) := by
  suffices
      ∀ (φ : Semiformula ℒₒᵣ ℕ 1), Hierarchy Γ.alt m φ →
      ∀ (f : ℕ → V),
        Semiformula.Evalm V ![0] f φ →
        (∀ x, Semiformula.Evalm V ![x] f φ → Semiformula.Evalm V ![x + 1] f φ) →
        ∀ x, Semiformula.Evalm V ![x] f φ by
    simp only [InductionScheme, Semantics.RealizeSet.setOf_iff, forall_exists_index, and_imp]
    rintro _ φ hφ rfl
    simpa [models_iff, succInd, Semiformula.eval_rew_q,
        Semiformula.eval_substs, Function.comp, Matrix.constant_eq_singleton]
    using this φ hφ
  intro φ hp v
  simpa using
    neg_succ_induction Γ m (P := fun x ↦ ¬Semiformula.Evalm V ![x] v φ)
      (.mkPolarity (∼(Rew.rewriteMap v ▹ φ)) (by simpa using hp)
      (by intro x; simp [←Matrix.fun_eq_vec_one, Semiformula.eval_rewriteMap]))

instance models_alt : V ⊧ₘ* 𝐈𝐍𝐃 Γ.alt m := by
  haveI : V ⊧ₘ* 𝐏𝐀⁻ := models_of_subtheory <| inferInstanceAs (V ⊧ₘ* 𝐈𝐍𝐃 Γ m)
  simp only [InductionOnHierarchy, ModelsTheory.add_iff]; constructor <;> infer_instance

lemma least_number {P : V → Prop} (hP : Γ-[m].BoldfacePred P)
    {x} (h : P x) : ∃ y, P y ∧ ∀ z < y, ¬P z := by
  haveI : V ⊧ₘ* 𝐏𝐀⁻ := models_of_subtheory <| inferInstanceAs (V ⊧ₘ* 𝐈𝐍𝐃 Γ m)
  by_contra A
  have A : ∀ z, P z → ∃ w < z, P w := by simpa using A
  have : ∀ z, ∀ w < z, ¬P w := by
    intro z
    induction z using succ_induction
    · exact Γ.alt
    · exact m
    · suffices Γ.alt-[m].BoldfacePred fun z ↦ ∀ w < z, ¬P w by exact this
      apply HierarchySymbol.Boldface.ball_blt (by definability)
      apply HierarchySymbol.Boldface.not
      apply HierarchySymbol.Boldface.bcomp₁ (hP := by simpa using hP) (by definability)
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

variable (Γ : SigmaPiDelta) (m : ℕ) [V ⊧ₘ* 𝐈𝐍𝐃 𝚺 m]

lemma succ_induction_sigma {P : V → Prop} (hP : Γ-[m].BoldfacePred P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x :=
  match Γ with
  | 𝚺 => succ_induction 𝚺 m hP zero succ
  | 𝚷 =>
    haveI : V ⊧ₘ* 𝐈𝐍𝐃 𝚷 m := models_alt 𝚺 m
    succ_induction 𝚷 m hP zero succ
  | 𝚫 => succ_induction 𝚺 m hP.of_delta zero succ

lemma order_induction_sigma {P : V → Prop} (hP : Γ-[m].BoldfacePred P)
    (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x :=
  match Γ with
  | 𝚺 => order_induction 𝚺 m hP ind
  | 𝚷 =>
    haveI : V ⊧ₘ* 𝐈𝐍𝐃 𝚷 m := models_alt 𝚺 m
    order_induction 𝚷 m hP ind
  | 𝚫 => order_induction 𝚺 m hP.of_delta ind

lemma least_number_sigma {P : V → Prop} (hP : Γ-[m].BoldfacePred P)
    {x} (h : P x) : ∃ y, P y ∧ ∀ z < y, ¬P z :=
  match Γ with
  | 𝚺 => least_number 𝚺 m hP h
  | 𝚷 =>
    haveI : V ⊧ₘ* 𝐈𝐍𝐃 𝚷 m := models_alt 𝚺 m
    least_number 𝚷 m hP h
  | 𝚫 => least_number 𝚺 m hP.of_delta h

end

instance [V ⊧ₘ* 𝐈𝐍𝐃 𝚺 m] : V ⊧ₘ* 𝐈𝐍𝐃 Γ m := by
  rcases Γ
  · infer_instance
  · exact models_alt 𝚺 m

instance [V ⊧ₘ* 𝐈𝐍𝐃 𝚷 m] : V ⊧ₘ* 𝐈𝐍𝐃 Γ m := by
  rcases Γ
  · exact models_alt 𝚷 m
  · infer_instance

lemma mod_ISigma_of_le {n₁ n₂} (h : n₁ ≤ n₂) [V ⊧ₘ* 𝐈𝚺 n₂] : V ⊧ₘ* 𝐈𝚺 n₁ :=
  ModelsTheory.of_ss inferInstance (ISigma_subset_mono h)

instance [V ⊧ₘ* 𝐈𝚺₁] : V ⊧ₘ* 𝐈𝚺₀ := mod_ISigma_of_le (show 0 ≤ 1 from by simp)

instance [V ⊧ₘ* 𝐈𝚺n] : V ⊧ₘ* 𝐈𝚷n := inferInstance

instance [V ⊧ₘ* 𝐈𝚷n] : V ⊧ₘ* 𝐈𝚺n := inferInstance

lemma models_ISigma_iff_models_IPi {n} : V ⊧ₘ* 𝐈𝚺 n ↔ V ⊧ₘ* 𝐈𝚷 n :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩

instance [V ⊧ₘ* 𝐈𝚺 n] : V ⊧ₘ* 𝐈𝐍𝐃 Γ n :=
  match Γ with
  | 𝚺 => inferInstance
  | 𝚷 => inferInstance

end InductionOnHierarchy

@[elab_as_elim] lemma ISigma0.succ_induction [V ⊧ₘ* 𝐈𝚺₀]
    {P : V → Prop} (hP : 𝚺₀.BoldfacePred P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x :=
  InductionOnHierarchy.succ_induction 𝚺 0 hP zero succ

@[elab_as_elim] lemma ISigma1.sigma1_succ_induction [V ⊧ₘ* 𝐈𝚺₁]
    {P : V → Prop} (hP : 𝚺₁-Predicate P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x :=
  InductionOnHierarchy.succ_induction 𝚺 1 hP zero succ

@[elab_as_elim] lemma ISigma1.pi1_succ_induction [V ⊧ₘ* 𝐈𝚺₁]
    {P : V → Prop} (hP : 𝚷₁-Predicate P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x :=
  InductionOnHierarchy.succ_induction 𝚷 1 hP zero succ

@[elab_as_elim] lemma ISigma0.order_induction [V ⊧ₘ* 𝐈𝚺₀]
    {P : V → Prop} (hP : 𝚺₀-Predicate P)
    (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x :=
  InductionOnHierarchy.order_induction 𝚺 0 hP ind

@[elab_as_elim] lemma ISigma1.sigma1_order_induction [V ⊧ₘ* 𝐈𝚺₁]
    {P : V → Prop} (hP : 𝚺₁-Predicate P)
    (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x :=
  InductionOnHierarchy.order_induction 𝚺 1 hP ind

@[elab_as_elim] lemma ISigma1.pi1_order_induction [V ⊧ₘ* 𝐈𝚺₁]
    {P : V → Prop} (hP : 𝚷₁-Predicate P)
    (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x :=
  InductionOnHierarchy.order_induction 𝚷 1 hP ind

lemma ISigma0.least_number [V ⊧ₘ* 𝐈𝚺₀] {P : V → Prop} (hP : 𝚺₀-Predicate P)
    {x} (h : P x) : ∃ y, P y ∧ ∀ z < y, ¬P z :=
  InductionOnHierarchy.least_number 𝚺 0 hP h

@[elab_as_elim] lemma ISigma1.succ_induction [V ⊧ₘ* 𝐈𝚺₁] (Γ)
    {P : V → Prop} (hP : Γ-[1]-Predicate P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x :=
  InductionOnHierarchy.succ_induction_sigma Γ 1 hP zero succ

@[elab_as_elim] lemma ISigma1.order_induction [V ⊧ₘ* 𝐈𝚺₁] (Γ)
    {P : V → Prop} (hP : Γ-[1]-Predicate P)
    (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x :=
  InductionOnHierarchy.order_induction_sigma Γ 1 hP ind


instance [V ⊧ₘ* 𝐈Open] : V ⊧ₘ* 𝐏𝐀⁻ := models_of_subtheory <| inferInstanceAs (V ⊧ₘ* 𝐈Open)

instance [V ⊧ₘ* 𝐈𝚺₀] : V ⊧ₘ* 𝐈Open := models_of_subtheory <| inferInstanceAs (V ⊧ₘ* 𝐈𝚺₀)

instance [V ⊧ₘ* 𝐈𝚺₁] : V ⊧ₘ* 𝐈𝚺₀ := inferInstance

def mod_ISigma_of_le {n₁ n₂} (h : n₁ ≤ n₂) [V ⊧ₘ* 𝐈𝚺 n₂] : V ⊧ₘ* 𝐈𝚺 n₁ :=
  ModelsTheory.of_ss inferInstance (ISigma_subset_mono h)

lemma models_succInd (φ : Semiformula ℒₒᵣ ℕ 1) : ℕ ⊧ₘ succInd φ := by
  suffices
    ∀ f : ℕ → ℕ,
      Semiformula.Evalm ℕ ![0] f φ →
      (∀ x, Semiformula.Evalm ℕ ![x] f φ → Semiformula.Evalm ℕ ![x + 1] f φ) →
        ∀ x, Semiformula.Evalm ℕ ![x] f φ by
    simpa [succInd, models_iff, Matrix.constant_eq_singleton, Semiformula.eval_substs]
  intro e hzero hsucc x; induction' x with x ih
  · exact hzero
  · exact hsucc x ih

instance models_ISigma (Γ k) : ℕ ⊧ₘ* 𝐈𝐍𝐃 Γ k := by
  simp only [ModelsTheory.add_iff, instModelsTheoryNat, InductionScheme,
    Semantics.RealizeSet.setOf_iff, forall_exists_index, and_imp, true_and]
  rintro _ φ _ rfl; simp [models_succInd]

instance models_ISigmaZero : ℕ ⊧ₘ* 𝐈𝚺₀ := inferInstance

instance models_ISigmaOne : ℕ ⊧ₘ* 𝐈𝚺₁ := inferInstance

instance models_Peano : ℕ ⊧ₘ* 𝐏𝐀 := by
  simp only [Peano, InductionScheme, ModelsTheory.add_iff, instModelsTheoryNat,
    Semantics.RealizeSet.setOf_iff, forall_exists_index, and_imp, true_and]
  rintro _ φ _ rfl; simp [models_succInd]

instance : Entailment.Consistent (𝐈𝐍𝐃 Γ k) := (𝐈𝐍𝐃 Γ k).consistent_of_sound (Eq ⊥) rfl

instance : Entailment.Consistent 𝐏𝐀 := 𝐏𝐀.consistent_of_sound (Eq ⊥) rfl

instance : 𝐏𝐀 ⪯ 𝐓𝐀 := inferInstance

instance (T : ArithmeticTheory) [𝐏𝐀⁻ ⪯ T] : 𝐑₀ ⪯ T :=
  Entailment.WeakerThan.trans (inferInstanceAs (𝐑₀ ⪯ 𝐏𝐀⁻)) inferInstance

instance (T : ArithmeticTheory) [𝐈𝚺₀ ⪯ T] : 𝐏𝐀⁻ ⪯ T :=
  Entailment.WeakerThan.trans (inferInstanceAs (𝐏𝐀⁻ ⪯ 𝐈𝚺₀)) inferInstance

instance (T : ArithmeticTheory) [𝐈𝚺₁ ⪯ T] : 𝐏𝐀⁻ ⪯ T :=
  Entailment.WeakerThan.trans (inferInstanceAs (𝐏𝐀⁻ ⪯ 𝐈𝚺₁)) inferInstance

instance (T : ArithmeticTheory) [𝐏𝐀 ⪯ T] : 𝐏𝐀⁻ ⪯ T :=
  Entailment.WeakerThan.trans (inferInstanceAs (𝐏𝐀⁻ ⪯ 𝐏𝐀)) inferInstance

end LO
