import Foundation.FirstOrder.Arith.Definability
import Foundation.FirstOrder.PeanoMinus.Functions

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

abbrev IOpen : Theory ℒₒᵣ := 𝐏𝐀⁻ + InductionScheme ℒₒᵣ Semiformula.Open

notation "𝐈open" => IOpen

abbrev InductionOnHierarchy (Γ : Polarity) (k : ℕ) : Theory ℒₒᵣ := 𝐏𝐀⁻ + InductionScheme ℒₒᵣ (Arith.Hierarchy Γ k)

prefix:max "𝐈𝐍𝐃" => InductionOnHierarchy

abbrev ISigma (k : ℕ) : Theory ℒₒᵣ := 𝐈𝐍𝐃𝚺 k

prefix:max "𝐈𝚺" => ISigma

notation "𝐈𝚺₀" => ISigma 0

abbrev IPi (k : ℕ) : Theory ℒₒᵣ := 𝐈𝐍𝐃𝚷 k

prefix:max "𝐈𝚷" => IPi

notation "𝐈𝚷₀" => IPi 0

notation "𝐈𝚺₁" => ISigma 1

notation "𝐈𝚷₁" => IPi 1

abbrev Peano : Theory ℒₒᵣ := 𝐏𝐀⁻ + InductionScheme ℒₒᵣ Set.univ

notation "𝐏𝐀" => Peano

variable {L}

variable {C C' : Semiformula ℒₒᵣ ℕ 1 → Prop}

lemma coe_InductionOnHierarchy_subset_InductionOnHierarchy :
    (InductionScheme ℒₒᵣ (Arith.Hierarchy Γ ν) : Theory L) ⊆ InductionScheme L (Arith.Hierarchy Γ ν) := by
  simp only [InductionScheme, Set.image_subset_iff, Set.preimage_setOf_eq, Set.setOf_subset_setOf, forall_exists_index, and_imp]
  rintro _ φ Hp rfl
  exact ⟨Semiformula.lMap (Language.oringEmb : ℒₒᵣ →ᵥ L) φ, Arith.Hierarchy.oringEmb Hp,
    by simp [succInd, Semiformula.lMap_substs]⟩

lemma InductionScheme_subset (h : ∀ {φ : Semiformula ℒₒᵣ ℕ 1},  C φ → C' φ) : InductionScheme ℒₒᵣ C ⊆ InductionScheme ℒₒᵣ C' := by
  intro _; simp only [InductionScheme, Set.mem_setOf_eq, forall_exists_index, and_imp]; rintro φ hp rfl; exact ⟨φ, h hp, rfl⟩

lemma ISigma_subset_mono {s₁ s₂} (h : s₁ ≤ s₂) : 𝐈𝚺 s₁ ⊆ 𝐈𝚺 s₂ :=
  Set.union_subset_union_right _ (InductionScheme_subset (fun H ↦ H.mono h))

lemma ISigma_weakerThan_of_le {s₁ s₂} (h : s₁ ≤ s₂) : 𝐈𝚺 s₁ ⪯ 𝐈𝚺 s₂ :=
  Entailment.WeakerThan.ofSubset (ISigma_subset_mono h)

instance : 𝐏𝐀⁻ ⪯ 𝐈𝐍𝐃Γ n := Entailment.WeakerThan.ofSubset (by simp [InductionOnHierarchy, Theory.add_def])

instance : 𝐄𝐐 ⪯ 𝐈𝐍𝐃Γ n := Entailment.WeakerThan.trans (inferInstanceAs (𝐄𝐐 ⪯ 𝐏𝐀⁻)) inferInstance

instance : 𝐄𝐐 ⪯ 𝐈open := Entailment.WeakerThan.trans (inferInstanceAs (𝐄𝐐 ⪯ 𝐏𝐀⁻)) inferInstance

instance : 𝐈open ⪯ 𝐈𝚺i :=
  Entailment.WeakerThan.ofSubset <| Set.union_subset_union_right _  <| InductionScheme_subset Arith.Hierarchy.of_open

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

end LO

namespace LO.InductionScheme

open FirstOrder Arith PeanoMinus

variable {V : Type*} [ORingStruc V]

section

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
lemma induction {P : V → Prop}
    (hP : ∃ e : ℕ → V, ∃ φ : Semiformula ℒₒᵣ ℕ 1, C φ ∧ ∀ x, P x ↔ Semiformula.Evalm V ![x] e φ) :
    P 0 → (∀ x, P x → P (x + 1)) → ∀ x, P x := by
  rcases hP with ⟨e, φ, Cp, hp⟩; simpa [←hp] using induction_eval (V := V) Cp e

end

variable [V ⊧ₘ* 𝐏𝐀⁻]

section

variable (Γ : Polarity) (m : ℕ) [V ⊧ₘ* InductionScheme ℒₒᵣ (Arith.Hierarchy Γ m)]

lemma induction_h {P : V → Prop} (hP : Γ-[m].BoldfacePred P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x :=
  induction (P := P) (C := Hierarchy Γ m) (by
    rcases hP with ⟨φ, hp⟩
    haveI : Inhabited V := Classical.inhabited_of_nonempty'

    exact ⟨φ.val.enumarateFVar, (Rew.rewriteMap φ.val.idxOfFVar) ▹ φ.val, by simp [hp],
      by  intro x; simp [Semiformula.eval_rewriteMap]
          have : (Semiformula.Evalm V ![x] fun x ↦ φ.val.enumarateFVar (φ.val.idxOfFVar x)) φ.val ↔ (Semiformula.Evalm V ![x] id) φ.val :=
            Semiformula.eval_iff_of_funEqOn _ (by
              intro x hx; simp [Semiformula.enumarateFVar_idxOfFVar (Semiformula.mem_fvarList_iff_fvar?.mpr hx)])
          simp [this, hp.df.iff]⟩)
    zero succ

lemma order_induction_h {P : V → Prop} (hP : Γ-[m].BoldfacePred P)
    (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x := by
  suffices ∀ x, ∀ y < x, P y by
    intro x; exact this (x + 1) x (by simp only [lt_add_iff_pos_right, lt_one_iff_eq_zero])
  intro x; induction x using induction_h
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
  case inst => exact inferInstance

private lemma neg_induction_h {P : V → Prop} (hP : Γ-[m].BoldfacePred P)
    (nzero : ¬P 0) (nsucc : ∀ x, ¬P x → ¬P (x + 1)) : ∀ x, ¬P x := by
  by_contra A
  have : ∃ x, P x := by simpa using A
  rcases this with ⟨a, ha⟩
  have : ∀ x ≤ a, P (a - x) := by
    intro x; induction x using induction_h
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
    case inst => exact inferInstance
  have : P 0 := by simpa using this a (by rfl)
  contradiction

lemma models_InductionScheme_alt : V ⊧ₘ* InductionScheme ℒₒᵣ (Arith.Hierarchy Γ.alt m) := by
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
    neg_induction_h Γ m (P := fun x ↦ ¬Semiformula.Evalm V ![x] v φ)
      (.mkPolarity (∼(Rew.rewriteMap v ▹ φ)) (by simpa using hp)
      (by intro x; simp [←Matrix.fun_eq_vec_one, Semiformula.eval_rewriteMap]))

instance : V ⊧ₘ* InductionScheme ℒₒᵣ (Arith.Hierarchy Γ.alt m) := models_InductionScheme_alt Γ m

lemma least_number_h {P : V → Prop} (hP : Γ-[m].BoldfacePred P)
    {x} (h : P x) : ∃ y, P y ∧ ∀ z < y, ¬P z := by
  by_contra A
  have A : ∀ z, P z → ∃ w < z, P w := by simpa using A
  have : ∀ z, ∀ w < z, ¬P w := by
    intro z
    induction z using induction_h
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

end LO.InductionScheme
