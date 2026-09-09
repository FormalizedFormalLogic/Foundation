module

public import Foundation.FirstOrder.Arithmetic.HFS.PRF

@[expose] public section
/-!

# Fixpoint Construction

-/

namespace LO.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

namespace Fixpoint

-- `Fixpoint` is intentionally re-opened here even though the ambient namespace
-- already contains it; renaming would break the widely-used public API
-- (`Arithmetic.Fixpoint.*`). Suppress the new dupNamespace linter for the
-- declarations in this namespace (the option is scoped by `namespace`/`end` and
-- reverts automatically at `end Fixpoint`).
set_option linter.dupNamespace false

structure Blueprint (k : ℕ) where
  /-- WIP: Add a description of when `core (something :> something :> v)` is true here. -/
  core : 𝚫₁.Semisentence (k + 2)

namespace Blueprint

variable {k} (φ : Blueprint k)

instance : Coe (Blueprint k) (𝚫₁.Semisentence (k + 2)) := ⟨Blueprint.core⟩

/-- `succDef.Evalb (u :> ih :> i :> v)` holds iff `u` is the value at `i + 1`, where `ih` is the value at `i`. Equivalently `u = c.succ v i ih`. -/
def succDef : 𝚺₁.Semisentence (k + 3) := .mkSigma
  “u ih i. ∀ x < u + (i + 1), (x ∈ u → x ≤ i ∧ !φ.core.sigma x ih ⋯) ∧ (x ≤ i ∧ !φ.core.pi x ih ⋯ → x ∈ u)”

/-
Suppose `i = 0`.
`∀ x < u + 1, (x ∈ u ↔ x ≤ 0 ∧ !φ.core x ih ⋯)`
`u = {!φ.core 0 ih ⋯}`
-/

def prBlueprint : PR.Blueprint k where
  zero := .mkSigma “x. x = 0”
  succ := φ.succDef

def limSeqDef : 𝚺₁.Semisentence (k + 2) := (φ.prBlueprint).resultDef

def fixpointDef : 𝚺₁.Semisentence (k + 1) :=
  .mkSigma “x. ∃ i L, !φ.limSeqDef L i ⋯  ∧ x ∈ L”

def fixpointDefΔ₁ : 𝚫₁.Semisentence (k + 1) := .mkDelta
  (.mkSigma “x. ∃ L, !φ.limSeqDef L (x + 1) ⋯  ∧ x ∈ L”)
  (.mkPi “x. ∀ L, !φ.limSeqDef L (x + 1) ⋯  → x ∈ L”)

end Blueprint

variable (V)

structure Construction {k : ℕ} (φ : Blueprint k) where
  /-- `c.Φ (v.succ.succ)` -/
  Φ : (Fin k → V) → Set V → V → Prop
  defined : 𝚫₁.Defined (fun v ↦ Φ (v ·.succ.succ) {x | x ∈ v 1} (v 0)) φ.core
  monotone {C C' : Set V} (h : C ⊆ C') {v x} : Φ v C x → Φ v C' x

class Construction.Finite {k : ℕ} {φ : Blueprint k} (c : Construction V φ) where
  finite {C : Set V} {v x} : c.Φ v C x → ∃ m, c.Φ v {y ∈ C | y < m} x

class Construction.StrongFinite {k : ℕ} {φ : Blueprint k} (c : Construction V φ) where
  strong_finite {C : Set V} {v x} : c.Φ v C x → c.Φ v {y ∈ C | y < x} x

instance {k : ℕ} {φ : Blueprint k} (c : Construction V φ) [c.StrongFinite] : c.Finite where
  finite {_ _ x} := fun h ↦ ⟨x, Construction.StrongFinite.strong_finite h⟩

variable {V}

namespace Construction

variable {k : ℕ} {φ : Blueprint k} (c : Construction V φ) (v : Fin k → V)

lemma eval_formula (v : Fin k.succ.succ → V) :
    φ.core.val.Evalb v ↔ c.Φ (v ·.succ.succ) {x | x ∈ v 1} (v 0) := c.defined.iff

lemma succ_existsUnique (i ih : V) :
    ∃! u : V, ∀ x, (x ∈ u ↔ x ≤ i ∧ c.Φ v {z | z ∈ ih} x) := by
  have : 𝚺₁-Predicate fun x ↦ x ≤ i ∧ c.Φ v {z | z ∈ ih} x := by
    apply HierarchySymbol.Definable.and (by definability)
      ⟨φ.core.sigma.rew <| Rew.embSubsts (#0 :> &ih :> fun i ↦ &(v i)),
        by intro x; simp [HierarchySymbol.Semiformula.val_sigma, c.eval_formula]⟩
  exact finite_comprehension₁! this
    ⟨i + 1, fun i ↦ by rintro ⟨hi, _⟩; exact lt_succ_iff_le.mpr hi⟩

noncomputable def succ (i ih : V) : V := Classical.choose! (c.succ_existsUnique v i ih)

variable {v}

lemma mem_succ_iff {v i ih} :
    x ∈ c.succ v i ih ↔ x ≤ i ∧ c.Φ v {z | z ∈ ih} x := Classical.choose!_spec (c.succ_existsUnique v i ih) x

private lemma succ_graph {u v i ih} :
    u = c.succ v i ih ↔ ∀ x < u + (i + 1), x ∈ u ↔ x ≤ i ∧ c.Φ v {z | z ∈ ih} x :=
  ⟨by rintro rfl x _; simp [mem_succ_iff], by
    intro h; apply mem_ext
    intro x; constructor
    · intro hx; exact c.mem_succ_iff.mpr <| h x (lt_of_lt_of_le (lt_of_mem hx) (by simp)) |>.mp hx
    · intro hx
      exact h x (lt_of_lt_of_le (lt_succ_iff_le.mpr (c.mem_succ_iff.mp hx).1)
        (by simp)) |>.mpr (c.mem_succ_iff.mp hx)⟩

lemma succ_defined : 𝚺₁.DefinedFunction (fun v : Fin (k + 2) → V ↦ c.succ (v ·.succ.succ) (v 1) (v 0)) φ.succDef := .mk fun v ↦ by
  simp [Blueprint.succDef, succ_graph, HierarchySymbol.Semiformula.val_sigma, c.eval_formula,
    c.defined.proper.iff', -and_imp,  BinderNotation.finSuccItr]
  grind

lemma eval_succDef (v : Fin (k + 3) → V) :
    φ.succDef.val.Evalb v ↔ v 0 = c.succ (v ·.succ.succ.succ) (v 2) (v 1) := c.succ_defined.iff

noncomputable def prConstruction : PR.Construction V φ.prBlueprint where
  zero := fun _ ↦ ∅
  succ := c.succ
  zero_defined := .mk fun v ↦ by simp [Blueprint.prBlueprint, emptyset_def]
  succ_defined := .mk fun v ↦ by simp [Blueprint.prBlueprint, c.eval_succDef]

variable (v)

noncomputable def limSeq (i : V) : V := c.prConstruction.result v i

variable {v}

@[simp] lemma limSeq_zero : c.limSeq v 0 = ∅ := by simp [limSeq, prConstruction]

lemma limSeq_succ (i : V) : c.limSeq v (i + 1) = c.succ v i (c.limSeq v i) := by simp [limSeq, prConstruction]

lemma termSet_defined : 𝚺₁.DefinedFunction (fun v ↦ c.limSeq (v ·.succ) (v 0)) φ.limSeqDef := .mk
  fun v ↦ by simp [c.prConstruction.result_defined_iff, Blueprint.limSeqDef]; rfl

@[simp] lemma eval_limSeqDef (v : Fin (k + 2) → V) :
    φ.limSeqDef.val.Evalb v ↔ v 0 = c.limSeq (v ·.succ.succ) (v 1) := c.termSet_defined.iff

instance limSeq_definable :
  𝚺₁.DefinableFunction (fun v ↦ c.limSeq (v ·.succ) (v 0)) := c.termSet_defined.to_definable

@[simp, definability] instance limSeq_definable' (Γ) : Γ-[m + 1].DefinableFunction (fun v ↦ c.limSeq (v ·.succ) (v 0)) := c.limSeq_definable.of_sigmaOne

lemma mem_limSeq_succ_iff {x i : V} :
    x ∈ c.limSeq v (i + 1) ↔ x ≤ i ∧ c.Φ v {z | z ∈ c.limSeq v i} x := by simp [limSeq_succ, mem_succ_iff]

lemma limSeq_cumulative {i i' : V} : i ≤ i' → c.limSeq v i ⊆ c.limSeq v i' := by
  induction i' using ISigma1.sigma1_succ_induction generalizing i
  · apply HierarchySymbol.Definable.ball_le (by definability)
    apply HierarchySymbol.Definable.comp₂
    · exact ⟨φ.limSeqDef.rew <| Rew.embSubsts (#0 :> #1 :> fun j ↦ &(v j)), by intro v; simp [c.eval_limSeqDef]⟩
    · exact ⟨φ.limSeqDef.rew <| Rew.embSubsts (#0 :> #2 :> fun j ↦ &(v j)), by intro v; simp [c.eval_limSeqDef]⟩
  case zero =>
    simp only [nonpos_iff_eq_zero, limSeq_zero]; rintro rfl; simp
  case succ i' ih =>
    intro hi u hu
    rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
    · simp at hu
    have hi : i ≤ i' := by simpa using hi
    rcases c.mem_limSeq_succ_iff.mp hu with ⟨hu, Hu⟩
    exact c.mem_limSeq_succ_iff.mpr ⟨_root_.le_trans hu hi, c.monotone (fun z hz ↦ ih hi hz) Hu⟩

lemma mem_limSeq_self [c.StrongFinite] {x i : V} :
    x ∈ c.limSeq v i → x ∈ c.limSeq v (x + 1) := by
  induction x using ISigma1.pi1_order_induction generalizing i
  · apply HierarchySymbol.Definable.all
    apply HierarchySymbol.Definable.imp
    · apply HierarchySymbol.Definable.comp₂
        ⟨φ.limSeqDef.rew <| Rew.embSubsts (#0 :> #1 :> fun j ↦ &(v j)), by intro v; simp [c.eval_limSeqDef]⟩
        (by definability)
    · apply HierarchySymbol.Definable.comp₂
        ⟨φ.limSeqDef.rew <| Rew.embSubsts (#0 :> ‘#2 + 1’ :> fun j ↦ &(v j)), by intro v; simp [c.eval_limSeqDef]⟩
        (by definability)
  case ind x ih =>
    rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
    · simp
    intro hu
    rcases c.mem_limSeq_succ_iff.mp hu with ⟨_, Hu⟩
    have : c.Φ v {z | z ∈ c.limSeq v i ∧ z < x} x := StrongFinite.strong_finite Hu
    have : c.Φ v {z | z ∈ c.limSeq v x} x :=
      c.monotone (by
        simp only [Set.ofPred_subset_ofPred, and_imp]
        intro z hz hzu
        exact c.limSeq_cumulative (succ_le_iff_lt.mpr hzu) (ih z hzu hz))
        this
    exact c.mem_limSeq_succ_iff.mpr ⟨by rfl, this⟩

variable (v)

def Fixpoint (x : V) : Prop := ∃ i, x ∈ c.limSeq v i

variable {v}

lemma fixpoint_iff [c.StrongFinite] {x : V} : c.Fixpoint v x ↔ x ∈ c.limSeq v (x + 1) :=
  ⟨by rintro ⟨i, hi⟩; exact c.mem_limSeq_self hi, fun h ↦ ⟨x + 1, h⟩⟩

lemma fixpoint_iff_succ {x : V} : c.Fixpoint v x ↔ ∃ u, x ∈ c.limSeq v (u + 1) :=
  ⟨by
    rintro ⟨u, h⟩
    rcases zero_or_succ u with (rfl | ⟨u, rfl⟩)
    · simp at h
    · exact ⟨u, h⟩, by rintro ⟨u, h⟩; exact ⟨u + 1, h⟩⟩

lemma finite_upperbound (m : V) : ∃ i, ∀ z < m, c.Fixpoint v z → z ∈ c.limSeq v i := by
  have : ∃ F : V, ∀ x, x ∈ F ↔ x < m ∧ c.Fixpoint v x := by
    have : 𝚺₁-Predicate fun x ↦ x < m ∧ c.Fixpoint v x :=
      HierarchySymbol.Definable.and (by definability)
        (HierarchySymbol.Definable.exs
          (HierarchySymbol.Definable.comp₂
            ⟨φ.limSeqDef.rew <| Rew.embSubsts (#0 :> #1 :> fun j ↦ &(v j)), by intro v; simp [c.eval_limSeqDef]⟩
            (by definability)))
    exact finite_comprehension₁! this ⟨m, fun i hi ↦ hi.1⟩ |>.exists
  rcases this with ⟨F, hF⟩
  have : ∀ x ∈ F, ∃ u, x ∈ c.limSeq v u := by
    intro x hx; exact hF x |>.mp hx |>.2
  have : ∃ f, IsMapping f ∧ domain f = F ∧ ∀ (x y : V), ⟪x, y⟫ ∈ f → x ∈ c.limSeq v y := sigmaOne_skolem
    (by apply HierarchySymbol.Definable.comp₂
          ⟨φ.limSeqDef.rew <| Rew.embSubsts (#0 :> #2 :> fun j ↦ &(v j)), by intro v; simp [c.eval_limSeqDef]⟩
          (by definability)) this
  rcases this with ⟨f, hmf, rfl, hf⟩
  exact ⟨f, by
    intro z hzm hz
    have : ∃ u, ⟪z, u⟫ ∈ f := hmf.get_exists_uniq ((hF z).mpr ⟨hzm, hz⟩) |>.exists
    rcases this with ⟨u, hu⟩
    have : z ∈ c.limSeq v u := hf z u hu
    exact c.limSeq_cumulative (le_of_lt <| lt_of_mem_rng hu) this⟩

theorem case [c.Finite] : c.Fixpoint v x ↔ c.Φ v {z | c.Fixpoint v z} x :=
  ⟨by intro h
      rcases c.fixpoint_iff_succ.mp h with ⟨u, hu⟩
      have : c.Φ v {z | z ∈ c.limSeq v u} x := (c.mem_limSeq_succ_iff.mp hu).2
      exact c.monotone (fun z hx ↦ by exact ⟨u, hx⟩) this,
   by intro hx
      rcases Finite.finite hx with ⟨m, hm⟩
      have : ∃ i, ∀ z < m, c.Fixpoint v z → z ∈ c.limSeq v i := c.finite_upperbound m
      rcases this with ⟨i, hi⟩
      have : c.Φ v {z | z ∈ c.limSeq v i} x :=
        c.monotone (by
          simp only [Set.ofPred_subset_ofPred, and_imp]
          intro z hz hzm; exact hi z hzm hz)
          hm
      exact ⟨max i x + 1,
        c.mem_limSeq_succ_iff.mpr <| ⟨by simp, c.monotone (fun z hz ↦ c.limSeq_cumulative (by simp) hz) this⟩⟩⟩

section

lemma fixpoint_defined : 𝚺₁.Defined (fun v ↦ c.Fixpoint (v ·.succ) (v 0)) φ.fixpointDef := .mk fun v ↦ by
  simp [Blueprint.fixpointDef, c.eval_limSeqDef]; rfl

@[simp] lemma eval_fixpointDef (v : Fin (k + 1) → V) :
    φ.fixpointDef.val.Evalb v ↔ c.Fixpoint (v ·.succ) (v 0) := c.fixpoint_defined.iff

lemma fixpoint_definedΔ₁ [c.StrongFinite] : 𝚫₁.Defined (fun v ↦ c.Fixpoint (v ·.succ) (v 0)) φ.fixpointDefΔ₁ :=
  ⟨by intro v; simp [Blueprint.fixpointDefΔ₁, c.eval_limSeqDef],
   by intro v; simp [Blueprint.fixpointDefΔ₁, c.eval_limSeqDef, fixpoint_iff]⟩

@[simp] lemma eval_fixpointDefΔ₁ [c.StrongFinite] (v : Fin (k + 1) → V) :
    φ.fixpointDefΔ₁.val.Evalb v ↔ c.Fixpoint (v ·.succ) (v 0) := c.fixpoint_definedΔ₁.iff

end

theorem induction [c.StrongFinite] {P : V → Prop} (hP : Γ-[1]-Predicate P)
    (H : ∀ C : Set V, (∀ x ∈ C, c.Fixpoint v x ∧ P x) → ∀ x, c.Φ v C x → P x) :
    ∀ x, c.Fixpoint v x → P x := by
  apply InductionOnHierarchy.order_induction_sigma (Γ := Γ) (m := 1) (P := fun x ↦ c.Fixpoint v x → P x)
  · apply HierarchySymbol.Definable.imp
      (HierarchySymbol.DefinablePred.comp
        (by
          apply HierarchySymbol.Definable.of_deltaOne
          exact ⟨φ.fixpointDefΔ₁.rew <| Rew.embSubsts <| #0 :> fun x ↦ &(v x), c.fixpoint_definedΔ₁.proper.rew' _,
            by intro v; simp [c.eval_fixpointDefΔ₁]⟩)
        (by definability))
      (by definability)
  intro x ih hx
  have : c.Φ v {y | c.Fixpoint v y ∧ y < x} x := StrongFinite.strong_finite (c.case.mp hx)
  exact H {y | c.Fixpoint v y ∧ y < x} (by intro y ⟨hy, hyx⟩; exact ⟨hy, ih y hyx hy⟩) x this

end Construction

attribute [irreducible] Blueprint.fixpointDef

end Fixpoint

end LO.FirstOrder.Arithmetic
