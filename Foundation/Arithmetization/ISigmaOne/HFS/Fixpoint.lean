import Foundation.Arithmetization.ISigmaOne.HFS.PRF

/-!

# Fixpoint Construction

-/

noncomputable section

namespace LO.Arith

open FirstOrder FirstOrder.Arith

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

namespace Fixpoint

structure Blueprint (k : ℕ) where
  core : 𝚫₁.Semisentence (k + 2)

namespace Blueprint

variable {k} (φ : Blueprint k)

instance : Coe (Blueprint k) (𝚫₁.Semisentence (k + 2)) := ⟨Blueprint.core⟩

def succDef : 𝚺₁.Semisentence (k + 3) := .mkSigma
  “u ih s. ∀ x < u + (s + 1), (x ∈ u → x ≤ s ∧ !φ.core.sigma x ih ⋯) ∧ (x ≤ s ∧ !φ.core.pi x ih ⋯ → x ∈ u)” (by simp)

def prBlueprint : PR.Blueprint k where
  zero := .mkSigma “x. x = 0” (by simp)
  succ := φ.succDef

def limSeqDef : 𝚺₁.Semisentence (k + 2) := (φ.prBlueprint).resultDef

def fixpointDef : 𝚺₁.Semisentence (k + 1) :=
  .mkSigma “x. ∃ s L, !φ.limSeqDef L s ⋯  ∧ x ∈ L” (by simp)

def fixpointDefΔ₁ : 𝚫₁.Semisentence (k + 1) := .mkDelta
  (.mkSigma “x. ∃ L, !φ.limSeqDef L (x + 1) ⋯  ∧ x ∈ L” (by simp))
  (.mkPi “x. ∀ L, !φ.limSeqDef L (x + 1) ⋯  → x ∈ L” (by simp))

end Blueprint

variable (V)

structure Construction {k : ℕ} (φ : Blueprint k) where
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
    Semiformula.Evalbm V v φ.core.val ↔ c.Φ (v ·.succ.succ) {x | x ∈ v 1} (v 0) := c.defined.df.iff v

lemma succ_existsUnique (s ih : V) :
    ∃! u : V, ∀ x, (x ∈ u ↔ x ≤ s ∧ c.Φ v {z | z ∈ ih} x) := by
  have : 𝚺₁-Predicate fun x ↦ x ≤ s ∧ c.Φ v {z | z ∈ ih} x := by
    apply HierarchySymbol.Boldface.and (by definability)
      ⟨φ.core.sigma.rew <| Rew.embSubsts (#0 :> &ih :> fun i ↦ &(v i)),
        by intro x; simp [HierarchySymbol.Semiformula.val_sigma, c.eval_formula]⟩
  exact finite_comprehension₁! this
    ⟨s + 1, fun i ↦ by rintro ⟨hi, _⟩; exact lt_succ_iff_le.mpr hi⟩

def succ (s ih : V) : V := Classical.choose! (c.succ_existsUnique v s ih)

variable {v}

lemma mem_succ_iff {v s ih} :
    x ∈ c.succ v s ih ↔ x ≤ s ∧ c.Φ v {z | z ∈ ih} x := Classical.choose!_spec (c.succ_existsUnique v s ih) x

private lemma succ_graph {u v s ih} :
    u = c.succ v s ih ↔ ∀ x < u + (s + 1), x ∈ u ↔ x ≤ s ∧ c.Φ v {z | z ∈ ih} x :=
  ⟨by rintro rfl x _; simp [mem_succ_iff], by
    intro h; apply mem_ext
    intro x; constructor
    · intro hx; exact c.mem_succ_iff.mpr <| h x (lt_of_lt_of_le (lt_of_mem hx) (by simp)) |>.mp hx
    · intro hx
      exact h x (lt_of_lt_of_le (lt_succ_iff_le.mpr (c.mem_succ_iff.mp hx).1)
        (by simp)) |>.mpr (c.mem_succ_iff.mp hx)⟩

lemma succ_defined : 𝚺₁.DefinedFunction (fun v : Fin (k + 2) → V ↦ c.succ (v ·.succ.succ) (v 1) (v 0)) φ.succDef := by
  intro v
  simp [Blueprint.succDef, succ_graph, HierarchySymbol.Semiformula.val_sigma, c.eval_formula,
    c.defined.proper.iff', -and_imp, ←iff_iff_implies_and_implies]

lemma eval_succDef (v) :
    Semiformula.Evalbm V v φ.succDef.val ↔ v 0 = c.succ (v ·.succ.succ.succ) (v 2) (v 1) := c.succ_defined.df.iff v

def prConstruction : PR.Construction V φ.prBlueprint where
  zero := fun _ ↦ ∅
  succ := c.succ
  zero_defined := by intro v; simp [Blueprint.prBlueprint, emptyset_def]
  succ_defined := by intro v; simp [Blueprint.prBlueprint, c.eval_succDef]

variable (v)

def limSeq (s : V) : V := c.prConstruction.result v s

variable {v}

@[simp] lemma limSeq_zero : c.limSeq v 0 = ∅ := by simp [limSeq, prConstruction]

lemma limSeq_succ (s : V) : c.limSeq v (s + 1) = c.succ v s (c.limSeq v s) := by simp [limSeq, prConstruction]

lemma termSet_defined : 𝚺₁.DefinedFunction (fun v ↦ c.limSeq (v ·.succ) (v 0)) φ.limSeqDef :=
  fun v ↦ by simp [c.prConstruction.result_defined_iff, Blueprint.limSeqDef]; rfl

@[simp] lemma eval_limSeqDef (v) :
    Semiformula.Evalbm V v φ.limSeqDef.val ↔ v 0 = c.limSeq (v ·.succ.succ) (v 1) := c.termSet_defined.df.iff v

instance limSeq_definable :
  𝚺₁.BoldfaceFunction (fun v ↦ c.limSeq (v ·.succ) (v 0)) := c.termSet_defined.to_definable

@[simp, definability] instance limSeq_definable' (Γ) : Γ-[m + 1].BoldfaceFunction (fun v ↦ c.limSeq (v ·.succ) (v 0)) := c.limSeq_definable.of_sigmaOne

lemma mem_limSeq_succ_iff {x s : V} :
    x ∈ c.limSeq v (s + 1) ↔ x ≤ s ∧ c.Φ v {z | z ∈ c.limSeq v s} x := by simp [limSeq_succ, mem_succ_iff]

lemma limSeq_cumulative {s s' : V} : s ≤ s' → c.limSeq v s ⊆ c.limSeq v s' := by
  induction s' using ISigma1.sigma1_succ_induction generalizing s
  · apply HierarchySymbol.Boldface.ball_le (by definability)
    apply HierarchySymbol.Boldface.comp₂
    · exact ⟨φ.limSeqDef.rew <| Rew.embSubsts (#0 :> #1 :> fun i ↦ &(v i)), by intro v; simp [c.eval_limSeqDef]⟩
    · exact ⟨φ.limSeqDef.rew <| Rew.embSubsts (#0 :> #2 :> fun i ↦ &(v i)), by intro v; simp [c.eval_limSeqDef]⟩
  case zero =>
    simp; rintro rfl; simp
  case succ s' ih =>
    intro hs u hu
    rcases zero_or_succ s with (rfl | ⟨s, rfl⟩)
    · simp at hu
    have hs : s ≤ s' := by simpa using hs
    rcases c.mem_limSeq_succ_iff.mp hu with ⟨hu, Hu⟩
    exact c.mem_limSeq_succ_iff.mpr ⟨_root_.le_trans hu hs, c.monotone (fun z hz ↦ ih hs hz) Hu⟩

lemma mem_limSeq_self [c.StrongFinite] {u s : V} :
    u ∈ c.limSeq v s → u ∈ c.limSeq v (u + 1) := by
  induction u using ISigma1.pi1_order_induction generalizing s
  · apply HierarchySymbol.Boldface.all
    apply HierarchySymbol.Boldface.imp
    · apply HierarchySymbol.Boldface.comp₂
        ⟨φ.limSeqDef.rew <| Rew.embSubsts (#0 :> #1 :> fun i ↦ &(v i)), by intro v; simp [c.eval_limSeqDef]⟩
        (by definability)
    · apply HierarchySymbol.Boldface.comp₂
        ⟨φ.limSeqDef.rew <| Rew.embSubsts (#0 :> ‘#2 + 1’ :> fun i ↦ &(v i)), by intro v; simp [c.eval_limSeqDef]⟩
        (by definability)
  case ind u ih =>
    rcases zero_or_succ s with (rfl | ⟨s, rfl⟩)
    · simp
    intro hu
    rcases c.mem_limSeq_succ_iff.mp hu with ⟨_, Hu⟩
    have : c.Φ v {z | z ∈ c.limSeq v s ∧ z < u} u := StrongFinite.strong_finite Hu
    have : c.Φ v {z | z ∈ c.limSeq v u} u :=
      c.monotone (by
        simp only [Set.setOf_subset_setOf, and_imp]
        intro z hz hzu
        exact c.limSeq_cumulative (succ_le_iff_lt.mpr hzu) (ih z hzu hz))
        this
    exact c.mem_limSeq_succ_iff.mpr ⟨by rfl, this⟩

variable (v)

def Fixpoint (x : V) : Prop := ∃ s, x ∈ c.limSeq v s

variable {v}

lemma fixpoint_iff [c.StrongFinite] {x : V} : c.Fixpoint v x ↔ x ∈ c.limSeq v (x + 1) :=
  ⟨by rintro ⟨s, hs⟩; exact c.mem_limSeq_self hs, fun h ↦ ⟨x + 1, h⟩⟩

lemma fixpoint_iff_succ {x : V} : c.Fixpoint v x ↔ ∃ u, x ∈ c.limSeq v (u + 1) :=
  ⟨by
    rintro ⟨u, h⟩
    rcases zero_or_succ u with (rfl | ⟨u, rfl⟩)
    · simp at h
    · exact ⟨u, h⟩, by rintro ⟨u, h⟩; exact ⟨u + 1, h⟩⟩

lemma finite_upperbound (m : V) : ∃ s, ∀ z < m, c.Fixpoint v z → z ∈ c.limSeq v s := by
  have : ∃ F : V, ∀ x, x ∈ F ↔ x < m ∧ c.Fixpoint v x := by
    have : 𝚺₁-Predicate fun x ↦ x < m ∧ c.Fixpoint v x :=
      HierarchySymbol.Boldface.and (by definability)
        (HierarchySymbol.Boldface.ex
          (HierarchySymbol.Boldface.comp₂
            ⟨φ.limSeqDef.rew <| Rew.embSubsts (#0 :> #1 :> fun i ↦ &(v i)), by intro v; simp [c.eval_limSeqDef]⟩
            (by definability)))
    exact finite_comprehension₁! this ⟨m, fun i hi ↦ hi.1⟩ |>.exists
  rcases this with ⟨F, hF⟩
  have : ∀ x ∈ F, ∃ u, x ∈ c.limSeq v u := by
    intro x hx; exact hF x |>.mp hx |>.2
  have : ∃ f, IsMapping f ∧ domain f = F ∧ ∀ (x y : V), ⟪x, y⟫ ∈ f → x ∈ c.limSeq v y := sigmaOne_skolem
    (by apply HierarchySymbol.Boldface.comp₂
          ⟨φ.limSeqDef.rew <| Rew.embSubsts (#0 :> #2 :> fun i ↦ &(v i)), by intro v; simp [c.eval_limSeqDef]⟩
          (by definability)) this
  rcases this with ⟨f, mf, rfl, hf⟩
  exact ⟨f, by
    intro z hzm hz
    have : ∃ u, ⟪z, u⟫ ∈ f := mf.get_exists_uniq ((hF z).mpr ⟨hzm, hz⟩) |>.exists
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
      simp at hm
      have : ∃ s, ∀ z < m, c.Fixpoint v z → z ∈ c.limSeq v s := c.finite_upperbound m
      rcases this with ⟨s, hs⟩
      have : c.Φ v {z | z ∈ c.limSeq v s} x :=
        c.monotone (by
          simp only [Set.setOf_subset_setOf, and_imp]
          intro z hz hzm; exact hs z hzm hz)
          hm
      exact ⟨max s x + 1,
        c.mem_limSeq_succ_iff.mpr <| ⟨by simp, c.monotone (fun z hz ↦ c.limSeq_cumulative (by simp) hz) this⟩⟩⟩

section

lemma fixpoint_defined : 𝚺₁.Defined (fun v ↦ c.Fixpoint (v ·.succ) (v 0)) φ.fixpointDef := by
  intro v; simp [Blueprint.fixpointDef, c.eval_limSeqDef]; rfl

@[simp] lemma eval_fixpointDef (v) :
    Semiformula.Evalbm V v φ.fixpointDef.val ↔ c.Fixpoint (v ·.succ) (v 0) := c.fixpoint_defined.df.iff v

lemma fixpoint_definedΔ₁ [c.StrongFinite] : 𝚫₁.Defined (fun v ↦ c.Fixpoint (v ·.succ) (v 0)) φ.fixpointDefΔ₁ :=
  ⟨by intro v; simp [Blueprint.fixpointDefΔ₁, c.eval_limSeqDef],
   by intro v; simp [Blueprint.fixpointDefΔ₁, c.eval_limSeqDef, fixpoint_iff]⟩

@[simp] lemma eval_fixpointDefΔ₁ [c.StrongFinite] (v) :
    Semiformula.Evalbm V v φ.fixpointDefΔ₁.val ↔ c.Fixpoint (v ·.succ) (v 0) := c.fixpoint_definedΔ₁.df.iff v

end

theorem induction [c.StrongFinite] {P : V → Prop} (hP : Γ-[1]-Predicate P)
    (H : ∀ C : Set V, (∀ x ∈ C, c.Fixpoint v x ∧ P x) → ∀ x, c.Φ v C x → P x) :
    ∀ x, c.Fixpoint v x → P x := by
  apply order_induction_sigma (Γ := Γ) (m := 1) (P := fun x ↦ c.Fixpoint v x → P x)
  · apply HierarchySymbol.Boldface.imp
      (HierarchySymbol.BoldfacePred.comp
        (by
          apply HierarchySymbol.Boldface.of_deltaOne
          exact ⟨φ.fixpointDefΔ₁.rew <| Rew.embSubsts <| #0 :> fun x ↦ &(v x), c.fixpoint_definedΔ₁.proper.rew' _,
            by intro v; simp [c.eval_fixpointDefΔ₁]⟩)
        (by definability))
      (by definability)
  intro x ih hx
  have : c.Φ v {y | c.Fixpoint v y ∧ y < x} x := StrongFinite.strong_finite (c.case.mp hx)
  exact H {y | c.Fixpoint v y ∧ y < x} (by intro y ⟨hy, hyx⟩; exact ⟨hy, ih y hyx hy⟩) x this

end Construction

end Fixpoint

end LO.Arith

end
