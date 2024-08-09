import Arithmetization.ISigmaOne.HFS.PRF

/-!

# Fixpoint Construction

-/

noncomputable section

namespace LO.Arith

open FirstOrder FirstOrder.Arith

variable {M : Type*} [Zero M] [One M] [Add M] [Mul M] [LT M] [M ⊧ₘ* 𝐈𝚺₁]

namespace Fixpoint

structure Blueprint (k : ℕ) where
  core : 𝚫₁-Semisentence (k + 2)

namespace Blueprint

variable {k} (φ : Blueprint k)

instance : Coe (Blueprint k) (𝚫₁-Semisentence (k + 2)) := ⟨Blueprint.core⟩

def succDef : 𝚺₁-Semisentence (k + 3) := .mkSigma
  “u ih s | ∀ x < u + (s + 1), (x ∈ u → x ≤ s ∧ !φ.core.sigma x ih ⋯) ∧ (x ≤ s ∧ !φ.core.pi x ih ⋯ → x ∈ u)” (by simp)

def prBlueprint : PR.Blueprint k where
  zero := .mkSigma “x | x = 0” (by simp)
  succ := φ.succDef

def limSeqDef : 𝚺₁-Semisentence (k + 2) := (φ.prBlueprint).resultDef

def fixpointDef : 𝚺₁-Semisentence (k + 1) :=
  .mkSigma “x | ∃ s L, !φ.limSeqDef L s ⋯  ∧ x ∈ L” (by simp)

def fixpointDefΔ₁ : 𝚫₁-Semisentence (k + 1) := .mkDelta
  (.mkSigma “x | ∃ L, !φ.limSeqDef L (x + 1) ⋯  ∧ x ∈ L” (by simp))
  (.mkPi “x | ∀ L, !φ.limSeqDef L (x + 1) ⋯  → x ∈ L” (by simp))

end Blueprint

variable (M)

structure Construction {k : ℕ} (φ : Blueprint k) where
  Φ : (Fin k → M) → Set M → M → Prop
  defined : Arith.Defined (fun v ↦ Φ (v ·.succ.succ) {x | x ∈ v 1} (v 0)) φ.core
  monotone {C C' : Set M} (h : C ⊆ C') {v x} : Φ v C x → Φ v C' x

class Construction.Finite {k : ℕ} {φ : Blueprint k} (c : Construction M φ) where
  finite {C : Set M} {v x} : c.Φ v C x → ∃ m, c.Φ v {y ∈ C | y < m} x

class Construction.StrongFinite {k : ℕ} {φ : Blueprint k} (c : Construction M φ) where
  strong_finite {C : Set M} {v x} : c.Φ v C x → c.Φ v {y ∈ C | y < x} x

instance {k : ℕ} {φ : Blueprint k} (c : Construction M φ) [c.StrongFinite] : c.Finite where
  finite {_ _ x} := fun h ↦ ⟨x, Construction.StrongFinite.strong_finite h⟩

variable {M}

namespace Construction

variable {k : ℕ} {φ : Blueprint k} (c : Construction M φ) (v : Fin k → M)

lemma eval_formula (v : Fin k.succ.succ → M) :
    Semiformula.Evalbm M v (HSemiformula.val φ.core) ↔ c.Φ (v ·.succ.succ) {x | x ∈ v 1} (v 0) := c.defined.df.iff v

lemma succ_existsUnique (s ih : M) :
    ∃! u : M, ∀ x, (x ∈ u ↔ x ≤ s ∧ c.Φ v {z | z ∈ ih} x) := by
  have : 𝚺₁-Predicate fun x ↦ x ≤ s ∧ c.Φ v {z | z ∈ ih} x := by
    apply Definable.and (by definability)
      ⟨φ.core.sigma.rew <| Rew.embSubsts (#0 :> &ih :> fun i ↦ &(v i)),
        by intro x; simp [HSemiformula.val_sigma, c.eval_formula]⟩
  exact finite_comprehension₁! this
    ⟨s + 1, fun i ↦ by rintro ⟨hi, _⟩; exact lt_succ_iff_le.mpr hi⟩

def succ (s ih : M) : M := Classical.choose! (c.succ_existsUnique v s ih)

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

lemma succ_defined : DefinedFunction (fun v : Fin (k + 2) → M ↦ c.succ (v ·.succ.succ) (v 1) (v 0)) φ.succDef := by
  intro v
  simp [Blueprint.succDef, succ_graph, HSemiformula.val_sigma, c.eval_formula,
    c.defined.proper.iff', -and_imp, ←iff_iff_implies_and_implies]
  rfl

lemma eval_succDef (v) :
    Semiformula.Evalbm M v φ.succDef.val ↔ v 0 = c.succ (v ·.succ.succ.succ) (v 2) (v 1) := c.succ_defined.df.iff v

def prConstruction : PR.Construction M φ.prBlueprint where
  zero := fun _ ↦ ∅
  succ := c.succ
  zero_defined := by intro v; simp [Blueprint.prBlueprint, emptyset_def]
  succ_defined := by intro v; simp [Blueprint.prBlueprint, c.eval_succDef]; rfl

variable (v)

def limSeq (s : M) : M := c.prConstruction.result v s

variable {v}

@[simp] lemma limSeq_zero : c.limSeq v 0 = ∅ := by simp [limSeq, prConstruction]

lemma limSeq_succ (s : M) : c.limSeq v (s + 1) = c.succ v s (c.limSeq v s) := by simp [limSeq, prConstruction]

lemma termSet_defined : DefinedFunction (fun v ↦ c.limSeq (v ·.succ) (v 0)) φ.limSeqDef :=
  fun v ↦ by simp [c.prConstruction.result_defined_iff, Blueprint.limSeqDef]; rfl

@[simp] lemma eval_limSeqDef (v) :
    Semiformula.Evalbm M v φ.limSeqDef.val ↔ v 0 = c.limSeq (v ·.succ.succ) (v 1) := c.termSet_defined.df.iff v

instance limSeq_definable :
  DefinableFunction ℒₒᵣ 𝚺₁ (fun v ↦ c.limSeq (v ·.succ) (v 0)) := Defined.to_definable _ c.termSet_defined

@[simp, definability] instance limSeq_definable' (Γ) :
    DefinableFunction ℒₒᵣ (Γ, m + 1) (fun v ↦ c.limSeq (v ·.succ) (v 0))  :=
  .of_sigmaOne c.limSeq_definable _ _

lemma mem_limSeq_succ_iff {x s : M} :
    x ∈ c.limSeq v (s + 1) ↔ x ≤ s ∧ c.Φ v {z | z ∈ c.limSeq v s} x := by simp [limSeq_succ, mem_succ_iff]

lemma limSeq_cumulative {s s' : M} : s ≤ s' → c.limSeq v s ⊆ c.limSeq v s' := by
  induction s' using induction_iSigmaOne generalizing s
  · apply Definable.ball_le' (by definability)
    apply Definable.comp₂_infer
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

lemma mem_limSeq_self [c.StrongFinite] {u s : M} :
    u ∈ c.limSeq v s → u ∈ c.limSeq v (u + 1) := by
  induction u using order_induction_piOne generalizing s
  · apply Definable.all
    apply Definable.imp
    · apply Definable.comp₂_infer (by definability)
      exact ⟨φ.limSeqDef.rew <| Rew.embSubsts (#0 :> #1 :> fun i ↦ &(v i)), by intro v; simp [c.eval_limSeqDef]⟩
    · apply Definable.comp₂_infer (by definability)
      exact ⟨φ.limSeqDef.rew <| Rew.embSubsts (#0 :> ‘#2 + 1’ :> fun i ↦ &(v i)), by intro v; simp [c.eval_limSeqDef]⟩
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

def Fixpoint (x : M) : Prop := ∃ s, x ∈ c.limSeq v s

variable {v}

lemma fixpoint_iff [c.StrongFinite] {x : M} : c.Fixpoint v x ↔ x ∈ c.limSeq v (x + 1) :=
  ⟨by rintro ⟨s, hs⟩; exact c.mem_limSeq_self hs, fun h ↦ ⟨x + 1, h⟩⟩

lemma fixpoint_iff_succ {x : M} : c.Fixpoint v x ↔ ∃ u, x ∈ c.limSeq v (u + 1) :=
  ⟨by
    rintro ⟨u, h⟩
    rcases zero_or_succ u with (rfl | ⟨u, rfl⟩)
    · simp at h
    · exact ⟨u, h⟩, by rintro ⟨u, h⟩; exact ⟨u + 1, h⟩⟩

lemma finite_upperbound (m : M) : ∃ s, ∀ z < m, c.Fixpoint v z → z ∈ c.limSeq v s := by
  have : ∃ F : M, ∀ x, x ∈ F ↔ x < m ∧ c.Fixpoint v x := by
    have : 𝚺₁-Predicate fun x ↦ x < m ∧ c.Fixpoint v x :=
      Definable.and (by definability)
        (Definable.ex (Definable.comp₂_infer (by definability)
          ⟨φ.limSeqDef.rew <| Rew.embSubsts (#0 :> #1 :> fun i ↦ &(v i)), by intro v; simp [c.eval_limSeqDef]⟩))
    exact finite_comprehension₁! this ⟨m, fun i hi ↦ hi.1⟩ |>.exists
  rcases this with ⟨F, hF⟩
  have : ∀ x ∈ F, ∃ u, x ∈ c.limSeq v u := by
    intro x hx; exact hF x |>.mp hx |>.2
  have : ∃ f, IsMapping f ∧ domain f = F ∧ ∀ (x y : M), ⟪x, y⟫ ∈ f → x ∈ c.limSeq v y := sigmaOne_skolem
    (by apply Definable.comp₂_infer (by definability)
        exact ⟨φ.limSeqDef.rew <| Rew.embSubsts (#0 :> #2 :> fun i ↦ &(v i)), by intro v; simp [c.eval_limSeqDef]⟩) this
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

lemma fixpoint_defined : Arith.Defined (fun v ↦ c.Fixpoint (v ·.succ) (v 0)) φ.fixpointDef := by
  intro v; simp [Blueprint.fixpointDef, c.eval_limSeqDef]; rfl

@[simp] lemma eval_fixpointDef (v) :
    Semiformula.Evalbm M v φ.fixpointDef.val ↔ c.Fixpoint (v ·.succ) (v 0) := c.fixpoint_defined.df.iff v

lemma fixpoint_definedΔ₁ [c.StrongFinite] : Arith.Defined (fun v ↦ c.Fixpoint (v ·.succ) (v 0)) φ.fixpointDefΔ₁ :=
  ⟨by intro v; simp [Blueprint.fixpointDefΔ₁, c.eval_limSeqDef],
   by intro v; simp [Blueprint.fixpointDefΔ₁, c.eval_limSeqDef, fixpoint_iff]⟩

@[simp] lemma eval_fixpointDefΔ₁ [c.StrongFinite] (v) :
    Semiformula.Evalbm M v φ.fixpointDefΔ₁.val ↔ c.Fixpoint (v ·.succ) (v 0) := c.fixpoint_definedΔ₁.df.iff v

end

theorem induction [c.StrongFinite] {P : M → Prop} (hP : (Γ, 1)-Predicate P)
    (H : ∀ C : Set M, (∀ x ∈ C, c.Fixpoint v x ∧ P x) → ∀ x, c.Φ v C x → P x) :
    ∀ x, c.Fixpoint v x → P x := by
  apply @order_induction_hh M _ _ _ _ _ _ ℒₒᵣ _ _ _ _ Γ 1 _
  · apply Definable.imp
      (Definable.comp₁ (by definability) (by
        apply Definable.of_deltaOne
        exact ⟨φ.fixpointDefΔ₁.rew <| Rew.embSubsts <| #0 :> fun x ↦ &(v x), c.fixpoint_definedΔ₁.proper.rew' _,
          by intro v; simp [c.eval_fixpointDefΔ₁]⟩))
      (by definability)
  intro x ih hx
  have : c.Φ v {y | c.Fixpoint v y ∧ y < x} x := StrongFinite.strong_finite (c.case.mp hx)
  exact H {y | c.Fixpoint v y ∧ y < x} (by intro y ⟨hy, hyx⟩; exact ⟨hy, ih y hyx hy⟩) x this

/-
theorem pi₁_induction [c.Finite] {P : M → Prop} (hP : 𝚷₁-Predicate P)
    (H : ∀ C : Set M, (∀ x ∈ C, c.Fixpoint v x ∧ P x) → ∀ x, c.Φ v C x → P x) :
    ∀ x, c.Fixpoint v x → P x := by
  apply @order_induction_hh M _ _ _ _ _ _ ℒₒᵣ _ _ _ _ 𝚷 1 _
  · apply Definable.imp
      (Definable.comp₁ (by definability) (by
        exact ⟨φ.fixpointDef.rew <| Rew.embSubsts <| #0 :> fun x ↦ &(v x),
          by intro v; simp [c.eval_fixpointDef]⟩))
      (by definability)
  intro x ih hx
  have := (c.case.mp hx)
  have : c.Φ v {y | c.Fixpoint v y ∧ y < x} x := StrongFinite.strong_finite (c.case.mp hx)
  exact H {y | c.Fixpoint v y ∧ y < x} (by intro y ⟨hy, hyx⟩; exact ⟨hy, ih y hyx hy⟩) x this
-/

end Construction

end Fixpoint

end LO.Arith

end
