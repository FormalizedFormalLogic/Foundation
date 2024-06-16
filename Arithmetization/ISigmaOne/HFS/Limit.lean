import Arithmetization.ISigmaOne.HFS.PRF

/-!

# Limit Construction

-/

noncomputable section

namespace LO.FirstOrder.Arith.Model

variable {M : Type*} [Zero M] [One M] [Add M] [Mul M] [LT M] [M ⊧ₘ* 𝐈𝚺₁]

namespace Limit

structure Formula (k : ℕ) where
  core : 𝚫₁-Semisentence (k + 2)

namespace Formula

variable {k} (φ : Formula k)

instance : Coe (Formula k) (𝚫₁-Semisentence (k + 2)) := ⟨Formula.core⟩

def succDef : 𝚺₁-Semisentence (k + 3) := .mkSigma
  “u ih s | ∀ x < u + (s + 1), (x ∈ u → x ≤ s ∧ !φ.core.sigma x ih ⋯) ∧ (x ≤ s ∧ !φ.core.pi x ih ⋯ → x ∈ u)” (by simp)

def prFormulae : PR.Formulae k where
  zero := .mkSigma “x | x = 0” (by simp)
  succ := φ.succDef

def limSeqDef : 𝚺₁-Semisentence (k + 2) := (φ.prFormulae).resultDef

def limitDef : 𝚫₁-Semisentence (k + 1) := .mkDelta
  (.mkSigma “x | ∃ L, !φ.limSeqDef L (x + 1) ⋯  ∧ x ∈ L” (by simp))
  (.mkPi “x | ∀ L, !φ.limSeqDef L (x + 1) ⋯  → x ∈ L” (by simp))

end Formula

variable (M)

structure Construction {k : ℕ} (φ : Formula k) where
  Φ : (Fin k → M) → Set M → M → Prop
  defined : Defined (fun v ↦ Φ (v ·.succ.succ) {x | x ∈ v 1} (v 0)) φ.core
  monotone {C C' : Set M} (h : C ⊆ C') {v x} : Φ v C x → Φ v C' x
  finite {C : Set M} {v x} : Φ v C x → Φ v {y ∈ C | y < x} x

variable {M}

namespace Construction

variable {k : ℕ} {φ : Formula k} (c : Construction M φ) (v : Fin k → M)

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

lemma succ_defined : DefinedFunction ℒₒᵣ 𝚺₁ (fun v : Fin (k + 2) → M ↦ c.succ (v ·.succ.succ) (v 1) (v 0)) φ.succDef := by
  intro v
  simp [Formula.succDef, succ_graph, HSemiformula.val_sigma, c.eval_formula,
    c.defined.proper.iff', -and_imp, ←iff_iff_implies_and_implies]
  rfl

lemma eval_succDef (v) :
    Semiformula.Evalbm M v φ.succDef.val ↔ v 0 = c.succ (v ·.succ.succ.succ) (v 2) (v 1) := c.succ_defined.df.iff v

def prConstruction : PR.Construction M φ.prFormulae where
  zero := fun _ ↦ ∅
  succ := c.succ
  zero_defined := by intro v; simp [Formula.prFormulae, emptyset_def]
  succ_defined := by intro v; simp [Formula.prFormulae, c.eval_succDef]; rfl

variable (v)

def limSeq (s : M) : M := c.prConstruction.result v s

variable {v}

@[simp] lemma limSeq_zero : c.limSeq v 0 = ∅ := by simp [limSeq, prConstruction]

lemma limSeq_succ (s : M) : c.limSeq v (s + 1) = c.succ v s (c.limSeq v s) := by simp [limSeq, prConstruction]

lemma termSet_defined : DefinedFunction ℒₒᵣ 𝚺₁ (fun v ↦ c.limSeq (v ·.succ) (v 0)) φ.limSeqDef :=
  fun v ↦ by simp [c.prConstruction.result_defined_iff, Formula.limSeqDef]; rfl

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
    apply Definable.comp₂'
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

lemma mem_limSeq_self {u s : M} :
    u ∈ c.limSeq v s → u ∈ c.limSeq v (u + 1) := by
  induction u using order_induction_piOne generalizing s
  · apply Definable.all
    apply Definable.imp
    · apply Definable.comp₂' (by definability)
      exact ⟨φ.limSeqDef.rew <| Rew.embSubsts (#0 :> #1 :> fun i ↦ &(v i)), by intro v; simp [c.eval_limSeqDef]⟩
    · apply Definable.comp₂' (by definability)
      exact ⟨φ.limSeqDef.rew <| Rew.embSubsts (#0 :> ‘#2 + 1’ :> fun i ↦ &(v i)), by intro v; simp [c.eval_limSeqDef]⟩
  case ind u ih =>
    rcases zero_or_succ s with (rfl | ⟨s, rfl⟩)
    · simp
    intro hu
    rcases c.mem_limSeq_succ_iff.mp hu with ⟨_, Hu⟩
    have : c.Φ v {z | z ∈ c.limSeq v s ∧ z < u} u := c.finite Hu
    have : c.Φ v {z | z ∈ c.limSeq v u} u :=
      c.monotone (by
        simp only [Set.setOf_subset_setOf, and_imp]
        intro z hz hzu
        exact c.limSeq_cumulative (succ_le_iff_lt.mpr hzu) (ih z hzu hz))
        this
    exact c.mem_limSeq_succ_iff.mpr ⟨by rfl, this⟩

variable (v)

def Limit (x : M) : Prop := ∃ s, x ∈ c.limSeq v s

variable {v}

lemma limit_iff {x : M} : c.Limit v x ↔ x ∈ c.limSeq v (x + 1) :=
  ⟨by rintro ⟨s, hs⟩; exact c.mem_limSeq_self hs, fun h ↦ ⟨x + 1, h⟩⟩

theorem fixpoint :
    c.Limit v x ↔ c.Φ v {z | c.Limit v z} x :=
  ⟨by rintro h
      have : c.Φ v {z | z ∈ c.limSeq v x} x := (c.mem_limSeq_succ_iff.mp (c.limit_iff.mp h)).2
      exact c.monotone (fun z hx ↦ by exact ⟨x, hx⟩) this,
   by intro hx
      have : c.Φ v {z | z ∈ c.limSeq v x} x :=
        c.monotone (by
          simp only [Set.setOf_subset_setOf, and_imp]
          intro z hz hzx
          exact c.limSeq_cumulative (succ_le_iff_lt.mpr hzx) (c.limit_iff.mp hz))
          (c.finite hx)
      exact ⟨x + 1, c.mem_limSeq_succ_iff.mpr <| ⟨by rfl, this⟩⟩⟩

section

lemma limit_defined : Defined (fun v ↦ c.Limit (v ·.succ) (v 0)) φ.limitDef :=
  ⟨by intro v; simp [Formula.limitDef, c.eval_limSeqDef],
   by intro v; simp [Formula.limitDef, c.eval_limSeqDef, limit_iff]⟩

@[simp] lemma eval_limitDef (v) :
    Semiformula.Evalbm M v φ.limitDef.val ↔ c.Limit (v ·.succ) (v 0) := c.limit_defined.df.iff v

end

end Construction

end Limit

end LO.FirstOrder.Arith.Model

end
