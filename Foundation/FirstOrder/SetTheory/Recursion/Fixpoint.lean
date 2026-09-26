module

public import Foundation.FirstOrder.SetTheory.Recursion.Blueprint

@[expose] public section
/-!

# Fixpoint Construction for the recursion theorem in $\mathsf{ZF}$

-/

namespace LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace Fixpoint

-- `Fixpoint` is intentionally re-opened here even though the ambient namespace
-- already contains it; renaming would break the widely-used public API
-- (`Arithmetic.Fixpoint.*`). Suppress the new dupNamespace linter for the
-- declarations in this namespace (the option is scoped by `namespace`/`end` and
-- reverts automatically at `end Fixpoint`).
set_option linter.dupNamespace false

structure Blueprint (k : ℕ) where
  graph : SetTheorySemisentence (k + 2)

namespace Blueprint

variable {k} (φ : Blueprint k)

instance : Coe (Blueprint k) (SetTheorySemisentence (k + 2)) := ⟨Blueprint.graph⟩

-- TODO: Use ∈-recursion along `V` instead of recursion along ordinals to define this, no longer require `x` to be an ordinal.
def mapDef : SetTheorySemisentence (k + 2) :=
  “u ih. ∀ x, (x ∈ u → !IsOrdinal.dfn x ∧ (∀ s, !lh.dfn s ih → x ⊆ s) ∧ !φ.graph x ih ⋯) ∧ (!IsOrdinal.dfn x ∧ (∀ s, !lh.dfn s ih → x ⊆ s) ∧ !φ.graph x ih ⋯ → x ∈ u)”
  -- “u ih α. ∀ x, (x ∈ u → (∀ z, !lh.dfn z α → x ∈ z) ∧ !φ.graph x ih ⋯) ∧ ((∀ z, !lh.dfn z α → x ∈ z) ∧ !φ.graph x ih ⋯ → x ∈ u)”

def recBlueprint : Recursion.Blueprint k where
  graph := φ.mapDef

def limSeqDef : SetTheorySemisentence (k + 2) := (φ.recBlueprint).result_dfn

def fixpointDef : SetTheorySemisentence (k + 1) :=
  “x. ∃ s L, !φ.limSeqDef L s ⋯  ∧ x ∈ L”

end Blueprint

variable (V)

structure Construction {k : ℕ} (φ : Blueprint k) where
  Φ : (Fin k → V) → Set V → V → Prop
  defined : Defined (fun v ↦ Φ (v ·.succ.succ) {x | x ∈ v 1} (v 0)) φ.graph
  monotone {C C' : Set V} (h : C ⊆ C') {v x} : Φ v C x → Φ v C' x

class Construction.SetSized {k : ℕ} {φ : Blueprint k} (c : Construction V φ) where
  set_sized {C : Set V} {v x} : c.Φ v C x → ∃ m : V, c.Φ v {y ∈ C | y ∈ m} x

class Construction.StrongSetSized {k : ℕ} {φ : Blueprint k} (c : Construction V φ) where
  strong_set_sized {C : Set V} {v x} : c.Φ v C x → c.Φ v {y ∈ C | y ∈ x} x

instance {k : ℕ} {φ : Blueprint k} (c : Construction V φ) [c.StrongSetSized] : c.SetSized where
  set_sized {_ _ x} := fun h ↦ ⟨x, Construction.StrongSetSized.strong_set_sized h⟩

variable {V}

namespace Construction

variable {k : ℕ} {φ : Blueprint k} (c : Construction V φ) (v : Fin k → V)

lemma eval_formula (v : Fin k.succ.succ → V) :
    φ.graph.Evalb v ↔ c.Φ (v ·.succ.succ) {x | x ∈ v 1} (v 0) := c.defined.iff v

lemma map_existsUnique (ih : V) :
    ∃! u : V, ∀ x, (x ∈ u ↔ IsOrdinal x ∧ x ⊆ lh ih ∧ c.Φ v {z | z ∈ ih} x) := by
  let s : V := lh ih
  have : IsOrdinal s := isOrdinal_lh ih
  have : ℒₛₑₜ-predicate fun x ↦ IsOrdinal x ∧ x ⊆ s ∧ c.Φ v {z | z ∈ ih} x := by
    refine Language.Definable.and (by definability) (Language.Definable.and (by definability) ?_)
    #check fun x ↦ c.eval_formula (x :> ih :> v)
    exact ⟨φ.graph.rew <| Rew.embSubsts (#0 :> &ih :> fun i ↦ &(v i)),
      by intro x; simp [Semiformula.eval_embSubsts]; sorry⟩
  -- have hsuccs : ∀ (i : V), IsOrdinal i ∧ i ⊆ s → i ∈ SetTheory.succ s :=
  --   fun i ↦ by rintro ⟨_, hi⟩; exact mem_succ_iff.mpr (IsOrdinal.subset_iff.mp hi)
  have hiff (x : V) (p : Prop) : IsOrdinal x ∧ x ⊆ lh ih ∧ p ↔ x ∈ succ s ∧ IsOrdinal x ∧ x ⊆ lh ih ∧ p := by
    constructor <;> intro h
    · exact ⟨mem_succ_iff.mpr (IsOrdinal.subset_iff (hα := h.1).mp h.2.1), h⟩
    · aesop
  conv => {arg 1; intro u x; rw [hiff]}
  exact separation_existsUnique (SetTheory.succ s) _ this

noncomputable def map (ih : V) : V := Classical.choose! (c.map_existsUnique v ih)

variable {v}

lemma mem_map_iff {v ih} :
    x ∈ c.map v ih ↔ IsOrdinal x ∧ x ⊆ lh ih ∧ c.Φ v {z | z ∈ ih} x := Classical.choose!_spec (c.map_existsUnique v ih) x

private lemma map_graph {u v ih} :
    u = c.map v ih ↔ ∀ x, x ∈ u ↔ IsOrdinal x ∧ x ⊆ lh ih ∧ c.Φ v {z | z ∈ ih} x :=
  ⟨by rintro rfl x; simp [mem_map_iff], by
    intro h; apply mem_ext
    intro x; constructor
    · intro hx; exact c.mem_map_iff.mpr ((h x).mp hx)
    · intro hx; exact (h x).mpr (c.mem_map_iff.mp hx)⟩

lemma map_defined : DefinedFunction (fun v : Fin (k + 1) → V ↦ c.map (v ·.succ) (v 0)) φ.mapDef := .mk fun v ↦ by
  simp [Blueprint.mapDef, map_graph, c.eval_formula,
    -and_imp, BinderNotation.finSuccItr]
  grind

lemma map_definable : ℒₛₑₜ-function₁ (c.map v) := Defined.to_definable (c.map_defined)

lemma eval_mapDef (v : Fin (k + 2) → V) :
    φ.mapDef.Evalb v ↔ v 0 = c.map (v ·.succ.succ) (v 1) := c.map_defined.iff v

noncomputable def recConstruction : Recursion.Construction V φ.recBlueprint where
  map := c.map
  map_defined := .mk fun v ↦ by simp [Blueprint.recBlueprint, c.eval_mapDef]

variable (v)

noncomputable def limSeq (s : V) : V := c.recConstruction.result v s

variable {v}

@[simp] lemma limSeq_zero : c.limSeq v 0 = c.map v ∅ := by simp [limSeq, zero_def]; rfl

lemma limSeq_succ (s : V) [hs : IsOrdinal s] : c.limSeq v (succ s) = c.map v (Classical.choose (Replacement.attempt_function_exists (c.map v) (c.map_definable) (IsOrdinal.toOrdinal s).succ)) := by simp [limSeq, c.recConstruction.result_succ v s]; rfl

lemma termSet_defined : DefinedFunction (fun v ↦ c.limSeq (v ·.succ) (v 0)) φ.limSeqDef := .mk
  fun v ↦ by simp [c.recConstruction.result_defined_iff, Blueprint.limSeqDef]; rfl

@[simp] lemma eval_limSeqDef (v : Fin (k + 2) → V) :
    φ.limSeqDef.Evalb v ↔ v 0 = c.limSeq (v ·.succ.succ) (v 1) := c.termSet_defined.iff v

instance limSeq_definable :
  (ℒₛₑₜ).DefinableFunction (fun v ↦ c.limSeq (v ·.succ) (v 0)) := c.termSet_defined.to_definable

/- TODO: Once the Lévy hierarchy is added, make a version relative to a hierarchy symbol. -/
-- @[simp, definability] instance limSeq_definable' (Γ) : Γ-[m + 1].DefinableFunction (fun v ↦ c.limSeq (v ·.succ) (v 0)) := c.limSeq_definable.of_sigmaOne

lemma mem_limSeq_succ_iff {x s : V} [IsOrdinal s] :
    x ∈ c.limSeq v (succ s) ↔ IsOrdinal x ∧ x ⊆ s ∧ c.Φ v {z | z ∈ c.limSeq v s} x := by simp [limSeq_succ, mem_succ_iff]

lemma limSeq_cumulative {s s' : V} [IsOrdinal s] [IsOrdinal s'] : s ⊆ s' → c.limSeq v s ⊆ c.limSeq v s' := by
  let s'o : Ordinal V := IsOrdinal.toOrdinal s'
  let motive (s' : V) : Prop := s ⊆ s' → c.limSeq v s ⊆ c.limSeq v s'
  refine transfinite_induction motive ?_ ?_ s'o
  · unfold Language.DefinablePred
    apply Language.Definable.imp (by definability)
    apply Language.Definable.all
    apply Language.Definable.imp (by definability)
    apply Language.DefinableRel.comp
    · exact ⟨φ.limSeqDef.rew <| Rew.embSubsts (#0 :> #1 :> fun i ↦ &(v i)), by intro v; simp only; simp [c.eval_limSeqDef]⟩
    · exact ⟨φ.limSeqDef.rew <| Rew.embSubsts (#0 :> #2 :> fun i ↦ &(v i)), by intro v; simp [c.eval_limSeqDef]⟩
  · intro s'o ih hsso z hz
    simp_all [limSeq]
    obtain ⟨f, hf, hlhf, hmemf⟩ := c.recConstruction.result_spec_of_isOrdinal v s

    sorry
  -- case zero =>
  --   simp only [nonpos_iff_eq_zero, limSeq_zero]; rintro rfl; simp
  -- case succ s' ih =>
  --   intro hs u hu
  --   rcases zero_or_succ s with (rfl | ⟨s, rfl⟩)
  --   · simp at hu
  --   have hs : s ≤ s' := by simpa using hs
  --   rcases c.mem_limSeq_succ_iff.mp hu with ⟨hu, Hu⟩
  --   exact c.mem_limSeq_succ_iff.mpr ⟨_root_.le_trans hu hs, c.monotone (fun z hz ↦ ih hs hz) Hu⟩

lemma mem_limSeq_self [c.StrongSetSized] {u s : V} :
    u ∈ c.limSeq v s → u ∈ c.limSeq v (succ u) := by
  induction u using ISigma1.pi1_order_induction generalizing s
  · apply HierarchySymbol.Definable.all
    apply HierarchySymbol.Definable.imp
    · apply HierarchySymbol.Definable.comp₂
        ⟨φ.limSeqDef.rew <| Rew.embSubsts (#0 :> #1 :> fun i ↦ &(v i)), by intro v; simp [c.eval_limSeqDef]⟩
        (by definability)
    · apply HierarchySymbol.Definable.comp₂
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

lemma fixpoint_iff [c.StrongSetSized] {x : V} : c.Fixpoint v x ↔ x ∈ c.limSeq v (x + 1) :=
  ⟨by rintro ⟨s, hs⟩; exact c.mem_limSeq_self hs, fun h ↦ ⟨x + 1, h⟩⟩

lemma fixpoint_iff_succ {x : V} : c.Fixpoint v x ↔ ∃ u, x ∈ c.limSeq v (u + 1) :=
  ⟨by
    rintro ⟨u, h⟩
    rcases zero_or_succ u with (rfl | ⟨u, rfl⟩)
    · simp at h
    · exact ⟨u, h⟩, by rintro ⟨u, h⟩; exact ⟨u + 1, h⟩⟩

lemma set_sized_upperbound (m : V) : ∃ s, ∀ z < m, c.Fixpoint v z → z ∈ c.limSeq v s := by
  have : ∃ F : V, ∀ x, x ∈ F ↔ x < m ∧ c.Fixpoint v x := by
    have : Predicate fun x ↦ x < m ∧ c.Fixpoint v x :=
      HierarchySymbol.Definable.and (by definability)
        (HierarchySymbol.Definable.exs
          (HierarchySymbol.Definable.comp₂
            ⟨φ.limSeqDef.rew <| Rew.embSubsts (#0 :> #1 :> fun i ↦ &(v i)), by intro v; simp [c.eval_limSeqDef]⟩
            (by definability)))
    exact finite_comprehension₁! this ⟨m, fun i hi ↦ hi.1⟩ |>.exists
  rcases this with ⟨F, hF⟩
  have : ∀ x ∈ F, ∃ u, x ∈ c.limSeq v u := by
    intro x hx; exact hF x |>.mp hx |>.2
  have : ∃ f, IsMapping f ∧ domain f = F ∧ ∀ (x y : V), ⟪x, y⟫ ∈ f → x ∈ c.limSeq v y := sigmaOne_skolem
    (by apply HierarchySymbol.Definable.comp₂
          ⟨φ.limSeqDef.rew <| Rew.embSubsts (#0 :> #2 :> fun i ↦ &(v i)), by intro v; simp [c.eval_limSeqDef]⟩
          (by definability)) this
  rcases this with ⟨f, mf, rfl, hf⟩
  exact ⟨f, by
    intro z hzm hz
    have : ∃ u, ⟪z, u⟫ ∈ f := mf.get_exists_uniq ((hF z).mpr ⟨hzm, hz⟩) |>.exists
    rcases this with ⟨u, hu⟩
    have : z ∈ c.limSeq v u := hf z u hu
    exact c.limSeq_cumulative (le_of_lt <| lt_of_mem_rng hu) this⟩

theorem case [c.SetSized] : c.Fixpoint v x ↔ c.Φ v {z | c.Fixpoint v z} x :=
  ⟨by intro h
      rcases c.fixpoint_iff_succ.mp h with ⟨u, hu⟩
      have : c.Φ v {z | z ∈ c.limSeq v u} x := (c.mem_limSeq_succ_iff.mp hu).2
      exact c.monotone (fun z hx ↦ by exact ⟨u, hx⟩) this,
   by intro hx
      rcases SetSized.set_sized hx with ⟨m, hm⟩
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

lemma fixpoint_defined : Defined (fun v ↦ c.Fixpoint (v ·.succ) (v 0)) φ.fixpointDef := .mk fun v ↦ by
  simp [Blueprint.fixpointDef, c.eval_limSeqDef]; rfl

@[simp] lemma eval_fixpointDef (v : Fin (k + 1) → V) :
    φ.fixpointDef.Evalb v ↔ c.Fixpoint (v ·.succ) (v 0) := c.fixpoint_defined.iff v

end

theorem induction [c.StrongSetSized] {P : V → Prop} (hP : ℒₛₑₜ-predicate P)
    (H : ∀ C : Set V, (∀ x ∈ C, c.Fixpoint v x ∧ P x) → ∀ x, c.Φ v C x → P x) :
    ∀ x, c.Fixpoint v x → P x := by
  apply InductionOnHierarchy.order_induction_sigma (Γ := Γ) (m := 1) (P := fun x ↦ c.Fixpoint v x → P x)
  · apply HierarchySymbol.Definable.imp
      (HierarchySymbol.DefinablePred.comp
        (by
          apply HierarchySymbol.Definable.of_deltaOne
          exact ⟨φ.fixpointDefΔ₁.rew <| Rew.embSubsts <| #0 :> fun x ↦ &(v x), c.fixpoint_defined.proper.rew' _,
            by intro v; simp [c.eval_fixpointDef]⟩)
        (by definability))
      (by definability)
  intro x ih hx
  have : c.Φ v {y | c.Fixpoint v y ∧ y < x} x := Strongset_sized.strong_set_sized (c.case.mp hx)
  exact H {y | c.Fixpoint v y ∧ y < x} (by intro y ⟨hy, hyx⟩; exact ⟨hy, ih y hyx hy⟩) x this

end Construction

attribute [irreducible] Blueprint.fixpointDef

end Fixpoint

end LO.FirstOrder.SetTheory
