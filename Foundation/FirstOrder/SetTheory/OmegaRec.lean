module

public import Foundation.FirstOrder.SetTheory.Ordinal
public import Foundation.FirstOrder.SetTheory.Function

/-!
# Definable recursion on omega in Zermelo set theory

The mathematical construction is folklore: finite computations are extended by adjoining one pair.
The blueprint interface and the extension by the empty set outside omega are specific to this
formalization, following `Arithmetic/HFS/PRF.lean`.
-/

@[expose] public section

namespace FFL.FirstOrder.SetTheory

namespace OmegaRec

structure Blueprint (k : ℕ) where
  /-- The initial value, with arguments ordered as output followed by parameters. -/
  zero : SetTheorySemisentence (k + 1)
  /-- The step, with arguments ordered as output, previous value, index, and parameters. -/
  succ : SetTheorySemisentence (k + 3)

def Blueprint.cseqDef {k : ℕ} (p : Blueprint k) : SetTheorySemisentence (k + 2) :=
  “s n.
    (∃ w, !isω w ∧ n ∈ w)
    ∧ !IsFunction.dfn s
    ∧ (∃ d, !domain.dfn d s ∧ !succ.dfn d n)
    ∧ (∃ e z t, !isEmpty e ∧ !p.zero z ⋯ ∧ !kpair.dfn t e z ∧ t ∈ s)
    ∧ (∀ i ∈ n, ∀ z t, !kpair.dfn t i z ∧ t ∈ s →
        ∃ u j q, !p.succ u z i ⋯ ∧ !succ.dfn j i ∧ !kpair.dfn q j u ∧ q ∈ s)”

def Blueprint.resultDef {k : ℕ} (p : Blueprint k) : SetTheorySemisentence (k + 2) :=
  “z n.
    (∃ s t, !p.cseqDef s n ⋯ ∧ !kpair.dfn t n z ∧ t ∈ s)
    ∨ ((∀ w, !isω w → n ∉ w) ∧ !isEmpty z)”

variable (V : Type*) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭]

structure Construction {k : ℕ} (p : Blueprint k) where
  zero : (Fin k → V) → V
  succ : (Fin k → V) → V → V → V
  zero_defined : DefinedFunction zero p.zero
  succ_defined : DefinedFunction (fun v ↦ succ (v ·.succ.succ) (v 1) (v 0)) p.succ

variable {V}

namespace Construction

variable {k : ℕ} {p : Blueprint k} (c : Construction V p)

instance zero_definable : (ℒₛₑₜ).DefinableFunction c.zero := c.zero_defined.to_definable

instance succ_definable :
    (ℒₛₑₜ).DefinableFunction (fun v ↦ c.succ (v ·.succ.succ) (v 1) (v 0)) :=
  c.succ_defined.to_definable

def CSeq (v : Fin k → V) (n s : V) : Prop :=
  n ∈ (ω : V) ∧ IsFunction s ∧ domain s = SetTheory.succ n ∧ ⟨0, c.zero v⟩ₖ ∈ s ∧
    ∀ i ∈ n, ∀ z, ⟨i, z⟩ₖ ∈ s → ⟨SetTheory.succ i, c.succ v i z⟩ₖ ∈ s

lemma cseq_defined : Defined
    (fun v ↦ c.CSeq (v ·.succ.succ) (v 1) (v 0)) p.cseqDef := .mk fun v ↦ by
  simp [Blueprint.cseqDef, CSeq, c.zero_defined.iff, c.succ_defined.iff, zero_def]

@[simp] lemma eval_cseqDef (v : Fin (k + 2) → V) :
    p.cseqDef.Evalb v ↔ c.CSeq (v ·.succ.succ) (v 1) (v 0) := c.cseq_defined.iff v

instance cseq_definable :
    (ℒₛₑₜ).Definable (fun v ↦ c.CSeq (v ·.succ.succ) (v 1) (v 0)) :=
  c.cseq_defined.to_definable

instance cseq_definable_param (v : Fin k → V) : ℒₛₑₜ-relation (c.CSeq v) := by
  use (Rew.embSubsts (#1 :> #0 :> fun i : Fin k ↦ &(v i))) ▹ p.cseqDef
  intro w
  simpa [Semiformula.eval_embSubsts, Matrix.comp_vecCons', Function.comp_def]
    using c.cseq_defined.iff (w 1 :> w 0 :> v)

instance succ_definable_param (v : Fin k → V) : ℒₛₑₜ-function₂ (c.succ v) := by
  use (Rew.embSubsts (#0 :> #2 :> #1 :> fun i : Fin k ↦ &(v i))) ▹ p.succ
  intro w
  simpa [Semiformula.eval_embSubsts, Matrix.comp_vecCons', Function.comp_def]
    using c.succ_defined.iff (w 0 :> w 2 :> w 1 :> v)

namespace CSeq

variable {c} {v : Fin k → V} {n m s t i z w : V}

lemma nat (h : c.CSeq v n s) : n ∈ (ω : V) := h.1

lemma isFunction (h : c.CSeq v n s) : IsFunction s := h.2.1

lemma domain_eq (h : c.CSeq v n s) : domain s = SetTheory.succ n := h.2.2.1

lemma zero (h : c.CSeq v n s) : ⟨0, c.zero v⟩ₖ ∈ s := h.2.2.2.1

lemma succ (h : c.CSeq v n s) (hi : i ∈ n) (hz : ⟨i, z⟩ₖ ∈ s) :
    ⟨SetTheory.succ i, c.succ v i z⟩ₖ ∈ s := h.2.2.2.2 i hi z hz

lemma exists_value (h : c.CSeq v n s) (hi : i ∈ SetTheory.succ n) :
    ∃ z, ⟨i, z⟩ₖ ∈ s := mem_domain_iff.mp (h.domain_eq ▸ hi)

lemma index_mem (h : c.CSeq v n s) (hz : ⟨i, z⟩ₖ ∈ s) : i ∈ (ω : V) :=
  IsTransitive.ω.transitive _ (ω_succ_closed h.nat) _
    (h.domain_eq ▸ mem_domain_of_kpair_mem hz)

lemma initial (v : Fin k → V) : c.CSeq v 0 {⟨0, c.zero v⟩ₖ} :=
  ⟨zero_mem_ω, inferInstance, by
    ext x; simp [mem_domain_iff, zero_def, kpair_iff, SetTheory.succ],
    by simp, by simp [zero_def]⟩

lemma successor (h : c.CSeq v n s) (hz : ⟨n, z⟩ₖ ∈ s) :
    c.CSeq v (SetTheory.succ n) (insert ⟨SetTheory.succ n, c.succ v n z⟩ₖ s) := by
  have : IsFunction s := h.isFunction
  and_intros
  · exact ω_succ_closed h.nat
  · exact IsFunction.insert s _ _ (by simp [h.domain_eq])
  · simp [h.domain_eq, SetTheory.succ]
  · simp [h.zero]
  · intro i hi y hiy
    have h₁ : (⟨i, y⟩ₖ : V) ≠ ⟨SetTheory.succ n, c.succ v n z⟩ₖ := by
      intro h₂
      exact mem_irrefl (SetTheory.succ n) ((kpair_iff.mp h₂).1 ▸ hi)
    have h₂ : ⟨i, y⟩ₖ ∈ s := (mem_insert.mp hiy).resolve_left h₁
    rcases mem_succ_iff.mp hi with rfl | hi
    · have : y = z := IsFunction.unique h₂ hz
      simp [this]
    · exact mem_insert.mpr (Or.inr (h.succ hi h₂))

private lemma mem_of_succ_pair (h : c.CSeq v n s) (hz : ⟨SetTheory.succ i, z⟩ₖ ∈ s) :
    i ∈ n := by
  have h₁ : SetTheory.succ i ∈ SetTheory.succ n :=
    h.domain_eq ▸ mem_domain_of_kpair_mem hz
  rcases mem_succ_iff.mp h₁ with h₁ | h₁
  · exact h₁ ▸ mem_succ_self i
  · exact (IsTransitive.nat h.nat).transitive _ h₁ _ (mem_succ_self i)

lemma agree (hs : c.CSeq v n s) (ht : c.CSeq v m t)
    (hi : i ∈ (ω : V)) (hz : ⟨i, z⟩ₖ ∈ s) (hw : ⟨i, w⟩ₖ ∈ t) : z = w := by
  have : IsFunction s := hs.isFunction
  have : IsFunction t := ht.isFunction
  have h₁ : ∀ i ∈ (ω : V), ∀ z w, ⟨i, z⟩ₖ ∈ s → ⟨i, w⟩ₖ ∈ t → z = w := by
    apply naturalNumber_induction
    · definability
    case zero =>
      intro z w hz hw
      have : z = c.zero v := IsFunction.unique hz hs.zero
      have : w = c.zero v := IsFunction.unique hw ht.zero
      simp_all
    case succ =>
      intro i _ ih z w hz hw
      have h₂ : i ∈ n := hs.mem_of_succ_pair hz
      have h₃ : i ∈ m := ht.mem_of_succ_pair hw
      obtain ⟨z', hz'⟩ := hs.exists_value (mem_succ_iff.mpr (Or.inr h₂))
      obtain ⟨w', hw'⟩ := ht.exists_value (mem_succ_iff.mpr (Or.inr h₃))
      have h₄ : z' = w' := ih z' w' hz' hw'
      have h₅ : z = c.succ v i z' := IsFunction.unique hz (hs.succ h₂ hz')
      have h₆ : w = c.succ v i w' := IsFunction.unique hw (ht.succ h₃ hw')
      simp [h₄, h₅, h₆]
  exact h₁ i hi z w hz hw

lemma subset (hs : c.CSeq v n s) (ht : c.CSeq v m t)
    (h : SetTheory.succ n ⊆ SetTheory.succ m) : s ⊆ t := by
  have : IsFunction s := hs.isFunction
  intro q hq
  obtain ⟨i, z, rfl⟩ := IsFunction.mem_eq_kpair hq
  have h₁ : i ∈ SetTheory.succ n := hs.domain_eq ▸ mem_domain_of_kpair_mem hq
  obtain ⟨w, hw⟩ := ht.exists_value (h _ h₁)
  have : z = w := hs.agree ht (hs.index_mem hq) hq hw
  simpa [this] using hw

lemma unique (hs : c.CSeq v n s) (ht : c.CSeq v n t) : s = t :=
  subset_antisymm (hs.subset ht (subset_refl _)) (ht.subset hs (subset_refl _))

variable (c v)

lemma «exists» (n : V) (hn : n ∈ (ω : V)) : ∃ s, c.CSeq v n s := by
  revert n
  apply naturalNumber_induction
  · definability
  case zero => exact ⟨_, initial v⟩
  case succ =>
    intro n _ ih
    obtain ⟨s, hs⟩ := ih
    obtain ⟨z, hz⟩ := hs.exists_value (mem_succ_self n)
    exact ⟨_, hs.successor hz⟩

end CSeq

variable (v : Fin k → V)

lemma cseq_result_existsUnique (n : V) (hn : n ∈ (ω : V)) :
    ∃! z, ∃ s, c.CSeq v n s ∧ ⟨n, z⟩ₖ ∈ s := by
  obtain ⟨s, hs⟩ := CSeq.exists c v n hn
  obtain ⟨z, hz⟩ := hs.exists_value (mem_succ_self n)
  apply ExistsUnique.intro z ⟨s, hs, hz⟩
  rintro w ⟨t, ht, hw⟩
  exact ht.agree hs hn hw hz

lemma result_existsUnique (n : V) :
    ∃! z, (∃ s, c.CSeq v n s ∧ ⟨n, z⟩ₖ ∈ s) ∨ (n ∉ (ω : V) ∧ z = ∅) := by
  by_cases hn : n ∈ (ω : V)
  · simpa [hn] using c.cseq_result_existsUnique v n hn
  · have h₁ : ∀ s, ¬c.CSeq v n s := fun _ hs ↦ hn hs.nat
    simp [hn, h₁]

/-- The recursive value at `n`, or the empty set when `n ∉ ω`. -/
noncomputable def result (n : V) : V := Classical.choose! (c.result_existsUnique v n)

lemma result_graph (z n : V) : z = c.result v n ↔
    (∃ s, c.CSeq v n s ∧ ⟨n, z⟩ₖ ∈ s) ∨ (n ∉ (ω : V) ∧ z = ∅) :=
  Classical.choose!_eq_iff_right (c.result_existsUnique v n)

lemma result_spec {n : V} (hn : n ∈ (ω : V)) :
    ∃ s, c.CSeq v n s ∧ ⟨n, c.result v n⟩ₖ ∈ s := by
  simpa [hn] using (c.result_graph v (c.result v n) n).mp rfl

@[simp] theorem result_of_not_mem {n : V} (hn : n ∉ (ω : V)) : c.result v n = ∅ :=
  ((c.result_graph v ∅ n).mpr (Or.inr ⟨hn, rfl⟩)).symm

@[simp] theorem result_zero : c.result v 0 = c.zero v := by
  obtain ⟨s, hs, hz⟩ := c.result_spec v zero_mem_ω
  exact IsFunction.unique (hf := hs.isFunction) hz hs.zero

@[simp] theorem result_succ {n : V} (hn : n ∈ (ω : V)) :
    c.result v (SetTheory.succ n) = c.succ v n (c.result v n) := by
  obtain ⟨s, hs, hz⟩ := c.result_spec v hn
  exact ((c.result_graph v _ _).mpr (Or.inl ⟨_, hs.successor hz, by simp⟩)).symm

lemma result_defined :
    DefinedFunction (fun v ↦ c.result (v ·.succ) (v 0)) p.resultDef := .mk fun v ↦ by
  simp [Blueprint.resultDef, c.result_graph, c.eval_cseqDef]

@[simp] lemma eval_resultDef (v : Fin (k + 2) → V) :
    p.resultDef.Evalb v ↔ v 0 = c.result (v ·.succ.succ) (v 1) := c.result_defined.iff v

instance result_definable :
    (ℒₛₑₜ).DefinableFunction (fun v ↦ c.result (v ·.succ) (v 0)) :=
  c.result_defined.to_definable

instance result_definable_param : ℒₛₑₜ-function₁ (c.result v) := by
  use (Rew.embSubsts (#0 :> #1 :> fun i : Fin k ↦ &(v i))) ▹ p.resultDef
  intro w
  simpa [Semiformula.eval_embSubsts, Matrix.comp_vecCons', Function.comp_def]
    using c.result_defined.iff (w 0 :> w 1 :> v)

theorem result_unique {f : V → V} (hf : ℒₛₑₜ-function₁ f)
    (hzero : f 0 = c.zero v)
    (hsucc : ∀ n ∈ (ω : V), f (SetTheory.succ n) = c.succ v n (f n)) :
    ∀ n ∈ (ω : V), f n = c.result v n := by
  apply naturalNumber_induction
  · definability
  · simpa using hzero
  · intro n hn ih
    simp [hsucc n hn, c.result_succ v hn, ih]

lemma result_mem {A : V} (hzero : c.zero v ∈ A)
    (hsucc : ∀ n ∈ (ω : V), ∀ z ∈ A, c.succ v n z ∈ A) :
    ∀ n ∈ (ω : V), c.result v n ∈ A := by
  apply naturalNumber_induction
  · definability
  · simpa using hzero
  · intro n hn ih
    simpa [c.result_succ v hn] using hsucc n hn (c.result v n) ih

/-- The graph of the recursive function restricted to values in `A`. -/
noncomputable def graph (A : V) : V :=
  {q ∈ (ω : V) ×ˢ A ; ∃ n, q = ⟨n, c.result v n⟩ₖ}

lemma mem_graph_iff {A q : V} : q ∈ c.graph v A ↔
    q ∈ (ω : V) ×ˢ A ∧ ∃ n, q = ⟨n, c.result v n⟩ₖ := by simp [graph]

@[simp] lemma kpair_mem_graph_iff {A n z : V} :
    ⟨n, z⟩ₖ ∈ c.graph v A ↔ n ∈ (ω : V) ∧ z ∈ A ∧ z = c.result v n := by
  simp only [mem_graph_iff, kpair_mem_iff, kpair_iff]
  grind

theorem graph_mem_function {A : V} (hzero : c.zero v ∈ A)
    (hsucc : ∀ n ∈ (ω : V), ∀ z ∈ A, c.succ v n z ∈ A) :
    c.graph v A ∈ A ^ (ω : V) := by
  apply mem_function.intro
  · intro q hq
    exact ((c.mem_graph_iff v).mp hq).1
  · intro n hn
    apply ExistsUnique.intro (c.result v n)
    · exact (c.kpair_mem_graph_iff v).mpr ⟨hn, c.result_mem v hzero hsucc n hn, rfl⟩
    · intro z hz
      exact ((c.kpair_mem_graph_iff v).mp hz).2.2

end Construction

end OmegaRec

end FFL.FirstOrder.SetTheory
