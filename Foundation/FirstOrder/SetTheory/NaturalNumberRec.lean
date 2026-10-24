module

public import Foundation.FirstOrder.SetTheory.Ordinal
public import Foundation.FirstOrder.SetTheory.FunctionSet

/-!
# Natural number recursion in Zermelo set theory

-/

@[expose] public section

namespace FFL.FirstOrder.SetTheory

namespace NaturalNumberRec

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

structure CSeq (v : Fin k → V) (n s : V) : Prop where
  nat : n ∈ (ω : V)
  isFunction : IsFunction s
  domain_eq : domain s = SetTheory.succ n
  zero : ⟨0, c.zero v⟩ₖ ∈ s
  succ : ∀ i ∈ n, ∀ z, ⟨i, z⟩ₖ ∈ s → ⟨SetTheory.succ i, c.succ v i z⟩ₖ ∈ s

lemma cseq_defined :
    Defined (fun v ↦ c.CSeq (v ·.succ.succ) (v 1) (v 0)) p.cseqDef := .mk fun v ↦ by
  suffices h : ∀ v, p.cseqDef.Evalb v ↔
      (v 1 ∈ (ω : V) ∧ IsFunction (v 0) ∧ domain (v 0) = SetTheory.succ (v 1) ∧
        ⟨0, c.zero (v ·.succ.succ)⟩ₖ ∈ v 0 ∧
        ∀ i ∈ v 1, ∀ z, ⟨i, z⟩ₖ ∈ v 0 →
          ⟨SetTheory.succ i, c.succ (v ·.succ.succ) i z⟩ₖ ∈ v 0) by
    exact (h v).trans ⟨
      (fun h ↦ ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩),
      (fun h ↦ ⟨h.nat, h.isFunction, h.domain_eq, h.zero, h.succ⟩)⟩
  simp [Blueprint.cseqDef, c.zero_defined.iff, c.succ_defined.iff, zero_def]

@[simp] lemma cseq_defined_iff (v : Fin (k + 2) → V) :
    p.cseqDef.Evalb v ↔ c.CSeq (v ·.succ.succ) (v 1) (v 0) := c.cseq_defined.iff v

instance cseq_definable_param (v : Fin k → V) : ℒₛₑₜ-relation (c.CSeq v) := by
  use (Rew.embSubsts (#1 :> #0 :> fun i : Fin k ↦ &(v i))) ▹ p.cseqDef
  intro w
  simpa [Semiformula.eval_embSubsts, Matrix.comp_vecCons', Function.comp_def]
    using c.cseq_defined.iff (w 1 :> w 0 :> v)

namespace CSeq

variable {c} {v : Fin k → V} {n m s t i z w : V}

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
    c.CSeq v (SetTheory.succ n) (insert ⟨SetTheory.succ n, c.succ v n z⟩ₖ s) where
  nat := ω_succ_closed h.nat
  isFunction := IsFunction.insert s _ _ (by simp [h.domain_eq]) (hf := h.isFunction)
  domain_eq := by simp [domain_insert, h.domain_eq, SetTheory.succ]
  zero := by simp [h.zero]
  succ := by
    intro i hi y hiy
    have h₁ : (⟨i, y⟩ₖ : V) ≠ ⟨SetTheory.succ n, c.succ v n z⟩ₖ := by
      intro h₂
      exact mem_irrefl (SetTheory.succ n) ((kpair_iff.mp h₂).1 ▸ hi)
    have h₂ : ⟨i, y⟩ₖ ∈ s := (mem_insert.mp hiy).resolve_left h₁
    rcases mem_succ_iff.mp hi with rfl | hi
    · have : y = z := IsFunction.unique (hf := h.isFunction) h₂ hz
      simp [this]
    · exact mem_insert.mpr (Or.inr (h.succ i hi y h₂))

private lemma mem_of_succ_pair (h : c.CSeq v n s) (hz : ⟨SetTheory.succ i, z⟩ₖ ∈ s) :
    i ∈ n := by
  have h₁ : SetTheory.succ i ∈ SetTheory.succ n :=
    h.domain_eq ▸ mem_domain_of_kpair_mem hz
  rcases mem_succ_iff.mp h₁ with h₁ | h₁
  · exact h₁ ▸ mem_succ_self i
  · exact (IsTransitive.nat h.nat).transitive _ h₁ _ (mem_succ_self i)

lemma value_unique (hs : c.CSeq v n s) (ht : c.CSeq v m t)
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
      have h₅ : z = c.succ v i z' := IsFunction.unique hz (hs.succ i h₂ z' hz')
      have h₆ : w = c.succ v i w' := IsFunction.unique hw (ht.succ i h₃ w' hw')
      simp [h₄, h₅, h₆]
  exact h₁ i hi z w hz hw

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
  exact ht.value_unique hs hn hw hz

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

theorem result_eq_empty_of_not_mem_omega {n : V} (hn : n ∉ (ω : V)) : c.result v n = ∅ :=
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
  simp [Blueprint.resultDef, c.result_graph, c.cseq_defined_iff]

instance result_definable :
    (ℒₛₑₜ).DefinableFunction (fun v ↦ c.result (v ·.succ) (v 0)) :=
  c.result_defined.to_definable

end Construction

end NaturalNumberRec

end FFL.FirstOrder.SetTheory
