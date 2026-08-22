module

public import Foundation.FirstOrder.SetTheory.Recursion.Seq
public import Foundation.FirstOrder.SetTheory.Recursion

@[expose] public section
/-!

# Blueprint for the recursion theorem in $\matHff{ZF}$

-/

namespace LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

namespace PR

structure Blueprint (k : ℕ) where
  graph : SetTheorySemisentence (k + 2)

-- TODO: To make this closer to `PRF.lean` from arithmetic, create a branch `recursion-fixpoint-nolength` where I don't pass the length `α` in to this definition.
def Blueprint.isAttempt_dfn (p : Blueprint k) : SetTheorySemisentence (k + 2) :=
  f“α f.
    !IsOrdinal.dfn α ∧ !IsFunction.dfn f ∧ !domain.dfn f = α ∧
    ∀ β ∈ α, ∀ y, !kpair.dfn β y ∈ f ↔ y = !p.graph (!restrict.dfn f β) ⋯”

#check fun (φ : Semisentence ℒₒᵣ 3) ↦ (⤫term(faf)[ α x y |   | !φ α x ⋯ ] : Semisentence ℒₒᵣ 3)

def Blueprint.result_dfn {k} (p : Blueprint k) : SetTheorySemisentence (k + 2) :=
  “y x. (!IsOrdinal.dfn x → ∃ α, ∃ f, !p.isAttempt_dfn α f ⋯ ∧ x ∼[f] y) ∧
    (¬!IsOrdinal.dfn x → !isEmpty y)”

/- TODO: Once the Lévy hierarchy has been added, add a `Δ` version. -/
-- def Blueprint.resultDeltaDef (p : Blueprint k) : SetTheorySemisentence (k + 2) := p.result.dfn.graphDelta

variable (V)

structure Construction {k : ℕ} (p : Blueprint k) where
  core : (Fin k → V) → V → V
  core_defined : DefinedFunction (fun v ↦ core (v ·.succ) (v 0)) p.graph

variable {V}

namespace Construction

variable {k : ℕ} {p : Blueprint k} (c : Construction V p) (v : Fin k → V)

def IsAttempt (α f : V) : Prop :=
  SetTheory.IsAttempt (c.core v) α f

-- An example showing that `⋯` in faf notation is implemented correctly.
set_option linter.flexible false in
example : Semiformula.Evalb v f“∀ x, ∃ y, y = !p.graph x ⋯” := by
  simp
  intro x
  use c.core v x
  intro z h
  have heq : ((“#0 = #3” : SetTheorySemisentence (k + 4)) :> fun (x : Fin k) ↦ “#0 = #x.succ.succ.succ.succ”) = fun x ↦ “#0 = #x.succ.succ.succ” := by
    apply funext_iff.mpr
    intro x
    by_cases hx : 0 ≠ x
    · obtain ⟨y, hy⟩ := Fin.exists_succ_eq.mpr hx.symm
      aesop
    · aesop
  suffices Semiformula.Evalb (z :> x :> v) p.graph by
    apply (c.core_defined.iff (z :> x :> v)).mp at this
    simp at this
    exact this.symm
  simp only [Semiformula.eval_nestFormulaeFunc, Nat.succ_eq_add_one, ← Semiformula.Evalb.eq_1] at h
  specialize h (x :> v)
  simpa [heq] using h

set_option linter.flexible false in
lemma eval_core_faf {x : V} : Semiformula.Evalb (x :> (c.core v x) :> v) f“x y. y = !p.graph x ⋯” := by
  simp
  intro z h
  suffices Semiformula.Evalb (z :> x :> v) p.graph by
    apply (c.core_defined.iff (z :> x :> v)).mp at this
    simp at this
    exact this.symm
  simp only [Semiformula.eval_nestFormulaeFunc, Nat.succ_eq_add_one, ← Semiformula.Evalb.eq_1] at h
  specialize h (x :> v)
  refine h ?_
  intro i
  by_cases hi : i = 0
  · aesop
  · obtain ⟨j, hj⟩ := Fin.exists_succ_eq.mpr hi
    aesop

set_option linter.flexible false in
lemma isAttempt_defined : Defined (fun v ↦ c.IsAttempt (v ·.succ.succ) (v 0) (v 1) : (Fin (k + 2) → V) → Prop) p.isAttempt_dfn := .mk fun v ↦ by
  -- TODO: This may be too specific to refactor into its own lemma.
  have hsplit {p : Fin (k + 1) → Prop} : (∀ i : Fin (k + 1), p i) ↔ (p 0 ∧ ∀ i : Fin k, p i.succ) := by
    constructor <;> intro h
    · exact And.intro (h 0) fun i ↦ h (i.succ)
    · intro i
      refine by_cases (p := i = 0) (q := p i) (by aesop) ?_
      · intro hi
        obtain ⟨j, hj⟩ := Fin.exists_succ_eq.mpr hi
        exact hj ▸ h.2 j
  simp [IsAttempt, SetTheory.IsAttempt, Blueprint.isAttempt_dfn]
  simp [Semiformula.eval_nestFormulaeFunc, ← Semiformula.Evalb.eq_1]
  intro hordinal hfunction hdomain
  apply forall_congr'
  intro x
  apply forall_congr'
  intro hx
  apply forall_congr'
  intro y
  simp [hsplit, c.core_defined.iff]
  simp only [← eq_iff_iff (a := ⟨x, y⟩ₖ ∈ v 1)]
  apply eq_iff_eq_cancel_left.mpr
  simp only [eq_iff_iff]
  constructor <;> intro h
  · specialize h (c.core (fun x ↦ v x.succ.succ) ((v 1) ↾ x))
    refine h ?_
    intro v_1 h₂
    aesop
  · intro x_1 h₂
    specialize h₂ (((v 1) ↾ x) :> (Matrix.vecTail (Matrix.vecTail v)))
    subst h
    simp_all only [Nat.succ_eq_add_one, Matrix.cons_val_zero, Matrix.cons_val_succ, forall_const]
    refine (h₂ ?_).symm
    aesop

#check c.isAttempt_defined.iff

@[simp] lemma isAttempt_defined_iff (v : Fin (k + 2) → V) :
    Semiformula.Evalb v p.isAttempt_dfn ↔ c.IsAttempt (v ·.succ.succ) (v 0) (v 1) := c.isAttempt_defined.iff v

variable {c v}

namespace IsAttempt

variable {α f : V}

lemma seq (h : c.IsAttempt v α f) : Seq f := ⟨h.2.1, α, h.2.2.1, h.1⟩

lemma spec (h : c.IsAttempt v α f) : ∀ β ∈ α, ∀ y, ⟨β, y⟩ₖ ∈ f ↔ y = c.core v (f ↾ β) := h.2.2.2

lemma empty (h : c.IsAttempt v α f) (hα : ∅ ∈ α) : ⟨∅, c.core v ∅⟩ₖ ∈ f := by
  have hrestrict {g : V} : g ↾ ∅ = ∅ := restrict_empty_eq
  exact (h.2.2.2 ∅ hα (c.core v ∅)).mpr (by aesop)

-- lemma succ (h : c.IsAttempt v α f) : ∀ β, SetTheory.succ β ∈ α → ∀ y, ⟨β, y⟩ₖ ∈ f → ⟨SetTheory.succ β, c.core v (insert ⟨β, y⟩ₖ (f ↾ β))⟩ₖ ∈ f := by
lemma succ (hf : c.IsAttempt v α f) : ∀ β, SetTheory.succ β ∈ α → ∀ y, ⟨β, y⟩ₖ ∈ f → ⟨SetTheory.succ β, c.core v ((f ↾ β) ⁀' y)⟩ₖ ∈ f := by
  intro β hβsuccα y hyf
  have := hf.1
  have := IsOrdinal.of_mem hβsuccα
  have hβα : β ∈ α :=
    IsTransitive.transitive (SetTheory.succ β) hβsuccα β (mem_succ_self (x := β))
  have := IsOrdinal.of_mem hβα
  have hβsubsetα : β ⊆ α := IsOrdinal.subset_iff.mpr (Or.inr hβα)
  have hy := (spec hf β hβα y).mp hyf
  have hlh : lh (f ↾ β) = β := (hf.seq.lh_restrict (by simpa using (hf.seq.lh_eq_domain_of ▸ hf.2.2.1).symm ▸ hβsubsetα))
  have hrestrict : f ↾ (SetTheory.succ β) = (f ↾ β) ⁀' y := by
    ext w
    constructor <;> intro h₂
    · rw [seqCons, SetTheory.mem_insert]
      rw [mem_restrict_iff] at h₂
      by_cases hw : w ∈ f ↾ β
      · exact Or.inr hw
      · obtain ⟨x, hx, y, hy⟩ := h₂.2
        refine Or.inl (hy ▸ kpair_iff.mpr ?_)
        apply mem_succ_iff.mp at hx
        have hxβ : x = β := by aesop
        refine And.intro ?_ (hf.2.1.unique (hxβ ▸ hy ▸ h₂.1) hyf)
        exact hxβ ▸ (hf.seq.lh_restrict (α := β) (hf.seq.domain_eq ▸ hf.2.2.1 ▸ hβsubsetα)).symm
    · rw [mem_restrict_iff]
      by_cases hw : w ∈ f ↾ β
      · refine And.intro (mem_restrict_iff.mp hw).1 ?_
        obtain ⟨x, hx, y, hxy⟩ := (mem_restrict_iff.mp hw).2
        exact ⟨x, mem_succ_iff.mpr (Or.inr hx), y, hxy⟩
      · rcases Or.resolve_right (mem_insert.mp h₂) hw with rfl
        refine And.intro (hlh.symm ▸ hyf) ⟨lh (f ↾ β), And.intro (hlh.symm ▸ (mem_succ_self β)) ⟨y, by simp⟩⟩
  exact (spec hf (SetTheory.succ β) hβsuccα _).mpr (by rw [hrestrict.symm])

lemma unique {f g α β : V} (h₁ : c.IsAttempt v α f) (h₂ : c.IsAttempt v β g) (h₁₂ : α ⊆ β) {γ} (hγα : γ ∈ α) {y₁ y₂} :
    ⟨γ, y₁⟩ₖ ∈ f → ⟨γ, y₂⟩ₖ ∈ g → y₁ = y₂ := by
  have : IsOrdinal α := h₁.1
  have : IsOrdinal β := h₂.1
  let αo : Ordinal V := IsOrdinal.toOrdinal α
  let βo : Ordinal V := IsOrdinal.toOrdinal β
  have := h₁.2.1
  have := h₂.2.1
  have hrestrict : f ↾ α = g ↾ α := by
    exact SetTheory.IsAttempt.isAttempt_coherent (α := αo) (β := βo) h₁ h₂ αo (by aesop)
  intro hy₁ hy₂
  have h := (mem_ext_iff.mp hrestrict) ⟨γ, y₁⟩ₖ
  have hy₁g : ⟨γ, y₁⟩ₖ ∈ g := by simpa [kpair_mem_restrict_iff, hy₁, hγα] using fun h₂ ↦ h.mp h₂
  exact this.unique hy₁g hy₂

end IsAttempt

lemma IsAttempt.zero : c.IsAttempt v 0 ∅ :=
  ⟨by simp, by simp, by aesop, fun β hβ ↦ False.elim (not_mem_empty hβ)⟩

lemma IsAttempt.one : c.IsAttempt v 1 {⟨∅, c.core v ∅⟩ₖ} :=
  ⟨IsOrdinal.nat one_mem_ω,
    by simp,
    by ext z; simp [mem_domain_iff, one_def, zero_def],
    by simp [one_def, zero_def]⟩

lemma IsAttempt.successor {f α y : V} (hf : c.IsAttempt v (SetTheory.succ α) f) (hy : ⟨α, y⟩ₖ ∈ f) :
    c.IsAttempt v (SetTheory.succ (SetTheory.succ α)) (f ⁀' c.core v f) :=
  ⟨ IsOrdinal.succ (h := hf.1), (hf.seq.seqCons _).1, by simp [seqCons, hf.2.2.1, hf.seq.lh_eq_domain_of, SetTheory.succ], by
    intro β hβ w
    have := hf.1
    have : IsOrdinal β := IsOrdinal.of_mem (by aesop)
    have hβ : β ⊆ SetTheory.succ α := IsOrdinal.subset_iff.mpr (mem_succ_iff.mp hβ)
    have hβdomain : β ⊆ domain f := hf.2.2.1 ▸ hβ
    -- have hrestrictβ : (f ⁀' c.core v y) ↾ β = f ↾ β :=
    --     restrict_insert_kpair_eq_restrict_of_not_mem (f := f) (x := lh f) (y := c.core v y) (A := β)
    --       fun h₂ ↦ mem_irrefl (lh f) (hf.seq.domain_eq ▸ hβdomain (lh f) h₂)
    have hrestrictβ {z : V} : (f ⁀' z) ↾ β = f ↾ β :=
        restrict_insert_kpair_eq_restrict_of_not_mem (f := f) (x := lh f) (y := z) (A := β)
          fun h₂ ↦ mem_irrefl (lh f) (hf.seq.domain_eq ▸ hβdomain (lh f) h₂)
    have hyeq := (hf.2.2.2 α (mem_succ_self α) y).mp hy
    rw [hrestrictβ, hyeq] at *
    have hseq := hf.seq.seqCons (c.core v f)
    have hrestrictlh := hf.2.1.restrict_eq_self f (lh f) (hf.seq.domain_eq ▸ subset_refl (domain f))
    rcases show β = SetTheory.succ α ∨ β ∈ SetTheory.succ α by
        exact IsOrdinal.subset_iff.mp hβ
        with (hβ | hβ)
    · have hβeq : β = lh f := hf.seq.lh_eq_domain_of ▸ hf.2.2.1 ▸ hβ
      rw [hβeq, lh_mem_seqCons_iff hf.seq, hrestrictlh]
    · have hβneq : β ≠ lh f := fun h ↦ mem_irrefl β ((h ▸ hf.seq.domain_eq ▸ hf.2.2.1) ▸ hβ)
      rw [kpair_mem_seqCons_iff]
      constructor <;> intro h
      · exact Or.elim h (by aesop) fun h ↦ (hf.2.2.2 β hβ w).mp h
      · exact Or.inr ((hf.2.2.2 β hβ w).mpr h)
  ⟩

variable (c v)

open Classical in
lemma IsAttempt.exists (α : V) [IsOrdinal α] : ∃ f, c.IsAttempt v (SetTheory.succ α) f ∧ SetTheory.succ α = lh f := by
  let αo : Ordinal V := IsOrdinal.toOrdinal α
  have := IsOrdinal.succ (α := α)
  have hdefinable : ℒₛₑₜ-function₁ c.core v := by
    refine ⟨?_⟩
    let φ : SetTheorySemiformula V 2 := Rewriting.subst p.graph.emb
        fun i ↦ (if hi : i.val < 2 then #(i.castLT hi) else &(v (i.subNat 2 (by omega))) : SetTheorySemiterm V 2)
    use φ
    intro v
    simpa [φ, c.core_defined.iff] using Iff.intro (fun h ↦ by simpa) (fun h ↦ by simpa)
  obtain ⟨f, hf⟩ := SetTheory.Replacement.attempt_function_exists (c.core v) hdefinable (IsOrdinal.toOrdinal (SetTheory.succ αo))
  refine ⟨f, ?_, ?_⟩
  · exact hf
  · simpa using (Construction.IsAttempt.seq hf).domain_eq ▸ hf.2.2.1.symm

lemma IsAttempt.existsUnique (α : V) [IsOrdinal α] : ∃! f, c.IsAttempt v (SetTheory.succ α) f ∧ SetTheory.succ α = lh f := by
  let αo : Ordinal V := IsOrdinal.toOrdinal α
  have := IsOrdinal.succ (α := α)
  have hdefinable : ℒₛₑₜ-function₁ c.core v := by
    refine ⟨?_⟩
    let φ : SetTheorySemiformula V 2 := Rewriting.subst p.graph.emb
        fun i ↦ (if hi : i.val < 2 then #(i.castLT hi) else &(v (i.subNat 2 (by omega))) : SetTheorySemiterm V 2)
    use φ
    intro v
    simpa [φ, c.core_defined.iff] using Iff.intro (fun h ↦ by simpa) (fun h ↦ by simpa)
  obtain ⟨f, hf⟩ := SetTheory.Replacement.attempt_function_exists (c.core v) hdefinable (IsOrdinal.toOrdinal (SetTheory.succ αo))
  #check SetTheory.IsAttempt.existsUnique_of_exists (c.core v) (SetTheory.succ α) (IsAttempt.exists c v α)

lemma attempt_result_existsUnique (α : V) : ∃! y,
    (IsOrdinal α → ∃ f, c.IsAttempt v (SetTheory.succ α) f ∧ ⟨α, y⟩ₖ ∈ f) ∧
    (¬IsOrdinal α → y = ∅) := by
  by_cases hα : IsOrdinal α
  · rcases IsAttempt.exists c v α with ⟨f, hf, heq⟩
    have : ∃ z, ⟨α, z⟩ₖ ∈ f := hf.seq.exists (show α ∈ lh f from by simp [←heq])
    rcases this with ⟨z, hz⟩
    simp only [hα, not_true, true_implies, false_implies, and_true]
    exact ExistsUnique.intro z ⟨f, hf, hz⟩ (by
      rintro z' ⟨f', hf', hz'⟩
      exact Eq.symm <| hf.unique hf' (by aesop) (mem_succ_self α) hz hz')
  · refine ExistsUnique.intro (∅ : V) (by aesop) fun y ↦ by aesop

noncomputable def result (α : V) : V := Classical.choose! (c.attempt_result_existsUnique v α)

lemma result_spec (α : V) :
    (IsOrdinal α → ∃ f, c.IsAttempt v (SetTheory.succ α) f ∧ ⟨α, c.result v α⟩ₖ ∈ f) ∧
    (¬IsOrdinal α → c.result v α = ∅) :=
  Classical.choose!_spec (c.attempt_result_existsUnique v α)

lemma result_spec_of_isOrdinal (α : V) [hα : IsOrdinal α] : ∃ f, c.IsAttempt v (SetTheory.succ α) f ∧ ⟨α, c.result v α⟩ₖ ∈ f := by
  simpa [hα] using c.result_spec v α

@[simp] theorem result_empty : c.result v ∅ = c.core v ∅ := by
  rcases c.result_spec_of_isOrdinal v ∅ with ⟨f, hf, hempty⟩
  exact hf.seq.1.unique hempty (hf.empty (mem_succ_self ∅))

@[simp] theorem result_succ (α : V) [hα : IsOrdinal α] : c.result v (SetTheory.succ α) = c.core v (Classical.choose (IsAttempt.exists c v α)) := by
  -- TODO: The theorem statement is incorrect, I don't think there's a way to state it without obtaining an attempt `f` and writing `c.core v f`.
  rcases c.result_spec_of_isOrdinal v α with ⟨f, hf, h⟩
  have := hf.successor h
  have hmemcons := hf.2.2.1.symm ▸ hf.seq.domain_eq ▸ SetTheory.lh_mem_seqCons f (c.core v f)
  -- have hrestrict := (hf.2.2.2 α (mem_succ_self α) _).mp h
  have heq : Classical.choose (IsAttempt.exists c v α) = f := by
    #check SetTheory.IsAttempt.un
    sorry
  exact Eq.symm
    <| Classical.choose_uniq (c.attempt_result_existsUnique v (SetTheory.succ α))
    ⟨ by
        simp only [IsOrdinal.succ, forall_const]
        refine ⟨f ⁀' c.core v f, ?_⟩
        refine ⟨this, ?_⟩
        aesop
        ,
      by simp [IsOrdinal.succ]
    ⟩
    -- ⟨_, this, by simp [hf.2.2.1 ▸ hf.seq.domain_eq]⟩

lemma result_graph (y α : V) : y = c.result v α ↔
    (IsOrdinal α → ∃ f, c.IsAttempt v (SetTheory.succ α) f ∧ ⟨α, y⟩ₖ ∈ f) ∧
    (¬IsOrdinal α → y = ∅) :=
  ⟨by rintro rfl
      refine And.intro (fun hα ↦ ?_) (fun hα ↦ ?_)
      · rcases (c.result_spec v α).1 hα with ⟨f, hf, h⟩
        exact ⟨f, hf, h⟩
      · exact (c.result_spec v α).2 hα,
   by
      rintro ⟨hleft, hright⟩
      by_cases hα : IsOrdinal α
      · rcases (c.result_spec v α).1 hα with ⟨f', hf', h'⟩
        rcases hleft hα with ⟨f, hf, h⟩
        exact Eq.symm <| hf'.unique hf
          (subset_refl (SetTheory.succ α))
          (mem_succ_self α) h' h
      · exact Eq.symm <| hright hα ▸ (c.result_spec v α).2 hα⟩

set_option linter.flexible false in
lemma result_defined : DefinedFunction (fun v ↦ c.result (v ·.succ) (v 0) : (Fin (k + 1) → V) → V) p.result_dfn := .mk fun v ↦ by
  simp [Blueprint.result_dfn, result_graph, c.isAttempt_defined_iff, -and_congr_left_iff]
  refine and_congr ?_ ?_
  · refine eq_iff_iff.mp ?_
    refine implies_congr rfl ?_
    refine eq_iff_iff.mpr ?_
    refine Iff.intro (fun h ↦ ?_) (by aesop)
    · rcases h with ⟨α', f', hf'⟩
      have := hf'.1.seq.IsOrdinal_of_mem_domain (mem_domain_of_kpair_mem hf'.2)
      have : IsOrdinal α' := hf'.1.1
      rcases IsAttempt.exists c (v ·.succ.succ) (v 1) with ⟨f, hf⟩
      use f
      refine And.intro ?_ ?_
      · exact hf.1
      · let α'o : Ordinal V := IsOrdinal.toOrdinal α'
        let v1o : Ordinal V := IsOrdinal.toOrdinal (v 1)
        have hsubset : succ v1o ⊆ α'o := (IsOrdinal.subset_succ_iff (succ v1o) α'o).mp
        have hrestrict : f = f' ↾ (SetTheory.succ v1o) := by
          rw [← hf.1.2.1.restrict_eq_self (A := succ (v 1))]
          rw [← (by aesop : v1o.val = v 1)] at hf
          #check SetTheory.IsAttempt.isAttempt_coherent hf.1 hf'.1
          sorry
        sorry
  · rfl

/- TODO: Once the Lévy hierarchy has been added, add a `Δ` version. -/
-- lemma result_defined_delta : DefinedFunction (fun v ↦ c.result (v ·.succ) (v 0) : (Fin (k + 1) → V) → V) p.resultDeltaDef :=
--   c.result_defined.graph_delta

@[simp] lemma result_defined_iff (v : Fin (k + 2) → V) :
    p.result_dfn.Evalb v ↔ v 0 = c.result (v ·.succ.succ) (v 1) := c.result_defined.iff

instance result_definable : DefinableFunction (fun v ↦ c.result (v ·.succ) (v 0) : (Fin (k + 1) → V) → V) :=
  c.result_defined.to_definable

attribute [irreducible] Blueprint.result_dfn

end Construction

end PR

end LO.FirstOrder.SetTheory
