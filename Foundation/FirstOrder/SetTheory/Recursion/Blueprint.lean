module

public import Foundation.FirstOrder.SetTheory.ZF
public import Foundation.FirstOrder.SetTheory.Recursion

@[expose] public section
/-!

# Blueprint wrapper for the recursion theorem in $\mathsf{ZF}$

-/

namespace LO.FirstOrder.SetTheory.Recursion

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

structure Blueprint (k : ℕ) where
  graph : SetTheorySemisentence (k + 2)

-- TODO: Look at how `ZF.lean` uses `ℒₛₑₜ-relation` vs. graph sentences, and imitate that here.
def Blueprint.isAttempt_dfn (p : Blueprint k) : SetTheorySemisentence (k + 1) :=
  f“f.
    :Seq f ∧
    ∀ β ∈ !lh.dfn f, ∀ y, !kpair.dfn β y ∈ f ↔ y = !p.graph (!restrict.dfn f β) ⋯”

#check fun (φ : Semisentence ℒₒᵣ 3) ↦ (⤫term(faf)[ α x y |   | !φ α x ⋯ ] : Semisentence ℒₒᵣ 3)

-- TODO: I don't know how to write a literal formula while in faf notation, so I specified `lh f = SetTheory.succ x` this way.
def Blueprint.result_dfn {k} (p : Blueprint k) : SetTheorySemisentence (k + 2) :=
  -- “y x. (!IsOrdinal.dfn x → ∃ f, !p.isAttempt_dfn f ⋯ ∧ x ∼[f] y) ∧
  --   (¬!IsOrdinal.dfn x → !isEmpty y)”
  “y x. (!IsOrdinal.dfn x → ∃ f, !p.isAttempt_dfn f ⋯ ∧ (∀ z, !SetTheory.succ.dfn z x → !lh.dfn z f) ∧ x ∼[f] y) ∧
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

instance core_definable : ℒₛₑₜ-function₁ c.core v := by
  refine ⟨(Rew.embSubsts (#0 :> #1 :> fun i : Fin k ↦ &(v i))) ▹ p.graph, ?_⟩
  intro x
  simpa [Semiformula.eval_embSubsts, Matrix.comp_vecCons', Function.comp_def]
    using c.core_defined.iff (x 0 :> x 1 :> v)

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
lemma isAttempt_defined : Defined (fun v ↦ SetTheory.IsAttempt (c.core (v ·.succ)) (v 0) : (Fin (k + 1) → V) → Prop) p.isAttempt_dfn := .mk fun v ↦ by
  have hsplit {p : Fin (k + 1) → Prop} : (∀ i : Fin (k + 1), p i) ↔ (p 0 ∧ ∀ i : Fin k, p i.succ) := by
    refine Iff.intro (fun h ↦ ⟨h 0, fun i ↦ h (i.succ)⟩) fun h i ↦ ?_
    refine by_cases (p := i = 0) (q := p i) (by aesop) ?_
    · intro hi
      obtain ⟨j, hj⟩ := Fin.exists_succ_eq.mpr hi
      exact hj ▸ h.2 j
  simp [IsAttempt, Blueprint.isAttempt_dfn]
  simp [Semiformula.eval_nestFormulaeFunc, ← Semiformula.Evalb.eq_1]
  intro hseq
  apply forall_congr'
  intro x
  apply forall_congr'
  intro hx
  apply forall_congr'
  intro y
  simp [hsplit, c.core_defined.iff]
  simp only [← eq_iff_iff (a := ⟨x, y⟩ₖ ∈ v 0)]
  apply eq_iff_eq_cancel_left.mpr
  simp only [eq_iff_iff]
  constructor <;> intro h
  · specialize h (c.core (fun x ↦ v x.succ) ((v 0) ↾ x))
    refine h ?_
    intro v_1 h₂
    aesop
  · intro x_1 h₂
    specialize h₂ (((v 0) ↾ x) :> (Matrix.vecTail v))
    subst h
    simp_all only [Matrix.cons_val_zero, Matrix.cons_val_succ, forall_const]
    refine (h₂ ?_).symm
    aesop

@[simp] lemma eval_isAttempt_dfn {v} : p.isAttempt_dfn.Evalb v ↔ SetTheory.IsAttempt (c.core (v ·.succ)) (v 0) := c.isAttempt_defined.iff v

-- @[simp] lemma isAttempt_defined_iff (v : Fin (k + 1) → V) :
--     Semiformula.Evalb v p.isAttempt_dfn ↔ c.IsAttempt (v ·.succ) (v 0) := c.isAttempt_defined.iff v

namespace IsAttempt

variable {c v} {f : V}

lemma seq (h : SetTheory.IsAttempt (c.core v) f) : Seq f := h.1

lemma isOrdinal_lh (hf : SetTheory.IsAttempt (c.core v) f) : IsOrdinal (lh f) := SetTheory.isOrdinal_lh hf.1

lemma spec (h : SetTheory.IsAttempt (c.core v) f) : ∀ β ∈ lh f, ∀ y, ⟨β, y⟩ₖ ∈ f ↔ y = c.core v (f ↾ β) := h.2

lemma domain_eq_lh (hf : SetTheory.IsAttempt (c.core v) f) : domain f = lh f := hf.1.domain_eq

lemma empty (h : SetTheory.IsAttempt (c.core v) f) (hlh : ∅ ∈ lh f) : ⟨∅, c.core v ∅⟩ₖ ∈ f := by
  have hrestrict {g : V} : g ↾ ∅ = ∅ := restrict_empty_eq
  exact (h.2 ∅ hlh (c.core v ∅)).mpr (by aesop)

lemma succ (hf : SetTheory.IsAttempt (c.core v) f) : ∀ β, SetTheory.succ β ∈ lh f → ∀ y, ⟨β, y⟩ₖ ∈ f → ⟨SetTheory.succ β, c.core v ((f ↾ β) ⁀' y)⟩ₖ ∈ f := by
  intro β hβsucclh y hyf
  have hlh := isOrdinal_lh hf
  have := IsOrdinal.of_mem (h := hlh) hβsucclh
  have hβmemlh : β ∈ lh f :=
    IsTransitive.transitive (self := IsOrdinal.toIsTransitive (self := hlh)) (SetTheory.succ β) hβsucclh β (mem_succ_self (x := β))
  have := IsOrdinal.of_mem (h := hlh) hβmemlh
  have hβsubsetlh : β ⊆ lh f := (IsOrdinal.subset_iff (hβ := hlh)).mpr (Or.inr hβmemlh)
  have hy := (spec hf β hβmemlh y).mp hyf
  have hlh : lh (f ↾ β) = β := (hf.1.lh_restrict hβsubsetlh)
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
        refine And.intro ?_ (hf.1.IsFunction.unique (hxβ ▸ hy ▸ h₂.1) hyf)
        exact hxβ ▸ (hf.1.lh_restrict (α := β) hβsubsetlh).symm
    · rw [mem_restrict_iff]
      by_cases hw : w ∈ f ↾ β
      · refine And.intro (mem_restrict_iff.mp hw).1 ?_
        obtain ⟨x, hx, y, hxy⟩ := (mem_restrict_iff.mp hw).2
        exact ⟨x, mem_succ_iff.mpr (Or.inr hx), y, hxy⟩
      · rcases Or.resolve_right (mem_insert.mp h₂) hw with rfl
        refine And.intro (hlh.symm ▸ hyf) ⟨lh (f ↾ β), And.intro (hlh.symm ▸ (mem_succ_self β)) ⟨y, by simp⟩⟩
  exact (spec hf (SetTheory.succ β) hβsucclh _).mpr (by rw [hrestrict.symm])

lemma unique {f g α β : V} (h₁ : SetTheory.IsAttempt (c.core v) f) (h₂ : SetTheory.IsAttempt (c.core v) g)
    (hlh₁ : lh f = α) (hlh₂ : lh g = β)
    (h₁₂ : α ⊆ β) {γ} (hγα : γ ∈ α) {y₁ y₂} :
    ⟨γ, y₁⟩ₖ ∈ f → ⟨γ, y₂⟩ₖ ∈ g → y₁ = y₂ := by
  have : IsOrdinal α := hlh₁ ▸ isOrdinal_lh h₁
  have : IsOrdinal β := hlh₂ ▸ isOrdinal_lh h₂
  let αo : Ordinal V := IsOrdinal.toOrdinal α
  let βo : Ordinal V := IsOrdinal.toOrdinal β
  have hαtest : αo.val = α := by simp [αo]
  have hg := h₂.1.IsFunction
  have hrestrict : f ↾ α = g ↾ α :=
    IsAttempt.isAttempt_coherent (α := αo) (β := βo) h₁ h₂ (by aesop) (by aesop) αo (by aesop)
  intro hy₁ hy₂
  have h := (mem_ext_iff.mp hrestrict) ⟨γ, y₁⟩ₖ
  have hy₁g : ⟨γ, y₁⟩ₖ ∈ g := by simpa [kpair_mem_restrict_iff, hy₁, hγα] using fun h₂ ↦ h.mp h₂
  exact hg.unique hy₁g hy₂

end IsAttempt

/-! #### Various facts about attempt functions -/

lemma IsAttempt.initial {F : V → V} {f : V} (hf : IsAttempt F f) (hlh : ∅ ∈ lh f) : ⟨∅, F ∅⟩ₖ ∈ f := by
  have hrestrict {g : V} : g ↾ ∅ = ∅ := restrict_empty_eq
  exact (hf.2 ∅ hlh (F ∅)).mpr (by aesop)

lemma IsAttempt.successor {F : V → V} {f : V} (hf : IsAttempt F f) : IsAttempt F (f ⁀' (F f)) :=
  ⟨ hf.1.seqCons (F f), by
    intro β hβ w
    have := hf.1.IsFunction
    let α := lh f
    have : IsOrdinal α := SetTheory.isOrdinal_lh hf.1
    have : IsOrdinal (lh (f ⁀' (F f))) := Seq.lh_seqCons (F f) hf.1 ▸ IsOrdinal.succ
    have : IsOrdinal β := IsOrdinal.of_mem hβ
    have hβα : β ⊆ α := IsOrdinal.subset_iff.mpr (mem_succ_iff.mp (Seq.lh_seqCons (F f) hf.1 ▸ hβ))
    have hβdomain : β ⊆ domain f := hf.1.domain_eq ▸ hβα
    have hrestrictβ {z : V} : (f ⁀' z) ↾ β = f ↾ β :=
        restrict_insert_kpair_eq_restrict_of_not_mem (f := f) (x := lh f) (y := z) (A := β)
          fun h₂ ↦ mem_irrefl (lh f) (hf.1.domain_eq ▸ hβdomain (lh f) h₂)
    have hrestrictlh := IsFunction.restrict_eq_self f (lh f) (hf.1.domain_eq ▸ subset_refl (domain f))
    rw [hrestrictβ] at *
    rcases show β = α ∨ β ∈ α
        from IsOrdinal.subset_iff.mp hβα
        with (hβ | hβ)
    · have hβeq : β = lh f := hβ
      rw [hβeq, lh_mem_seqCons_iff hf.1, hrestrictlh]
    · have hβneq : β ≠ lh f := fun h ↦ mem_irrefl β (h ▸ hβ)
      rw [kpair_mem_seqCons_iff]
      refine Iff.intro (fun h ↦ ?_) fun h ↦ ?_
      · exact Or.elim h (by aesop) fun h ↦ (hf.2 β hβ w).mp h
      · exact Or.inr ((hf.2 β hβ w).mpr h)
  ⟩

lemma attempt_result_existsUnique (F : V → V) (hF : ℒₛₑₜ-function₁ F) (α : V) : ∃! y,
    (IsOrdinal α → ∃ f, SetTheory.IsAttempt F f ∧ lh f = SetTheory.succ α ∧ ⟨α, y⟩ₖ ∈ f) ∧
    (¬IsOrdinal α → y = ∅) := by
  by_cases hα : IsOrdinal α
  · let αo : Ordinal V := IsOrdinal.toOrdinal α
    let αsucco : Ordinal V := IsOrdinal.toOrdinal (SetTheory.succ α)
    rcases SetTheory.Replacement.attempt_function_exists F hF αsucco with ⟨f, hf, hlhf⟩
    have : ∃ z, ⟨α, z⟩ₖ ∈ f := hf.1.exists (show α ∈ lh f from by simp_all [αsucco])
    rcases this with ⟨z, hz⟩
    simp only [hα, not_true, true_implies, false_implies, and_true]
    exact ExistsUnique.intro z ⟨f, hf, by simpa, hz⟩ (by
      rintro z' ⟨f', hf', hlhf', hz'⟩
      exact Eq.symm <| SetTheory.IsAttempt.eq_of_isAttempt hf hf' hlhf hlhf' (by aesop) αo.lt_succ hz hz')
  · refine ExistsUnique.intro (∅ : V) (by aesop) fun y ↦ by aesop

noncomputable def result (α : V) : V := Classical.choose! (attempt_result_existsUnique (c.core v) (c.core_definable v) α)

-- TODO: The definability argument is the same here as in `result`. Adding a lemma which proves `ℒₛₑₜ-function₁ c.core v` would help to remove redundant code.
lemma result_spec (α : V) :
    (IsOrdinal α → ∃ f, SetTheory.IsAttempt (c.core v) f ∧ lh f = SetTheory.succ α ∧ ⟨α, c.result v α⟩ₖ ∈ f) ∧
    (¬IsOrdinal α → c.result v α = ∅) :=
  Classical.choose!_spec (attempt_result_existsUnique (c.core v) (c.core_definable v) α)

lemma result_spec_of_isOrdinal (α : V) [hα : IsOrdinal α] : ∃ f, SetTheory.IsAttempt (c.core v) f ∧ lh f = SetTheory.succ α ∧ ⟨α, c.result v α⟩ₖ ∈ f := by
  simpa [hα] using c.result_spec v α

@[simp] theorem result_empty : c.result v ∅ = c.core v ∅ := by
  rcases c.result_spec_of_isOrdinal v ∅ with ⟨f, hf, hlhf, hempty⟩
  exact hf.1.IsFunction.unique hempty (hf.empty (hlhf ▸ mem_succ_self ∅))

@[simp] theorem result_succ (α : V) [hα : IsOrdinal α] : c.result v (SetTheory.succ α) = c.core v (Classical.choose (Replacement.attempt_function_exists (c.core v) (c.core_definable v) (IsOrdinal.toOrdinal α).succ)) := by
  rcases c.result_spec_of_isOrdinal v α with ⟨f, hf, hlhf, h⟩
  let αo : Ordinal V := IsOrdinal.toOrdinal α
  have := hf.successor
  have hmemcons := hlhf.symm ▸ SetTheory.lh_mem_seqCons f (c.core v f)
  have hexists := Replacement.attempt_function_exists (c.core v) (c.core_definable v) αo.succ
  let g := Classical.choose hexists
  have hg := Classical.choose_spec hexists
  have heq : Classical.choose hexists = f := by
    exact Eq.symm <| IsAttempt.isAttempt_unique hf hg.1 (by aesop : lh f = αo.succ.val) hg.2
  rw [heq]
  exact Eq.symm
    <| Classical.choose_uniq (attempt_result_existsUnique (c.core v) (c.core_definable v) (SetTheory.succ α))
    ⟨ by
        simp only [IsOrdinal.succ, forall_const]
        exact ⟨f ⁀' c.core v f, this, hlhf ▸ Seq.lh_seqCons (c.core v f) hf.1, hlhf ▸ lh_mem_seqCons f (c.core v f)⟩
        ,
      by simp [IsOrdinal.succ]
    ⟩

lemma result_graph (y α : V) : y = c.result v α ↔
    (IsOrdinal α → ∃ f, SetTheory.IsAttempt (c.core v) f ∧ lh f = SetTheory.succ α ∧ ⟨α, y⟩ₖ ∈ f) ∧
    (¬IsOrdinal α → y = ∅) :=
  ⟨by rintro rfl
      refine And.intro (fun hα ↦ ?_) (fun hα ↦ ?_)
      · rcases (c.result_spec v α).1 hα with ⟨f, hf, h⟩
        exact ⟨f, hf, h⟩
      · exact (c.result_spec v α).2 hα,
   by
      rintro ⟨hleft, hright⟩
      by_cases hα : IsOrdinal α
      · rcases (c.result_spec v α).1 hα with ⟨f', hf', hlhf', h'⟩
        rcases hleft hα with ⟨f, hf, hlhf, h⟩
        let αo : Ordinal V := IsOrdinal.toOrdinal α
        exact Eq.symm <| hf'.eq_of_isAttempt hf (by aesop : lh f' = αo.succ) (by aesop : lh f = αo.succ)
          (le_refl αo.succ)
          (Ordinal.lt_succ αo) h' h
      · exact Eq.symm <| hright hα ▸ (c.result_spec v α).2 hα⟩

set_option linter.flexible false in
lemma result_defined : DefinedFunction (fun v ↦ c.result (v ·.succ) (v 0) : (Fin (k + 1) → V) → V) p.result_dfn := .mk fun v ↦ by
  simp [Blueprint.result_dfn, result_graph, c.eval_isAttempt_dfn, -and_congr_left_iff]
  refine and_congr ?_ ?_
  · refine eq_iff_iff.mp ?_
    refine implies_congr rfl ?_
    refine eq_iff_iff.mpr ?_
    refine Iff.intro (fun h ↦ ?_) (by aesop)
    · rcases h with ⟨f, hf, hmemf⟩
      exact ⟨f, hf, hmemf.1.symm, hmemf.2⟩
  · rfl

@[simp] lemma eval_resultDef {v} : p.result_dfn.Evalb v ↔ v 0 = c.result (v ·.succ.succ) (v 1) := c.result_defined.iff v

/- TODO: Once the Lévy hierarchy has been added, add a `Δ` version. -/
-- lemma result_defined_delta : DefinedFunction (fun v ↦ c.result (v ·.succ) (v 0) : (Fin (k + 1) → V) → V) p.resultDeltaDef :=
--   c.result_defined.graph_delta

@[simp] lemma result_defined_iff (v : Fin (k + 2) → V) :
    p.result_dfn.Evalb v ↔ v 0 = c.result (v ·.succ.succ) (v 1) := c.result_defined.iff v

instance result_definable : (ℒₛₑₜ).DefinableFunction (fun v ↦ c.result (v ·.succ) (v 0) : (Fin (k + 1) → V) → V) :=
  c.result_defined.to_definable

attribute [irreducible] Blueprint.result_dfn

end Construction

end Recursion
