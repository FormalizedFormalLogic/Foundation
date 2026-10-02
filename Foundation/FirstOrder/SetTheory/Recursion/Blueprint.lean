module

public import Foundation.FirstOrder.SetTheory.ZF
public import Foundation.FirstOrder.SetTheory.Recursion

@[expose] public section
/-!

# Blueprint wrapper for the recursion theorem in $\mathsf{ZF}$

-/

namespace FFL.FirstOrder.SetTheory.Recursion

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] {k : ℕ}

structure Blueprint (k : ℕ) where
  /-- `graph.Evalb (y :> x :> v)` states that `c.map v x = y`. -/
  graph : SetTheorySemisentence (k + 2)

def Blueprint.isAttempt_dfn (p : Blueprint k) : SetTheorySemisentence (k + 1) :=
  f“f.
    :Seq f ∧
    ∀ β ∈ !lh.dfn f, ∀ y, !kpair.dfn β y ∈ f ↔ y = !p.graph (!restrict.dfn f β) ⋯”

#check fun (φ : Semisentence ℒₒᵣ 3) ↦ (⤫term(faf)[ α x y |   | !φ α x ⋯ ] : Semisentence ℒₒᵣ 3)

/- TODO: I don't know how to write a literal formula while in faf notation, so I
specified `lh f = SetTheory.succ x` this way. -/
def Blueprint.result_dfn {k} (p : Blueprint k) : SetTheorySemisentence (k + 2) :=
  -- “y x. (!IsOrdinal.dfn x → ∃ f, !p.isAttempt_dfn f ⋯ ∧ x ∼[f] y) ∧
  --   (¬!IsOrdinal.dfn x → !isEmpty y)”
  “y x. (!IsOrdinal.dfn x → ∃ f, !p.isAttempt_dfn f ⋯ ∧
      (∀ z, !SetTheory.succ.dfn z x → !lh.dfn z f) ∧ x ∼[f] y) ∧
    (¬!IsOrdinal.dfn x → !isEmpty y)”

/- TODO: Once the Lévy hierarchy has been added, add a `Δ` version. -/
-- def Blueprint.resultDeltaDef (p : Blueprint k) : SetTheorySemisentence (k + 2) :=
--   p.result.dfn.graphDelta

variable (V)

structure Construction {k : ℕ} (p : Blueprint k) where
  /-- `c.map v` is the function `F : V → V` which transfinite recursion is performed on,
  analogously to `c.succ` in arithmetic. -/
  map : (Fin k → V) → V → V
  map_defined : DefinedFunction (fun v ↦ map (v ·.succ) (v 0)) p.graph

variable {V}

namespace Construction

variable {k : ℕ} {p : Blueprint k} (c : Construction V p) (v : Fin k → V)

instance map_definable : ℒₛₑₜ-function₁ c.map v := by
  refine ⟨(Rew.embSubsts (#0 :> #1 :> fun i : Fin k ↦ &(v i))) ▹ p.graph, ?_⟩
  intro x
  simpa [Semiformula.eval_embSubsts, Matrix.comp_vecCons', Function.comp_def]
    using c.map_defined.iff (x 0 :> x 1 :> v)

-- An example showing that `⋯` in faf notation is implemented correctly.
set_option linter.flexible false in
example : Semiformula.Evalb v f“∀ x, ∃ y, y = !p.graph x ⋯” := by
  simp
  intro x
  use c.map v x
  intro z h
  have heq : ((“#0 = #3” : SetTheorySemisentence (k + 4)) :>
      fun (x : Fin k) ↦ “#0 = #x.succ.succ.succ.succ”) = fun x ↦ “#0 = #x.succ.succ.succ” := by
    apply funext_iff.mpr
    intro x
    by_cases hx : 0 ≠ x
    · obtain ⟨y, hy⟩ := Fin.exists_succ_eq.mpr hx.symm
      aesop
    · aesop
  suffices Semiformula.Evalb (z :> x :> v) p.graph by
    apply (c.map_defined.iff (z :> x :> v)).mp at this
    simp at this
    exact this.symm
  simp only [Semiformula.eval_nestFormulaeFunc, Nat.succ_eq_add_one, ← Semiformula.Evalb.eq_1] at h
  specialize h (x :> v)
  simpa [heq] using h

set_option linter.flexible false in
omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
lemma eval_map_faf {x : V} :
    Semiformula.Evalb (x :> (c.map v x) :> v) f“x y. y = !p.graph x ⋯” := by
  simp
  intro z h
  suffices Semiformula.Evalb (z :> x :> v) p.graph by
    apply (c.map_defined.iff (z :> x :> v)).mp at this
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
lemma isAttempt_defined : Defined (fun v ↦ SetTheory.IsAttempt (c.map (v ·.succ)) (v 0) :
    (Fin (k + 1) → V) → Prop) p.isAttempt_dfn := .mk fun v ↦ by
  have hsplit {p : Fin (k + 1) → Prop} :
      (∀ i : Fin (k + 1), p i) ↔ (p 0 ∧ ∀ i : Fin k, p i.succ) := by
    refine Iff.intro (fun h ↦ ⟨h 0, fun i ↦ h (i.succ)⟩) fun h i ↦ ?_
    apply by_cases (p := i = 0) (q := p i) (by aesop)
    intro hi
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
  simp [hsplit, c.map_defined.iff]
  simp only [← eq_iff_iff (a := ⟨x, y⟩ₖ ∈ v 0)]
  apply eq_iff_eq_cancel_left.mpr
  simp only [eq_iff_iff]
  constructor <;> intro h
  · specialize h (c.map (fun x ↦ v x.succ) ((v 0) ↾ x))
    refine h ?_
    intro v_1 h₂
    aesop
  · intro x_1 h₂
    specialize h₂ (((v 0) ↾ x) :> (Matrix.vecTail v))
    subst h
    simp_all only [Matrix.cons_val_zero, Matrix.cons_val_succ, forall_const]
    refine (h₂ ?_).symm
    aesop

@[simp] lemma eval_isAttempt_dfn {v} : p.isAttempt_dfn.Evalb v ↔
  SetTheory.IsAttempt (c.map (v ·.succ)) (v 0) := c.isAttempt_defined.iff v

-- @[simp] lemma isAttempt_defined_iff (v : Fin (k + 1) → V) :
--     Semiformula.Evalb v p.isAttempt_dfn ↔ c.IsAttempt (v ·.succ) (v 0) :=
--   c.isAttempt_defined.iff v

namespace IsAttempt

variable {c v} {f : V}

lemma seq (h : SetTheory.IsAttempt (c.map v) f) : Seq f := h.1

variable (f) in
lemma isOrdinal_lh : IsOrdinal (lh f) := SetTheory.isOrdinal_lh f

lemma spec (h : SetTheory.IsAttempt (c.map v) f) :
    ∀ β ∈ lh f, ∀ y, ⟨β, y⟩ₖ ∈ f ↔ y = c.map v (f ↾ β) := h.2

lemma domain_eq_lh (hf : SetTheory.IsAttempt (c.map v) f) : domain f = lh f := hf.1.domain_eq

lemma empty (h : SetTheory.IsAttempt (c.map v) f) (hlh : ∅ ∈ lh f) : ⟨∅, c.map v ∅⟩ₖ ∈ f := by
  have hrestrict {g : V} : g ↾ ∅ = ∅ := restrict_empty_eq
  exact (h.2 ∅ hlh (c.map v ∅)).mpr (by aesop)

lemma succ (hf : SetTheory.IsAttempt (c.map v) f) : ∀ β, SetTheory.succ β ∈ lh f →
    ∀ y, ⟨β, y⟩ₖ ∈ f → ⟨SetTheory.succ β, c.map v ((f ↾ β) ⁀' y)⟩ₖ ∈ f := by
  intro β hβsucclh y hyf
  have hlh := isOrdinal_lh f
  have := IsOrdinal.of_mem (h := hlh) hβsucclh
  have hβmemlh : β ∈ lh f :=
    IsTransitive.transitive (self := IsOrdinal.toIsTransitive (self := hlh))
      (SetTheory.succ β) hβsucclh β (mem_succ_self (x := β))
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
      · obtain ⟨x, hx, y, hxy⟩ := (mem_restrict_iff.mp hw).2
        exact ⟨(mem_restrict_iff.mp hw).1, ⟨x, mem_succ_iff.mpr (Or.inr hx), y, hxy⟩⟩
      · rcases Or.resolve_right (mem_insert.mp h₂) hw with rfl
        exact And.intro (hlh.symm ▸ hyf) ⟨lh (f ↾ β),
          And.intro (hlh.symm ▸ (mem_succ_self β)) ⟨y, by simp⟩⟩
  exact (spec hf (SetTheory.succ β) hβsucclh _).mpr (by rw [hrestrict.symm])

lemma unique {f g : V}
    (h₁ : SetTheory.IsAttempt (c.map v) f)
    (h₂ : SetTheory.IsAttempt (c.map v) g)
    {γ y₁ y₂} :
    ⟨γ, y₁⟩ₖ ∈ f → ⟨γ, y₂⟩ₖ ∈ g → y₁ = y₂ := by
  intro hy₁ hy₂
  have : IsOrdinal (lh f) := SetTheory.isOrdinal_lh f
  have : IsOrdinal (lh g) := SetTheory.isOrdinal_lh g
  have : IsOrdinal γ := h₁.1.isOrdinal_of_mem_domain (mem_domain_of_kpair_mem hy₁)
  let αo : Ordinal V := IsOrdinal.toOrdinal (lh f)
  let βo : Ordinal V := IsOrdinal.toOrdinal (lh g)
  let γo : Ordinal V := IsOrdinal.toOrdinal γ
  exact IsAttempt.eq_of_isAttempt h₁ h₂ (γ := γo) hy₁ hy₂

end IsAttempt

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
      exact Eq.symm <|
        SetTheory.IsAttempt.eq_of_isAttempt hf hf' (γ := αo) hz hz')
  · refine ExistsUnique.intro (∅ : V) (by aesop) fun y ↦ by aesop

noncomputable def result (α : V) : V :=
  Classical.choose! (attempt_result_existsUnique (c.map v) (c.map_definable v) α)

/- TODO: The definability argument is the same here as in `result`. Adding a lemma which
proves `ℒₛₑₜ-function₁ c.map v` would help to remove redundant code. -/
lemma result_spec (α : V) :
    (IsOrdinal α → ∃ f, SetTheory.IsAttempt (c.map v) f ∧
        lh f = SetTheory.succ α ∧ ⟨α, c.result v α⟩ₖ ∈ f) ∧
    (¬IsOrdinal α → c.result v α = ∅) :=
  Classical.choose!_spec (attempt_result_existsUnique (c.map v) (c.map_definable v) α)

lemma result_spec_of_isOrdinal (α : V) [hα : IsOrdinal α] :
    ∃ f, SetTheory.IsAttempt (c.map v) f ∧ lh f = SetTheory.succ α ∧ ⟨α, c.result v α⟩ₖ ∈ f := by
  simpa [hα] using c.result_spec v α

@[aesop safe] lemma result_not_isOrdinal (α : V) (hα : ¬IsOrdinal α) : c.result v α = ∅ := by
  simpa [hα] using c.result_spec v α

lemma result_eq_of_mem {f y} (α : V) (hf : IsAttempt (c.map v) f) (hmemf : ⟨α, y⟩ₖ ∈ f) :
    y = c.result v α := by
  have := hf.1.isOrdinal_of_mem_domain (mem_domain_of_kpair_mem hmemf)
  rcases c.result_spec_of_isOrdinal v α with ⟨f', hf', hlhf, hmemf'⟩
  exact IsAttempt.unique hf hf' hmemf hmemf'

@[simp] theorem result_empty : c.result v ∅ = c.map v ∅ := by
  rcases c.result_spec_of_isOrdinal v ∅ with ⟨f, hf, hlhf, hempty⟩
  exact hf.1.IsFunction.unique hempty (IsAttempt.empty hf (hlhf ▸ mem_succ_self ∅))

lemma result_succ (α : V) [hα : IsOrdinal α] :
    c.result v (SetTheory.succ α) = c.map v (repl (fun β ↦ ⟨β, c.result v β⟩ₖ) sorry (succ α)) := by
  classical
  let αo : Ordinal V := IsOrdinal.toOrdinal α
  obtain ⟨f, hf, hlhf, hmemf⟩ := c.result_spec_of_isOrdinal v (succ α)
  rw [(IsAttempt.spec hf (succ α) (by aesop) _).mp hmemf]
  refine (?_ : f ↾ (succ α) = repl (fun β ↦ ⟨β, c.result v β⟩ₖ) sorry (succ α)) ▸ rfl
  ext p
  rw [mem_restrict_iff, repl_spec]
  refine ⟨fun ⟨hmem, x, hx, y, _⟩ ↦ ?_, fun ⟨x, hx, _⟩ ↦ ?_⟩
  · subst p
    exact ⟨x, hx, c.result_eq_of_mem v x hf hmem ▸ rfl⟩
  · subst p
    have : IsOrdinal x := IsOrdinal.of_mem hx
    let xo : Ordinal V := IsOrdinal.toOrdinal x
    have hle : xo.succ ≤ αo.succ.succ :=
      Ordinal.le_def.mpr (Ordinal.succ_val xo ▸ (Ordinal.subset_succ_iff.mpr
        (mem_succ_iff.mpr (.inr hx))))
    obtain ⟨f', hf', hlhf', hmemf'⟩ := c.result_spec_of_isOrdinal v xo
    have heq : f ↾ (succ x) = f' :=
      IsAttempt.isAttempt_restrict_eq_of_le (α := αo.succ.succ) (β := xo.succ) hle hf hf' hlhf hlhf'
    exact ⟨(heq ▸ SetTheory.restrict_subset f (succ x)) _ hmemf', ⟨x, hx, c.result v x, rfl⟩⟩

lemma result_succ_of_isAttempt {f} (α : V) [hα : IsOrdinal α]
    (hf : IsAttempt (c.map v) f) (hlhf : lh f = succ α) :
    c.result v (SetTheory.succ α) = c.map v f := by
  let αo : Ordinal V := IsOrdinal.toOrdinal α
  have huniq := by
    simpa [IsOrdinal.succ] using attempt_result_existsUnique (c.map v) (c.map_definable v) (succ α)
  obtain ⟨y, ⟨f', hf', hlhf', hmemf'⟩, hyuniq⟩ := huniq
  have hrestrict : f = f' ↾ (succ α) :=
    Eq.symm <| IsAttempt.isAttempt_restrict_eq_of_le (α := αo.succ.succ) (β := αo.succ)
      (le_of_lt (by simp)) hf' hf hlhf' hlhf
  rw [hyuniq (c.map v f)
    (by
      refine ⟨f', hf', hlhf', ?_⟩
      exact (hf'.2 (succ α) (hlhf' ▸ mem_succ_self (succ α)) (c.map v f)).mpr (hrestrict ▸ rfl))
    ]
  exact Eq.symm <| c.result_eq_of_mem v (succ α) hf' hmemf'

lemma result_graph (y α : V) : y = c.result v α ↔
    (IsOrdinal α → ∃ f, SetTheory.IsAttempt (c.map v) f ∧ lh f = SetTheory.succ α ∧ ⟨α, y⟩ₖ ∈ f) ∧
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
        exact Eq.symm <|
          hf'.eq_of_isAttempt hf (γ := αo) h' h
      · exact Eq.symm <| hright hα ▸ (c.result_spec v α).2 hα⟩

set_option linter.flexible false in
lemma result_defined : DefinedFunction (fun v ↦ c.result (v ·.succ) (v 0) : (Fin (k + 1) → V) → V)
    p.result_dfn := .mk fun v ↦ by
  simp [Blueprint.result_dfn, result_graph, c.eval_isAttempt_dfn, -and_congr_left_iff]
  refine and_congr ?_ ?_
  · refine eq_iff_iff.mp ?_
    refine implies_congr rfl ?_
    refine eq_iff_iff.mpr ?_
    refine Iff.intro (fun h ↦ ?_) (by aesop)
    · rcases h with ⟨f, hf, hmemf⟩
      exact ⟨f, hf, hmemf.1.symm, hmemf.2⟩
  · rfl

/- TODO: Once the Lévy hierarchy has been added, add a `Δ` version. -/
-- lemma result_defined_delta : DefinedFunction
--     (fun v ↦ c.result (v ·.succ) (v 0) : (Fin (k + 1) → V) → V) p.resultDeltaDef :=
--   c.result_defined.graph_delta

@[simp] lemma result_defined_iff (v : Fin (k + 2) → V) :
    p.result_dfn.Evalb v ↔ v 0 = c.result (v ·.succ.succ) (v 1) := c.result_defined.iff v

instance result_definable : (ℒₛₑₜ).DefinableFunction
    (fun v ↦ c.result (v ·.succ) (v 0) : (Fin (k + 1) → V) → V) :=
  c.result_defined.to_definable

attribute [irreducible] Blueprint.result_dfn

end FFL.FirstOrder.SetTheory.Recursion.Construction
