module

public import Foundation.FirstOrder.SetTheory.Recursion.Seq
public import Foundation.FirstOrder.SetTheory.ZF
-- public import Foundation.FirstOrder.SetTheory.Recursion

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
    -- !IsOrdinal.dfn α ∧ !IsFunction.dfn f ∧ !domain.dfn f = α ∧
    ∀ β ∈ !lh.dfn f, ∀ y, !kpair.dfn β y ∈ f ↔ y = !p.graph (!restrict.dfn f β) ⋯”

#check fun (φ : Semisentence ℒₒᵣ 3) ↦ (⤫term(faf)[ α x y |   | !φ α x ⋯ ] : Semisentence ℒₒᵣ 3)

def Blueprint.result_dfn {k} (p : Blueprint k) : SetTheorySemisentence (k + 2) :=
  “y x. (!IsOrdinal.dfn x → ∃ f, !p.isAttempt_dfn f ⋯ ∧ x ∼[f] y) ∧
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

/--
`f` is an attempt of length `α` for the function `F`, meaning that the domain of `f` is `α`, and for all `β < α`, it holds that `f(β) = F (f ↾ β)`.
The "attempt" terminology may be due to Paul Taylor.
-/
def IsAttempt (f : V) : Prop :=
  Seq f ∧
    ∀ β ∈ lh f, ∀ y, ⟨β, y⟩ₖ ∈ f ↔ y = c.core v (f ↾ β)

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
lemma isAttempt_defined : Defined (fun v ↦ c.IsAttempt (v ·.succ) (v 0) : (Fin (k + 1) → V) → Prop) p.isAttempt_dfn := .mk fun v ↦ by
  have hsplit {p : Fin (k + 1) → Prop} : (∀ i : Fin (k + 1), p i) ↔ (p 0 ∧ ∀ i : Fin k, p i.succ) := by
    constructor <;> intro h
    · exact And.intro (h 0) fun i ↦ h (i.succ)
    · intro i
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

@[simp] lemma isAttempt_defined_iff (v : Fin (k + 1) → V) :
    Semiformula.Evalb v p.isAttempt_dfn ↔ c.IsAttempt (v ·.succ) (v 0) := c.isAttempt_defined.iff v

namespace IsAttempt

variable {c v} {f : V}

lemma seq (h : c.IsAttempt v f) : Seq f := h.1

lemma isOrdinal_lh (hf : c.IsAttempt v f) : IsOrdinal (lh f) := SetTheory.isOrdinal_lh hf.seq

lemma spec (h : c.IsAttempt v f) : ∀ β ∈ lh f, ∀ y, ⟨β, y⟩ₖ ∈ f ↔ y = c.core v (f ↾ β) := h.2

lemma domain_eq_lh (hf : c.IsAttempt v f) : domain f = lh f := hf.seq.domain_eq

lemma empty (h : c.IsAttempt v f) (hlh : ∅ ∈ lh f) : ⟨∅, c.core v ∅⟩ₖ ∈ f := by
  have hrestrict {g : V} : g ↾ ∅ = ∅ := restrict_empty_eq
  exact (h.2 ∅ hlh (c.core v ∅)).mpr (by aesop)

-- lemma succ (h : c.IsAttempt v α f) : ∀ β, SetTheory.succ β ∈ α → ∀ y, ⟨β, y⟩ₖ ∈ f → ⟨SetTheory.succ β, c.core v (insert ⟨β, y⟩ₖ (f ↾ β))⟩ₖ ∈ f := by
lemma succ (hf : c.IsAttempt v f) : ∀ β, SetTheory.succ β ∈ lh f → ∀ y, ⟨β, y⟩ₖ ∈ f → ⟨SetTheory.succ β, c.core v ((f ↾ β) ⁀' y)⟩ₖ ∈ f := by
  intro β hβsucclh y hyf
  have hlh := hf.isOrdinal_lh
  have := IsOrdinal.of_mem (h := hlh) hβsucclh
  have hβmemlh : β ∈ lh f :=
    IsTransitive.transitive (self := IsOrdinal.toIsTransitive (self := hlh)) (SetTheory.succ β) hβsucclh β (mem_succ_self (x := β))
  have := IsOrdinal.of_mem (h := hlh) hβmemlh
  have hβsubsetlh : β ⊆ lh f := (IsOrdinal.subset_iff (hβ := hlh)).mpr (Or.inr hβmemlh)
  have hy := (spec hf β hβmemlh y).mp hyf
  have hlh : lh (f ↾ β) = β := (hf.seq.lh_restrict hβsubsetlh)
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
        exact hxβ ▸ (hf.seq.lh_restrict (α := β) hβsubsetlh).symm
    · rw [mem_restrict_iff]
      by_cases hw : w ∈ f ↾ β
      · refine And.intro (mem_restrict_iff.mp hw).1 ?_
        obtain ⟨x, hx, y, hxy⟩ := (mem_restrict_iff.mp hw).2
        exact ⟨x, mem_succ_iff.mpr (Or.inr hx), y, hxy⟩
      · rcases Or.resolve_right (mem_insert.mp h₂) hw with rfl
        refine And.intro (hlh.symm ▸ hyf) ⟨lh (f ↾ β), And.intro (hlh.symm ▸ (mem_succ_self β)) ⟨y, by simp⟩⟩
  exact (spec hf (SetTheory.succ β) hβsucclh _).mpr (by rw [hrestrict.symm])

lemma isAttempt_coherent {α β : Ordinal V} {f g : V}
    (hf : c.IsAttempt v f) (hg : c.IsAttempt v g)
    (hlhf : lh f = α) (hlhg : lh g = β) :
    ∀ γ : Ordinal V, γ.val ⊆ α.val ∧ γ.val ⊆ β.val → f ↾ γ.val = g ↾ γ.val := by
  rcases hf with ⟨_, _⟩
  rcases hg with ⟨_, _⟩
  refine transfinite_induction (P := fun x ↦ x ⊆ α.val ∧ x ⊆ β.val → f ↾ x = g ↾ x) (by definability) ?_
  rintro γ ihγ ⟨hγα, hγβ⟩
  ext p
  simp only [mem_restrict_iff, and_congr_left_iff, forall_exists_index, and_imp]
  intro x hxγ y rfl
  have : IsOrdinal x := IsOrdinal.of_mem hxγ
  let xo : Ordinal V := IsOrdinal.toOrdinal x
  have hxα : x ∈ α.val := hγα x hxγ
  have hxβ : x ∈ β.val := hγβ x hxγ
  have hxoα : xo.val ⊆ α.val := α.ordinal.toIsTransitive.transitive x hxα
  have hxoβ : xo.val ⊆ β.val := β.ordinal.toIsTransitive.transitive x hxβ
  have : f ↾ xo = g ↾ xo := ihγ xo hxγ ⟨hxoα, hxoβ⟩
  simp_all only [IsOrdinal.toOrdinal_val, xo]

lemma unique {f g α β : V} (h₁ : c.IsAttempt v f) (h₂ : c.IsAttempt v g)
    (hlh₁ : lh f = α) (hlh₂ : lh g = β)
    (h₁₂ : α ⊆ β) {γ} (hγα : γ ∈ α) {y₁ y₂} :
    ⟨γ, y₁⟩ₖ ∈ f → ⟨γ, y₂⟩ₖ ∈ g → y₁ = y₂ := by
  have : IsOrdinal α := hlh₁ ▸ SetTheory.isOrdinal_lh h₁.seq
  have : IsOrdinal β := hlh₂ ▸ SetTheory.isOrdinal_lh h₂.seq
  let αo : Ordinal V := IsOrdinal.toOrdinal α
  let βo : Ordinal V := IsOrdinal.toOrdinal β
  have hαtest : αo.val = α := by simp [αo]
  have hg := h₂.1.IsFunction
  have hrestrict : f ↾ α = g ↾ α :=
    isAttempt_coherent (α := αo) (β := βo) h₁ h₂ (by aesop) (by aesop) αo (by aesop)
  intro hy₁ hy₂
  have h := (mem_ext_iff.mp hrestrict) ⟨γ, y₁⟩ₖ
  have hy₁g : ⟨γ, y₁⟩ₖ ∈ g := by simpa [kpair_mem_restrict_iff, hy₁, hγα] using fun h₂ ↦ h.mp h₂
  exact hg.unique hy₁g hy₂

/--
An attempt function of length `α`, if existing, is unique.
-/
lemma eq_of_isAttempt {f g : V}
    (hf : c.IsAttempt v f) (hg : c.IsAttempt v g)
    (hlh : lh f = lh g) :
    f = g := by
  have := hf.seq.IsFunction
  have := hg.seq.IsFunction
  have := SetTheory.isOrdinal_lh hf.seq
  let αo : Ordinal V := IsOrdinal.toOrdinal (lh f)
  have hflh : f ↾ αo = f := IsFunction.restrict_eq_self f αo (subset_of_eq (by simp [αo, hf.seq.domain_eq]))
  have hglh : g ↾ αo = g := IsFunction.restrict_eq_self g αo (subset_of_eq (by simp [αo, hg.seq.domain_eq, hlh]))
  simpa [hflh, hglh] using isAttempt_coherent hf hg (by aesop) (by aesop) αo ⟨subset_refl αo.val, subset_refl αo.val⟩

/--
If `β ≤ α`, then an attempt function on `α` restricts to the attempt function on `β`.
-/
lemma isAttempt_restrict_eq_of_le
    {α β : Ordinal V} {f g : V}
    (hβα : β ≤ α)
    (hf : c.IsAttempt v f)
    (hg : c.IsAttempt v g)
    (hlhf : lh f = α)
    (hlhg : lh g = β) :
    f ↾ β.val = g := by
  have := hf.seq.IsFunction
  have := hg.seq.IsFunction
  have hsubset : domain g ⊆ β.val := subset_of_eq (hg.domain_eq_lh ▸ hlhg)
  exact isAttempt_coherent hf hg hlhf hlhg β ⟨hβα, subset_refl β.val⟩ ▸ IsFunction.restrict_eq_self g β.val hsubset

/-! #### Existence and choices of attempt functions -/

/-- Existence of an attempt function of a given length. -/
def Exists (α : V) : Prop :=
  ∃ f : V, c.IsAttempt v f ∧ lh f = α

/-- `Exists` implies `∃!`. -/
lemma existsUnique_of_exists (α : V) (hex : Exists (c := c) (v := v) α) :
    ∃! f : V, c.IsAttempt v f ∧ lh f = α := by
  obtain ⟨f, hf, hlhf⟩ := hex
  have : IsFunction f := hf.seq.IsFunction
  refine ⟨f, hf, ?_⟩
  intro g hg
  have : IsFunction g := hg.1.seq.IsFunction
  have hα : IsOrdinal α := hf.2 ▸ hf.1.isOrdinal_lh
  let αo : Ordinal V := IsOrdinal.toOrdinal α
  apply (eq_of_isAttempt (α := αo) hf hg hlhf hlhg).symm

end IsAttempt

/--
This lemma is originally by tosiaki.
-/
lemma attemptOrEmpty_existsUnique (α : V) : ∃! y,
    (Construction.IsAttempt.Exists (c := c) (v := v) α → c.IsAttempt v y ∧ lh y = α) ∧
    (¬Construction.IsAttempt.Exists (c := c) (v := v) α → y = ∅) := by
  by_cases hexists : Construction.IsAttempt.Exists (c := c) (v := v) α <;> simp only [hexists, not_false_eq_true, true_implies, false_implies, true_and]
  · obtain ⟨f, hf, huniq⟩ := IsAttempt.existsUnique_of_exists α hexists
    exact ⟨f, by simpa using hf, fun y hy ↦ by aesop⟩
  · exact existsUnique_of_exists_of_unique ⟨∅, rfl⟩ (by aesop)

/--
An attempt of length `α`, or `∅` if one doesn't exist.
This definition is by tosiaki.
-/
noncomputable def attemptOrEmpty (α : V) : V :=
  Classical.choose! (attemptOrEmpty_existsUnique (c := c) v α)

/--
A pair `⟨α, F f⟩ₖ` of an ordinal `α` and the value of `F` on `attemptOrEmpty F α`.
This is a technical definition needed for the proof of the transfinite recursion theorem.
-/
noncomputable def pairValueAttempt (α : V) : V :=
  ⟨α, c.core v (attemptOrEmpty (c := c) v α)⟩ₖ

lemma kpair_eq_pairValueAttempt_iff {α : V} {x y : V} :
    ⟨x, y⟩ₖ = c.pairValueAttempt v α ↔ x = α ∧ y = c.core v (attemptOrEmpty (c := c) (v := v) α) := by
  simp [pairValueAttempt]

lemma eq_of_kpair_eq_pairValueAttempt {α : V} {x y : V} (h : ⟨x, y⟩ₖ = pairValueAttempt (c := c) (v := v) α) : x = α :=
  ((c.kpair_eq_pairValueAttempt_iff v).mp h).1

/-! #### Constructing attempt functions using replacement -/

namespace Replacement

/--
Function that outputs an attempt of length `α`, subject to the assumption that for all `β < α`, there is an attempt of length `β`.
This is a big function constructed using replacement.
-/
noncomputable def replAttemptOrEmpty : V → V :=
  repl (c.pairValueAttempt (v := v)) (hF := by
    have : ℒₛₑₜ-function₁ c.attemptOrEmpty (v := v) := by
      suffices ℒₛₑₜ-relation[V] (· = c.attemptOrEmpty (v := v) ·) by exact this
      simp only [attemptOrEmpty, Classical.choose!_eq_iff_right]
      unfold IsAttempt.Exists
      have : ℒₛₑₜ-relation (c.IsAttempt v) := c.isAttempt_defined.to_definable
      sorry
      definability
    unfold pairValueAttempt
    definability)

@[simp] lemma mem_replAttemptOrEmpty_iff
    (α : V) (p : V) :
    p ∈ replAttemptOrEmpty (c := c) (v := v) α ↔ ∃ β ∈ α, p = c.pairValueAttempt (v := v) β := by
  apply repl_spec

@[simp] lemma kpair_mem_replAttemptOrEmpty_iff
    {α : Ordinal V} {β y : V} :
    ⟨β, y⟩ₖ ∈ replAttemptOrEmpty (c := c) (v := v) α ↔ β ∈ α.val ∧ ⟨β, y⟩ₖ = c.pairValueAttempt (v := v) β := by
  simp only [mem_replAttemptOrEmpty_iff]
  constructor <;> intro h
  · obtain ⟨β, hβα, h⟩ := h
    rw [eq_of_kpair_eq_pairValueAttempt h] at *
    exact ⟨hβα, h⟩
  · use β

lemma domain_replAttemptOrEmpty_eq (α : Ordinal V) :
    domain (replAttemptOrEmpty (c := c) (v := v) α) = α.val := by
  ext z
  simp only [mem_domain_iff, mem_replAttemptOrEmpty_iff]
  constructor <;> intro h
  · obtain ⟨y, β, hβα, hβ⟩ := h
    exact eq_of_kpair_eq_pairValueAttempt hβ ▸ hβα
  · use c.core v (attemptOrEmpty F z)
    use z
    simp_all only [true_and, pairValueAttempt, true_and]

instance (α : Ordinal V) : IsFunction (replAttemptOrEmpty (c := c) (v := v) α) := by
  let f := replAttemptOrEmpty (c := c) (v := v) α
  have hdomain : domain f = α.val := domain_replAttemptOrEmpty_eq (c := c) (v := v) α
  apply isFunction_iff.mpr
  apply mem_function_iff.mpr
  constructor
  · intro p hpf
    obtain ⟨β, _, f, rfl, _⟩ := (mem_replAttemptOrEmpty_iff (c := c) (v := v) _ _).mp hpf
    apply kpair_mem_iff.mpr
    exact And.intro (mem_domain_of_kpair_mem hpf) (mem_range_of_kpair_mem hpf)
  · intro x hx
    simp only [kpair_mem_replAttemptOrEmpty_iff]
    apply existsUnique_of_exists_of_unique
    · rw [hdomain] at hx
      exact ⟨c.core v (c.attemptOrEmpty (v := v) x), And.intro hx (pairValueAttempt.eq_1 (c := c) (v := v) x)⟩
    · intro y₁ y₂
      simp_all only [pairValueAttempt, kpair_iff, true_and, implies_true]

/--
An auxiliary lemma about `replAttemptOrEmpty`.
-/
lemma replAttemptOrEmpty_aux :
    (α : Ordinal V) → c.IsAttempt v (replAttemptOrEmpty (c := c) (v := v) α) := by
  let motive (α : V) : Prop := c.IsAttempt v α (replAttemptOrEmpty (c := c) (v := v) α)

  have := c.isAttempt_defined.to_definable
  have : ℒₛₑₜ-function₁ replAttemptOrEmpty (c := c) (v := v) := by
    unfold replAttemptOrEmpty
    definability
  have motive_definable : ℒₛₑₜ-predicate motive := by
    unfold motive
    definability
  refine transfinite_induction motive motive_definable ?_
  intro α ih
  have hα := Ordinal.ordinal α

  have hrestrict : ((β : V) → (hβα : β ∈ α.val) → c.IsAttempt v β ((replAttemptOrEmpty (c := c) (v := v) α) ↾ β)) := by
    intro β hβα
    have hβ : IsOrdinal β := IsOrdinal.of_mem hβα
    let βo : Ordinal V := IsOrdinal.toOrdinal β
    have haux := ih βo hβα

    suffices h : (replAttemptOrEmpty (c := c) (v := v) α) ↾ β = replAttemptOrEmpty (c := c) (v := v) β from h ▸ haux
    ext p
    simp only [mem_restrict_iff, mem_replAttemptOrEmpty_iff]
    constructor <;> intro h
    · rcases h with ⟨⟨γ, hγα, hγ⟩, ⟨x, hxβ, y, rfl⟩⟩
      use x
      refine And.intro hxβ ?_
      exact (eq_of_kpair_eq_pairValueAttempt hγ).symm ▸ hγ
    · obtain ⟨γ, hγβ, hγ⟩ := h
      refine And.intro ?_ ?_
      · use γ
        exact And.intro (IsTransitive.mem_trans IsOrdinal.toIsTransitive hγβ hβα) hγ
      · exact ⟨γ, hγβ, c.core v (attemptOrEmpty (c := c) (v := v) γ), hγ⟩
  refine ⟨hα, inferInstance, domain_replAttemptOrEmpty_eq (c := c) (v := v) α, ?_⟩
  intro β hβα y
  have hβ : IsOrdinal β := IsOrdinal.of_mem hβα
  let βo : Ordinal V := IsOrdinal.toOrdinal β

  suffices h : ⟨β, y⟩ₖ ∈ replAttemptOrEmpty (c := c) (v := v) α.val ↔ ∃ f, y = F f ∧ c.IsAttempt v β f from by
    constructor <;> intro h₂
    · obtain ⟨f, rfl, hf⟩ := h.mp h₂
      have : IsFunction f := hf.2.1
      have : IsFunction ((replAttemptOrEmpty (c := c) (v := v) (↑α)) ↾ ↑βo) := inferInstance
      simp only [IsAttempt.isAttempt_unique hf (hrestrict βo hβα), IsOrdinal.toOrdinal_val, βo]
    · apply h.mpr
      use (replAttemptOrEmpty (c := c) (v := v) (↑α)) ↾ β
      simp only [h₂, true_and]
      exact hrestrict βo hβα
  have hexists : IsAttempt.Exists (c := c) (v := v) β := ⟨replAttemptOrEmpty (c := c) (v := v) β, ih βo hβα⟩
  simp_all only [mem_replAttemptOrEmpty_iff, pairValueAttempt, kpair_iff, ↓existsAndEq, true_and,
    motive]
  have hattempt : c.IsAttempt v β (c.attemptOrEmpty (v := v) β) := by
    simp_all [attemptOrEmpty, Classical.choose!_spec]
  constructor <;> intro h
  · use c.attemptOrEmpty (v := v) β
  · obtain ⟨f, hfleft, hfright⟩ := h
    have heq := IsOrdinal.toOrdinal_val β
    rw [← heq] at *
    have := hfright.2.1
    have := hattempt.2.1
    exact (IsAttempt.isAttempt_unique hfright hattempt) ▸ hfleft

/--
For any ordinal `α`, there exists an attempt function of length `α`.
-/
lemma attempt_function_exists :
    (α : Ordinal V) → IsAttempt.Exists (c := c) (v := v) α :=
  fun α ↦ ⟨replAttemptOrEmpty (c := c) (v := v) α, replAttemptOrEmpty_aux (c := c) (v := v) α⟩

end Replacement

end Somethingidk

lemma IsAttempt.zero : c.IsAttempt v 0 ∅ :=
  ⟨by simp, by aesop, fun β hβ ↦ False.elim (not_mem_empty hβ)⟩

lemma IsAttempt.one : c.IsAttempt v 1 {⟨∅, c.core v ∅⟩ₖ} :=
  ⟨by simpa [seqCons] using SetTheory.singleton_seq (c.core v ∅),
    by rw [(by simp [seqCons] : {⟨∅, c.core v ∅⟩ₖ} = !⟦c.core v ∅⟧)]; ext z; simp [Seq.lh_seqCons, mem_succ_iff, one_def, zero_def],
    by simp [one_def, zero_def]⟩

lemma IsAttempt.successor {f α : V} (hf : c.IsAttempt v α f) :
    c.IsAttempt v (SetTheory.succ α) (f ⁀' c.core v f) :=
  ⟨ hf.seq.seqCons (c.core v f), hf.2.1 ▸ Seq.lh_seqCons (c.core v f) hf.seq, by
    intro β hβ w
    have := hf.1.IsFunction
    have : IsOrdinal α := hf.2.1 ▸ SetTheory.isOrdinal_lh hf.seq
    have : IsOrdinal β := IsOrdinal.of_mem hβ
    have hβ : β ⊆ α := IsOrdinal.subset_iff.mpr (mem_succ_iff.mp hβ)
    have hβdomain : β ⊆ domain f := (hf.seq.domain_eq ▸ hf.2.1) ▸ hβ
    have hrestrictβ {z : V} : (f ⁀' z) ↾ β = f ↾ β :=
        restrict_insert_kpair_eq_restrict_of_not_mem (f := f) (x := lh f) (y := z) (A := β)
          fun h₂ ↦ mem_irrefl (lh f) (hf.seq.domain_eq ▸ hβdomain (lh f) h₂)
    have hrestrictlh := IsFunction.restrict_eq_self f (lh f) (hf.seq.domain_eq ▸ subset_refl (domain f))
    rw [hrestrictβ] at *
    rcases show β = α ∨ β ∈ α
        from IsOrdinal.subset_iff.mp hβ
        with (hβ | hβ)
    · have hβeq : β = lh f := hf.2.1 ▸ hβ
      rw [hβeq, lh_mem_seqCons_iff hf.seq, hrestrictlh]
    · have hβneq : β ≠ lh f := fun h ↦ mem_irrefl β ((h ▸ hf.2.1) ▸ hβ)
      rw [kpair_mem_seqCons_iff]
      refine Iff.intro (fun h ↦ ?_) fun h ↦ ?_
      · exact Or.elim h (by aesop) fun h ↦ (hf.2.2 β hβ w).mp h
      · exact Or.inr ((hf.2.2 β hβ w).mpr h)
  ⟩

variable (c v)

open Classical in
lemma IsAttempt.exists (α : V) [IsOrdinal α] : ∃ f, c.IsAttempt v (SetTheory.succ α) f ∧ SetTheory.succ α = lh f := by
  let αo : Ordinal V := IsOrdinal.toOrdinal α
  have := IsOrdinal.succ (α := α)
  have hdefinable : ℒₛₑₜ-function₁ c.core v := by
    refine ⟨?_⟩
    -- let φ : SetTheorySemiformula V 2 := Rewriting.subst p.graph.emb
    --     fun i ↦ (if hi : i.val < 2 then #(i.castLT hi) else &(v (i.subNat 2 (by omega))) : SetTheorySemiterm V 2)
    let φ : SetTheorySemiformula V 2 := (Rew.embSubsts (#0 :> #1 :> fun i : Fin arity ↦ &(v i))) ▹ p.graph
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
      have := Seq.isOrdinal_of_mem_domain hf'.1.seq (mem_domain_of_kpair_mem hf'.2)
      -- have := hf'.1.seq.IsOrdinal_of_mem_domain (mem_domain_of_kpair_mem hf'.2)
      have : IsOrdinal α' := SetTheory.isOrdinal_lh hf'.1.seq
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

end Recursion

end LO.FirstOrder.SetTheory.Recursion
