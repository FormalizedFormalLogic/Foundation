module

public import Foundation.FirstOrder.SetTheory.Ordinal
public import Foundation.FirstOrder.SetTheory.Function
public import Foundation.FirstOrder.SetTheory.ZF

@[expose] public section

namespace LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V]

/-! ### Attempt functions -/

/--
`f` is an attempt of length `α` for the function `F`, meaning that the domain of `f` is `α`, and for all `β < α`, it holds that `f(β) = F (f ↾ β)`.
The "attempt" terminology may be due to Paul Taylor.
-/
def IsAttempt [V↓[ℒₛₑₜ] ⊧* 𝗭] (F : V → V) (α f : V) : Prop :=
  IsOrdinal α ∧ IsFunction f ∧ domain f = α ∧
    ∀ β ∈ α, ∀ y, ⟨β, y⟩ₖ ∈ f ↔ y = F (f ↾ β)

lemma IsAttempt.definable [V↓[ℒₛₑₜ] ⊧* 𝗭] {F : V → V} (hF : ℒₛₑₜ-function₁ F) :
    ℒₛₑₜ-relation (IsAttempt F) := by unfold IsAttempt; definability

/-! #### Uniqueness of attempt functions -/

namespace IsAttempt

variable [V↓[ℒₛₑₜ] ⊧* 𝗭]

/--
Any two attempt functions restrict to the same function.

Also see lemma 3.7 in chapter 2 of Frank Drake's *Set Theory: An Introduction to Large Cardinals* (Studies in Logic and the Foundations of Mathematics vol. 76, 1974).
-/
lemma isAttempt_coherent {F : V → V} {α β : Ordinal V} {f g : V} [IsFunction f] [IsFunction g]
    (hf : IsAttempt F α f) (hg : IsAttempt F β g) :
    ∀ γ : Ordinal V, γ.val ⊆ α.val ∧ γ.val ⊆ β.val → f ↾ γ.val = g ↾ γ.val := by
  rcases hf with ⟨_, _, _, testf⟩
  rcases hg with ⟨_, _, _, testg⟩
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

/--
An attempt function of length `α`, if existing, is unique.
-/
lemma isAttempt_unique {F : V → V} {α : Ordinal V} {f g : V} [IsFunction f] [IsFunction g]
    (hf : IsAttempt F α f) (hg : IsAttempt F α g) :
    f = g := by
  have hfα : f ↾ α.val = f := IsFunction.restrict_eq_self f α.val (subset_of_eq hf.2.2.1)
  have hgα : g ↾ α.val = g := IsFunction.restrict_eq_self g α.val (subset_of_eq hg.2.2.1)
  simpa [hfα, hgα] using isAttempt_coherent hf hg α ⟨subset_refl α.val, subset_refl α.val⟩

/--
If `β ≤ α`, then an attempt function on `α` restricts to the attempt function on `β`.
-/
lemma isAttempt_restrict_eq_of_le
    (F : V → V)
    {α β : Ordinal V} {f g : V} [IsFunction f] [IsFunction g]
    (hβα : β ≤ α)
    (hf : IsAttempt F α f)
    (hg : IsAttempt F β g) :
    f ↾ β.val = g := by
  have hsubset : domain g ⊆ β.val := subset_of_eq hg.2.2.1
  exact isAttempt_coherent hf hg β ⟨hβα, subset_refl β.val⟩ ▸ IsFunction.restrict_eq_self g β.val hsubset

/-! #### Existence and choices of attempt functions -/

/-- Existence of an attempt function of a given length. -/
def Exists (F : V → V) (α : V) : Prop :=
  ∃ f : V, IsAttempt F α f

/-- `Exists` implies `∃!`. -/
lemma existsUnique_of_exists (F : V → V) (α : V) (hex : Exists F α) :
    ∃! f : V, IsAttempt F α f := by
  obtain ⟨f, hf⟩ := hex
  have : IsFunction f := hf.2.1
  refine ⟨f, hf, ?_⟩
  intro g hg
  have : IsFunction g := hg.2.1
  have hα : IsOrdinal α := hf.1
  let αo : Ordinal V := IsOrdinal.toOrdinal α
  apply (IsAttempt.isAttempt_unique (α := αo) hf hg).symm

end IsAttempt

variable [V↓[ℒₛₑₜ] ⊧* 𝗭]

/--
This lemma is originally by tosiaki.
-/
lemma attemptOrEmpty_existsUnique (F : V → V) (α : V) : ∃! y,
    (IsAttempt.Exists F α ∧ IsAttempt F α y) ∨
    (¬IsAttempt.Exists F α ∧ y = ∅) := by
  by_cases hexists : IsAttempt.Exists F α
  · obtain ⟨f, hf, huniq⟩ := IsAttempt.existsUnique_of_exists F α hexists
    refine ⟨f, Or.inl ⟨hexists, hf⟩, ?_⟩
    intro y hy
    simp only [hexists, true_and, not_true_eq_false, false_and, or_false] at hy
    exact huniq y hy
  · refine existsUnique_of_exists_of_unique ⟨∅, Or.inr ⟨hexists, rfl⟩⟩ (by aesop)

/--
An attempt of length `α`, or `∅` if one doesn't exist.
This definition is by tosiaki.
-/
noncomputable def attemptOrEmpty (F : V → V) (α : V) : V :=
  Classical.choose! (attemptOrEmpty_existsUnique F α)

/--
A pair `⟨α, F f⟩ₖ` of an ordinal `α` and the value of `F` on `attemptOrEmpty F α`.
This is a technical definition needed for the proof of the transfinite recursion theorem.
-/
noncomputable def pairValueAttempt (F : V → V) (α : V) : V :=
  ⟨α, F (attemptOrEmpty F α)⟩ₖ

lemma kpair_eq_pairValueAttempt_iff {F : V → V} {α : V} {x y : V} :
    ⟨x, y⟩ₖ = pairValueAttempt F α ↔ x = α ∧ y = F (attemptOrEmpty F α) := by
  simp [pairValueAttempt]

lemma eq_of_kpair_eq_pairValueAttempt {F : V → V} {α : V} {x y : V} (h : ⟨x, y⟩ₖ = pairValueAttempt F α) : x = α :=
  (kpair_eq_pairValueAttempt_iff.mp h).1

/-! #### Constructing attempt functions using replacement -/

namespace Replacement

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/--
Function that outputs an attempt of length `α`, subject to the assumption that for all `β < α`, there is an attempt of length `β`.
This is a big function constructed using replacement.
-/
noncomputable def replAttemptOrEmpty (F : V → V) (hF : ℒₛₑₜ-function₁ F) : V → V :=
  repl (pairValueAttempt F) (hF := by
    have : ℒₛₑₜ-function₁ attemptOrEmpty F := by
      suffices ℒₛₑₜ-relation[V] (· = attemptOrEmpty F ·) by exact this
      simp only [attemptOrEmpty, Classical.choose!_eq_iff_right]
      unfold IsAttempt.Exists
      have : ℒₛₑₜ-relation (IsAttempt F) := IsAttempt.definable hF
      definability
    unfold pairValueAttempt
    definability)

@[simp] lemma mem_replAttemptOrEmpty_iff
    (F : V → V) (hF : ℒₛₑₜ-function₁ F)
    (α : V) (p : V) :
    p ∈ replAttemptOrEmpty F hF α ↔ ∃ β ∈ α, p = pairValueAttempt F β := by
  apply repl_spec

@[simp] lemma kpair_mem_replAttemptOrEmpty_iff
    (F : V → V) (hF : ℒₛₑₜ-function₁ F)
    {α : Ordinal V} {β y : V} :
    ⟨β, y⟩ₖ ∈ replAttemptOrEmpty F hF α ↔ β ∈ α.val ∧ ⟨β, y⟩ₖ = pairValueAttempt F β := by
  simp only [mem_replAttemptOrEmpty_iff]
  constructor <;> intro h
  · obtain ⟨β, hβα, h⟩ := h
    rw [eq_of_kpair_eq_pairValueAttempt h] at *
    exact ⟨hβα, h⟩
  · use β

lemma domain_replAttemptOrEmpty_eq (F : V → V) (hF : ℒₛₑₜ-function₁ F) (α : Ordinal V) :
    domain (replAttemptOrEmpty F hF α) = α.val := by
  ext z
  simp only [mem_domain_iff, mem_replAttemptOrEmpty_iff]
  constructor <;> intro h
  · obtain ⟨y, β, hβα, hβ⟩ := h
    exact eq_of_kpair_eq_pairValueAttempt hβ ▸ hβα
  · use F (attemptOrEmpty F z)
    use z
    simp_all only [true_and, pairValueAttempt, true_and]

instance (F : V → V) (hF : ℒₛₑₜ-function₁ F) (α : Ordinal V) : IsFunction (replAttemptOrEmpty F hF α) := by
  let f := replAttemptOrEmpty F hF α
  have hdomain : domain f = α.val := domain_replAttemptOrEmpty_eq F hF α
  apply isFunction_iff.mpr
  apply mem_function_iff.mpr
  constructor
  · intro p hpf
    obtain ⟨β, _, f, rfl, _⟩ := (mem_replAttemptOrEmpty_iff F hF _ _).mp hpf
    apply kpair_mem_iff.mpr
    exact And.intro (mem_domain_of_kpair_mem hpf) (mem_range_of_kpair_mem hpf)
  · intro x hx
    simp only [kpair_mem_replAttemptOrEmpty_iff]
    apply existsUnique_of_exists_of_unique
    · rw [hdomain] at hx
      exact ⟨F (attemptOrEmpty F x), And.intro hx (pairValueAttempt.eq_1 F x)⟩
    · intro y₁ y₂
      simp_all only [pairValueAttempt, kpair_iff, true_and, implies_true]

/--
An auxiliary lemma about `replAttemptOrEmpty`.
-/
lemma replAttemptOrEmpty_aux
    (F : V → V) (hF : ℒₛₑₜ-function₁ F) :
    (α : Ordinal V) → IsAttempt F α (replAttemptOrEmpty F hF α) := by
  let motive (α : V) : Prop := IsAttempt F α (replAttemptOrEmpty F hF α)

  have := IsAttempt.definable hF
  have : ℒₛₑₜ-function₁ replAttemptOrEmpty F hF := by
    unfold replAttemptOrEmpty
    definability
  have motive_definable : ℒₛₑₜ-predicate motive := by
    unfold motive
    definability
  refine transfinite_induction motive motive_definable ?_
  intro α ih
  have hα := Ordinal.ordinal α

  have hrestrict : ((β : V) → (hβα : β ∈ α.val) → IsAttempt F β ((replAttemptOrEmpty F hF α) ↾ β)) := by
    intro β hβα
    have hβ : IsOrdinal β := IsOrdinal.of_mem hβα
    let βo : Ordinal V := IsOrdinal.toOrdinal β
    have haux := ih βo hβα

    suffices h : (replAttemptOrEmpty F hF α) ↾ β = replAttemptOrEmpty F hF β from h ▸ haux
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
      · exact ⟨γ, hγβ, F (attemptOrEmpty F γ), hγ⟩
  refine ⟨hα, inferInstance, domain_replAttemptOrEmpty_eq F hF α, ?_⟩
  intro β hβα y
  have hβ : IsOrdinal β := IsOrdinal.of_mem hβα
  let βo : Ordinal V := IsOrdinal.toOrdinal β

  suffices h : ⟨β, y⟩ₖ ∈ replAttemptOrEmpty F hF α.val ↔ ∃ f, y = F f ∧ IsAttempt F β f from by
    constructor <;> intro h₂
    · obtain ⟨f, rfl, hf⟩ := h.mp h₂
      have : IsFunction f := hf.2.1
      have : IsFunction ((replAttemptOrEmpty F hF (↑α)) ↾ ↑βo) := inferInstance
      simp only [IsAttempt.isAttempt_unique hf (hrestrict βo hβα), IsOrdinal.toOrdinal_val, βo]
    · apply h.mpr
      use (replAttemptOrEmpty F hF (↑α)) ↾ β
      simp only [h₂, true_and]
      exact hrestrict βo hβα
  have hexists : IsAttempt.Exists F β := ⟨replAttemptOrEmpty F hF β, ih βo hβα⟩
  simp_all only [mem_replAttemptOrEmpty_iff, pairValueAttempt, kpair_iff, ↓existsAndEq, true_and,
    motive]
  have hattempt : IsAttempt F β (attemptOrEmpty F β) := by
    simp_all [attemptOrEmpty, Classical.choose!_spec]
  constructor <;> intro h
  · use attemptOrEmpty F β
  · obtain ⟨f, hfleft, hfright⟩ := h
    have heq := IsOrdinal.toOrdinal_val β
    rw [← heq] at *
    have := hfright.2.1
    have := hattempt.2.1
    exact (IsAttempt.isAttempt_unique hfright hattempt) ▸ hfleft

/--
For any ordinal `α`, there exists an attempt function of length `α`.
-/
lemma attempt_function_exists
    (F : V → V) (hF : ℒₛₑₜ-function₁ F) :
    (α : Ordinal V) → IsAttempt.Exists F α :=
  fun α ↦ ⟨replAttemptOrEmpty F hF α, replAttemptOrEmpty_aux F hF α⟩

end LO.FirstOrder.SetTheory.Replacement
