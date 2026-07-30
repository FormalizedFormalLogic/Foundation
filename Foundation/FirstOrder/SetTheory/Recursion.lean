module

public import Foundation.FirstOrder.SetTheory.Ordinal
public import Foundation.FirstOrder.SetTheory.Function
public import Foundation.FirstOrder.SetTheory.ZF

@[expose] public section

namespace LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭]

/-! ### Attempt functions -/

/--
`f` is an attempt of length `α` for the function `F`, meaning that the domain of `f` is `α`, and for all `β < α`, it holds that `f(β) = F (f ↾ β)`.
The "attempt" terminology may be due to Paul Taylor.
-/
def IsAttempt (F : V → V) (α f : V) : Prop :=
  IsOrdinal α ∧ IsFunction f ∧ domain f = α ∧
    ∀ β ∈ α, ∀ y, ⟨β, y⟩ₖ ∈ f ↔ y = F (f ↾ β)

/--
A `SetTheorySemiformula` defining `IsAttempt F` for a definable function `F`. Pass a formula `φ` defining `F`.
-/
def IsAttempt.dfn (φ : SetTheorySemiformula V 2) : SetTheorySemiformula V 2 :=
  f“α f. !IsOrdinal.dfn' α ∧ !IsFunction.dfn' f ∧ !domain.dfn' f = α ∧
    ∀ β ∈ α, ∀ y, !kpair.dfn' β y ∈ f ↔ y = !φ (!restrict.dfn' f β)”
  /- Cast `kpair.dfn` and `restrict.dfn` to a type that allows parameters, to work with `Semiformula.nestFormulaeFunc`. -/
  where
    IsOrdinal.dfn' : SetTheorySemiformula V 1 := (Rew.rewriteMap (Empty.elim : Empty → V)) ▹ IsOrdinal.dfn
    IsFunction.dfn' : SetTheorySemiformula V 1 := (Rew.rewriteMap (Empty.elim : Empty → V)) ▹ IsFunction.dfn
    domain.dfn' : SetTheorySemiformula V 2 := (Rew.rewriteMap (Empty.elim : Empty → V)) ▹ domain.dfn
    kpair.dfn' : SetTheorySemiformula V 3 := (Rew.rewriteMap (Empty.elim : Empty → V)) ▹ kpair.dfn
    restrict.dfn' : SetTheorySemiformula V 3 := (Rew.rewriteMap (Empty.elim : Empty → V)) ▹ restrict.dfn

lemma IsAttempt.defined (F : V → V) {φ : SetTheorySemiformula V 2} (hF : IsDefinedByWithParam (fun v ↦ v 0 = F (v 1)) φ) :
    IsDefinedByWithParam (fun v ↦ IsAttempt F (v 0) (v 1)) (IsAttempt.dfn φ) := by
  intro v
  simp_all [IsAttempt, IsAttempt.dfn,
    dfn.IsOrdinal.dfn', dfn.IsFunction.dfn', dfn.domain.dfn', dfn.kpair.dfn', dfn.restrict.dfn',
    Semiformula.eval_rewriteMap]

lemma IsAttempt.definable (F : V → V) {φ : SetTheorySemiformula V 2} (hF : IsDefinedByWithParam (fun v ↦ v 0 = F (v 1)) φ) :
    ℒₛₑₜ-relation[V] (fun α f ↦ IsAttempt F α f) := by
  use IsAttempt.dfn φ
  intro v
  simp only [IsAttempt.defined F hF, Fin.isValue]

/-! #### Uniqueness of attempt functions -/

namespace IsAttempt

/--
Any two attempt functions restrict to the same function.

Also see lemma 3.7 in chapter 2 of Frank Drake's *Set Theory: An Introduction to Large Cardinals* (Studies in Logic and the Foundations of Mathematics vol. 76, 1974).
-/
lemma isAttempt_coherent (F : V → V) {α β : Ordinal V} {f g : V} [IsFunction f] [IsFunction g]
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
  simpa [hfα, hgα] using isAttempt_coherent F hf hg α ⟨subset_refl α.val, subset_refl α.val⟩

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
  exact isAttempt_coherent F hf hg β ⟨hβα, subset_refl β.val⟩ ▸ IsFunction.restrict_eq_self g β.val hsubset

/-! #### Existence and choices of attempt functions -/

/-- Existence of an attempt function of a given length. -/
def ExistsAttempt (F : V → V) (α : V) : Prop :=
  ∃ f : V, IsAttempt F α f

def ExistsAttempt.dfn (φ : SetTheorySemiformula V 2) : SetTheorySemiformula V 1 :=
  f“α. ∃ f, !(IsAttempt.dfn φ) α f”

lemma ExistsAttempt.defined (F : V → V) {φ : SetTheorySemiformula V 2} (hF : IsDefinedByWithParam (fun v ↦ v 0 = F (v 1)) φ) :
    IsDefinedByWithParam (fun v ↦ ExistsAttempt F (v 0)) (ExistsAttempt.dfn φ) := by
  intro v
  simp [ExistsAttempt.dfn, IsAttempt.defined F hF]
  rfl

lemma ExistsAttempt.definable (F : V → V) {φ : SetTheorySemiformula V 2} (hF : IsDefinedByWithParam (fun v ↦ v 0 = F (v 1)) φ) :
    ℒₛₑₜ-predicate (fun α ↦ ExistsAttempt F α) := by
  use ExistsAttempt.dfn φ
  intro v
  simp [ExistsAttempt.dfn, IsAttempt.defined F hF]
  rfl

/-- `ExistsAttempt` implies `∃!`. -/
lemma existsUnique_of_ExistsAttempt (F : V → V) (α : V) (hex : ExistsAttempt F α) :
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

/--
This lemma is originally by tosiaki.
-/
lemma attemptOrEmpty_existsUnique (F : V → V) (α : V) : ∃! y,
    (IsAttempt.ExistsAttempt F α ∧ IsAttempt F α y) ∨
    (¬ IsAttempt.ExistsAttempt F α ∧ y = ∅) := by
  by_cases hexists : IsAttempt.ExistsAttempt F α
  · refine existsUnique_of_exists_of_unique ⟨hexists.choose, Or.inl ⟨hexists, hexists.choose_spec⟩⟩ ?_
    intro y₁ y₂ hy₁ hy₂
    simp_all only [true_and, not_true_eq_false, false_and, or_false]
    rcases hy₁.1, hy₁.2.1, hy₂.2.1 with ⟨hα, _, _⟩
    let αo : Ordinal V := IsOrdinal.toOrdinal α
    rw [← IsOrdinal.toOrdinal_val α] at hy₁
    exact IsAttempt.isAttempt_unique hy₁ hy₂
  · refine existsUnique_of_exists_of_unique ⟨∅, Or.inr ⟨hexists, rfl⟩⟩ (by aesop)

/--
An attempt of length `α`, or `∅` if one doesn't exist.
This definition is by tosiaki.
-/
noncomputable def attemptOrEmpty (F : V → V) (α : V) : V :=
  Classical.choose! (attemptOrEmpty_existsUnique F α)

/--
A `SetTheorySemiformula` defining `attemptOrEmpty F` for a definable function `F`. Pass a formula `φ` defining `F`.
-/
def attemptOrEmpty.dfn (φ : SetTheorySemiformula V 2) : SetTheorySemiformula V 2 :=
  f“y α. !(IsAttempt.ExistsAttempt.dfn φ) α ∧ !(IsAttempt.dfn φ) α y
    ∨ ¬ !(IsAttempt.ExistsAttempt.dfn φ) α ∧ !isEmpty' y”
    /- Cast `kpair.dfn` and `restrict.dfn` to a type that allows parameters, to work with `Semiformula.nestFormulaeFunc`. -/
    where
      isEmpty' : SetTheorySemiformula V 1 := (Rew.rewriteMap (Empty.elim : Empty → V)) ▹ isEmpty

lemma attemptOrEmpty.defined {φ : SetTheorySemiformula V 2} (F : V → V) (hF : IsDefinedByWithParam (fun v ↦ v 0 = F (v 1)) φ) :
    IsDefinedByWithParam (fun v ↦ v 0 = attemptOrEmpty F (v 1)) (attemptOrEmpty.dfn φ) := by
  intro v
  simp_all [attemptOrEmpty, attemptOrEmpty.dfn, IsAttempt.ExistsAttempt.defined F hF, IsAttempt.defined F hF,
   dfn.isEmpty', Semiformula.eval_rewriteMap]

lemma attemptOrEmpty.definable {φ : SetTheorySemiformula V 2} (F : V → V) (hF : IsDefinedByWithParam (fun v ↦ v 0 = F (v 1)) φ) :
    ℒₛₑₜ-function₁[V] (attemptOrEmpty F) := by
  use attemptOrEmpty.dfn φ
  intro v
  simp [attemptOrEmpty.defined F hF]

/--
A pair `⟨α, F f⟩ₖ` of an ordinal `α` and the value of `F` on `attemptOrEmpty F α`.
This is a technical definition needed for the proof of the transfinite recursion theorem.
-/
noncomputable def pairValueAttempt (F : V → V) (α : V) : V :=
  ⟨α, F (attemptOrEmpty F α)⟩ₖ

/--
A `SetTheorySemiformula` defining `pairValueAttempt F` for a definable function `F`. Pass a formula `φ` defining `F`.
-/
def pairValueAttempt.dfn (φ : SetTheorySemiformula V 2) : SetTheorySemiformula V 2 :=
  f“y α. y = !kpair.dfn' α (!φ (!(attemptOrEmpty.dfn φ) α))”
  /- Cast `kpair.dfn` and `restrict.dfn` to a type that allows parameters, to work with `Semiformula.nestFormulaeFunc`. -/
  where
    kpair.dfn' : SetTheorySemiformula V 3 := (Rew.rewriteMap (Empty.elim : Empty → V)) ▹ kpair.dfn

lemma pairValueAttempt.defined {φ : SetTheorySemiformula V 2} (F : V → V) (hF : IsDefinedByWithParam (fun v ↦ v 0 = F (v 1)) φ) :
    IsDefinedByWithParam (fun v ↦ v 0 = pairValueAttempt F (v 1)) (pairValueAttempt.dfn φ) := by
  intro v
  simp_all [pairValueAttempt.dfn, pairValueAttempt, dfn.kpair.dfn', Semiformula.eval_rewriteMap,
    attemptOrEmpty.defined F hF]

lemma pairValueAttempt.definable {φ : SetTheorySemiformula V 2} (F : V → V) (hF : IsDefinedByWithParam (fun v ↦ v 0 = F (v 1)) φ) :
    ℒₛₑₜ-function₁ (pairValueAttempt F) := by
  use pairValueAttempt.dfn φ
  intro v
  simp [pairValueAttempt.defined F hF]

lemma eq_of_kpair_eq_pairValueAttempt {F : V → V} {α : V} {x y : V} (h : ⟨x, y⟩ₖ = pairValueAttempt F α) : x = α :=
  (kpair_iff.mp (pairValueAttempt.eq_1 F α ▸ h)).1

/-! #### Constructing attempt functions using replacement -/

namespace Replacement

variable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/--
Function that outputs an attempt of length `α`, subject to the assumption that for all `β < α`, there is an attempt of length `β`.
This is a big function constructed using replacement.
-/
noncomputable def replAttemptOrEmpty
    {φ : SetTheorySemiformula V 2} (F : V → V) (hF : IsDefinedByWithParam (fun v ↦ v 0 = F (v 1)) φ)
    (α : V) : V :=
  repl α (pairValueAttempt F) (hF := pairValueAttempt.definable F hF)

@[simp] lemma mem_replAttemptOrEmpty_iff
    {φ : SetTheorySemiformula V 2} (F : V → V) (hF : IsDefinedByWithParam (fun v ↦ v 0 = F (v 1)) φ)
    (α : V) (p : V) :
    p ∈ replAttemptOrEmpty F hF α ↔ ∃ β ∈ α, p = pairValueAttempt F β := by
  apply repl_spec

@[simp] lemma kpair_mem_replAttemptOrEmpty_iff
    {φ : SetTheorySemiformula V 2} (F : V → V) (hF : IsDefinedByWithParam (fun v ↦ v 0 = F (v 1)) φ)
    {α : Ordinal V} {β y : V} :
    ⟨β, y⟩ₖ ∈ replAttemptOrEmpty F hF α ↔ β ∈ α.val ∧ ⟨β, y⟩ₖ = pairValueAttempt F β := by
  simp only [mem_replAttemptOrEmpty_iff]
  constructor <;> intro h
  · obtain ⟨β, hβα, h⟩ := h
    rw [eq_of_kpair_eq_pairValueAttempt h] at *
    exact ⟨hβα, h⟩
  · use β

/--
A `SetTheorySemiformula` defining `replAttemptOrEmpty F` for a definable function `F`. Pass a formula `φ` defining `F`.
-/
def replAttemptOrEmpty.dfn (φ : SetTheorySemiformula V 2) :
    SetTheorySemiformula V 2 :=
  f“Y α. ∀ y, y ∈ Y ↔ ∃ β ∈ α, y = !(pairValueAttempt.dfn φ) β”

lemma replAttemptOrEmpty.defined
    {φ : SetTheorySemiformula V 2} (F : V → V) (hF : IsDefinedByWithParam (fun v ↦ v 0 = F (v 1)) φ) :
    IsDefinedByWithParam (fun (v : Fin 2 → V) ↦ v 0 = replAttemptOrEmpty F hF (v 1)) (replAttemptOrEmpty.dfn φ) := by
  intro v
  simp_all [replAttemptOrEmpty, replAttemptOrEmpty.dfn, pairValueAttempt.defined F hF,
    mem_ext_iff (x := v 0)]

instance replAttemptOrEmpty.definable
    {φ : SetTheorySemiformula V 2} (F : V → V) (hF : IsDefinedByWithParam (fun v ↦ v 0 = F (v 1)) φ) :
    ℒₛₑₜ-function₁[V] (replAttemptOrEmpty F (hF := hF)) := by
  use replAttemptOrEmpty.dfn φ
  intro v
  simp [replAttemptOrEmpty.defined F hF]

lemma domain_replAttemptOrEmpty_eq
    {φ : SetTheorySemiformula V 2} (F : V → V) (hF : IsDefinedByWithParam (fun v ↦ v 0 = F (v 1)) φ)
    (α : Ordinal V) :
    domain (replAttemptOrEmpty F hF α) = α.val := by
  ext z
  simp only [mem_domain_iff, mem_replAttemptOrEmpty_iff]
  constructor <;> intro h
  · obtain ⟨y, β, hβα, hβ⟩ := h
    exact eq_of_kpair_eq_pairValueAttempt hβ ▸ hβα
  · use F (attemptOrEmpty F z)
    use z
    simp_all only [true_and, pairValueAttempt, true_and]

instance {φ : SetTheorySemiformula V 2} (F : V → V) (hF : IsDefinedByWithParam (fun v ↦ v 0 = F (v 1)) φ)
    (α : Ordinal V) :
    IsFunction (replAttemptOrEmpty F hF α) := by
  -- Name it for brevity
  let f := replAttemptOrEmpty F hF α
  have hdomain : domain f = α.val := domain_replAttemptOrEmpty_eq F hF α
  apply isFunction_iff.mpr
  apply mem_function_iff.mpr
  constructor
  · -- Show that `f` contains only ordered pairs
    intro p hpf
    obtain ⟨β, hβα, f, rfl, hf⟩ := (repl_spec {definable := ⟨pairValueAttempt.dfn φ, pairValueAttempt.defined F hF⟩}).mp hpf
    apply kpair_mem_iff.mpr
    exact And.intro (mem_domain_of_kpair_mem hpf) (mem_range_of_kpair_mem hpf)
  · -- Show well-definedness of `f`, i.e. uniqueness of output
    intro x hx
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
    {φ : SetTheorySemiformula V 2} (F : V → V) (hF : IsDefinedByWithParam (fun v ↦ v 0 = F (v 1)) φ) :
    (α : Ordinal V) →
    IsAttempt F α (replAttemptOrEmpty F hF α) := by
  let motive (α : V) : Prop := IsAttempt F α (replAttemptOrEmpty F hF α)

  let motive_dfn : SetTheorySemiformula V 1 :=
    f“α. !(IsAttempt.dfn φ) α (!(replAttemptOrEmpty.dfn φ) α)”

  have motive_definable : ℒₛₑₜ-predicate motive := by
    use motive_dfn
    intro v
    simp_all [motive, motive_dfn, replAttemptOrEmpty.defined F hF, IsAttempt.defined F hF]

  refine transfinite_induction motive motive_definable ?_
  -- Now I just need to prove the transfinite induction.
  intro α ih
  have hα := Ordinal.ordinal α

  -- The case of (restrict) for `α`. This follows from ih for (aux), i.e. `∀ β < α, ((aux) for β)`.
  have hrestrict : ((β : V) → (hβα : β ∈ α.val) → IsAttempt F β ((replAttemptOrEmpty F hF α) ↾ β)) := by
    intro β hβα
    have hβ : IsOrdinal β := IsOrdinal.of_mem hβα
    let βo : Ordinal V := IsOrdinal.toOrdinal β
    -- Get a case of (aux) that's been proven up to this point in the transfinite induction
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
  -- Proving (aux) for `α`
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
  have hexists : IsAttempt.ExistsAttempt F β := ⟨replAttemptOrEmpty F hF β, ih βo hβα⟩
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
    {φ : SetTheorySemiformula V 2} (F : V → V) (hF : IsDefinedByWithParam (fun v ↦ v 0 = F (v 1)) φ) :
    (α : Ordinal V) → IsAttempt.ExistsAttempt F α := by
  let motive (α : V) : Prop := IsAttempt.ExistsAttempt F α

  refine transfinite_induction motive (IsAttempt.ExistsAttempt.definable F hF) ?_
  intro α ih
  have hexists : ∀ β ∈ α.val, motive β := by
    intro β hβα
    have : IsOrdinal β := IsOrdinal.of_mem hβα
    exact ih (IsOrdinal.toOrdinal β) hβα
  use replAttemptOrEmpty F hF α
  exact replAttemptOrEmpty_aux F hF α

end LO.FirstOrder.SetTheory.Replacement
