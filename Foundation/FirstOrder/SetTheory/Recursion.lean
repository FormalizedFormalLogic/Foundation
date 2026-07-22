module

public import Foundation.FirstOrder.SetTheory.Ordinal
public import Foundation.FirstOrder.SetTheory.Function
public import Foundation.FirstOrder.SetTheory.ZF

@[expose] public section

namespace LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭]

namespace IsOrdinal

variable {α β γ : V}

/-! ### Attempt functions -/

/--
`f` is an attempt of length `α` for the function `F`, meaning that the domain of `f` is `α`, and for all `β < α`, it holds that `f(β) = y` iff `y = F (f ↾ β)`.
The "attempt" terminology may be due to Paul Taylor.
-/
def IsAttempt (F : V → V) (α f : V) : Prop :=
  IsOrdinal α ∧ IsFunction f ∧ domain f = α ∧
    ∀ β ∈ α, ∀ y, ⟨β, y⟩ₖ ∈ f ↔ y = F (f ↾ β)

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

lemma IsAttempt.defined (F : V → V) (hF : IsDefinedByWithParam (fun v ↦ v 0 = F (v 1)) φ) :
    IsDefinedByWithParam (fun v ↦ IsAttempt F (v 0) (v 1)) (IsAttempt.dfn φ) := by
  intro v
  simp_all [IsAttempt, IsAttempt.dfn,
    dfn.IsOrdinal.dfn', dfn.IsFunction.dfn', dfn.domain.dfn', dfn.kpair.dfn', dfn.restrict.dfn',
    Semiformula.eval_rewriteMap]

/-
TODO: Find a way to make `hFdef` not a typeclass without getting an error.
-/
lemma IsAttempt.definable (F : V → V) (hF : IsDefinedByWithParam (fun v ↦ v 0 = F (v 1)) φ) :
    ℒₛₑₜ-relation[V] (fun β f ↦ IsAttempt F β f) := by
  intro v
  simp only [IsAttempt.defined, Fin.isValue]

/-! #### Uniqueness of attempt functions -/

lemma attempt_function_coherent (F : V → V) (α : Ordinal V) {f g : V} [IsFunction f] [IsFunction g]
    (hf : IsAttempt F α f) (hg : IsAttempt F α g) :
    ∀ β : Ordinal V, β.val ⊆ α.val → f ↾ β.val = g ↾ β.val := by
  rcases hf with ⟨_, _, _, testf⟩
  rcases hg with ⟨_, _, _, testg⟩
  refine transfinite_induction (P := fun x ↦ x ⊆ α.val → f ↾ x = g ↾ x) (by definability) ?_
  intro β ihβ hβα
  ext p
  simp only [mem_restrict_iff, and_congr_left_iff, forall_exists_index, and_imp]
  intro x hxβ y rfl
  have : IsOrdinal x := IsOrdinal.of_mem hxβ
  let xo : Ordinal V := IsOrdinal.toOrdinal x
  have hxα : x ∈ α.val := hβα x hxβ
  have hxoα : xo.val ⊆ α.val := subset_trans (β.ordinal.toIsTransitive.transitive x hxβ) hβα
  have hfxogxo : f ↾ xo = g ↾ xo := ihβ xo hxβ hxoα
  simp_all only [toOrdinal_val, xo]

/--
An attempt function of length `α`, if existing, is unique.
-/
lemma attempt_function_unique {F : V → V} {α : Ordinal V} {f g : V} [IsFunction f] [IsFunction g]
    (hf : IsAttempt F α f) (hg : IsAttempt F α g) :
    f = g := by
  have hrestr :
      ∀ β : Ordinal V, β.val ⊆ α → f ↾ β.val = g ↾ β.val := by
    apply attempt_function_coherent <;> assumption
  have hαfg : f ↾ α.val = g ↾ α.val := hrestr α (subset_refl α.val)
  have hfα : f ↾ α.val = f := IsFunction.restrict_eq_self f α.val (subset_of_eq hf.2.2.1)
  have hgα : g ↾ α.val = g := IsFunction.restrict_eq_self g α.val (subset_of_eq hg.2.2.1)
  simp_all

/--
If `β < α`, an attempt function on `α` restricts to the attempt function on `β`.
-/
lemma attempt_function_restrict_eq_of_lt
    (F : V → V)
    {α β : Ordinal V} {f g : V} [IsFunction f] [IsFunction g]
    (hβα : β < α)
    (hf : IsAttempt F α f)
    (hg : IsAttempt F β g) :
    f ↾ β.val = g := by
  rcases hf with ⟨_, _, hdf, hrecf⟩
  have hdg := hg.2.2.1
  have : IsFunction (f ↾ β.val) := IsFunction.restrict f β.val
  have hsubseteq : β.val ⊆ α.val := by
    apply le_of_lt at hβα
    apply Ordinal.le_def.mp at hβα
    assumption
  have hαβ : α.val ∩ β.val = β.val := inter_eq_right_of_subset hsubseteq
  suffices IsAttempt F β (f ↾ β.val) by
    rw [← restrict_restrict_of_subset (A := β.val) subset_rfl]
    rw [← IsFunction.restrict_eq_self (A := β.val) (f := g) (subset_of_eq hdg)]
    apply (attempt_function_coherent F β this hg β subset_rfl)
  unfold IsAttempt
  simp only [Ordinal.instIsOrdinalVal, this, domain_restrict_eq, hdf, hαβ, true_and]
  intro γ hγβ y
  have hγα : γ ∈ α.val := by aesop
  have : IsOrdinal γ := of_mem hγβ
  have hγsusbetβ : γ ⊆ β.val := by grind
  simp_all [mem_restrict_iff]

/-- Any two attempt functions agree on overlapping inputs. -/
lemma attempt_function_coherent_on
    (F : V → V)
    {α β : Ordinal V} {f g x y₁ y₂ : V}
    [IsFunction f] [IsFunction g]
    (hf : IsAttempt F α f)
    (hg : IsAttempt F β g)
    (hxy₁ : ⟨x, y₁⟩ₖ ∈ f) (hxy₂ : ⟨x, y₂⟩ₖ ∈ g) :
    y₁ = y₂ := by
  have := hf.2.1
  have := hg.2.1
  rcases IsOrdinal.mem_trichotomy α.val β.val with (hαβ | heq | hβα) <;> simp_all only [← Ordinal.lt_def]
  · have hrestrict := attempt_function_restrict_eq_of_lt F hαβ hg hf
    rw [← hrestrict] at hxy₁
    have hxy₁ := (kpair_mem_restrict_iff.mp hxy₁).1
    exact IsFunction.unique hxy₁ hxy₂
  · simp_all only [attempt_function_unique hf hg]
    exact IsFunction.unique hxy₁ hxy₂
  · have hrestrict := attempt_function_restrict_eq_of_lt F hβα hf hg
    rw [← hrestrict] at hxy₂
    have hxy₂ := (kpair_mem_restrict_iff.mp hxy₂).1
    exact IsFunction.unique hxy₁ hxy₂

/-! #### Existence and choices of attempt functions -/

/-- Existence of an attempt function of a given length. -/
def ExistsAttempt (F : V → V) (α : V) : Prop :=
  ∃ f : V, IsAttempt F α f

noncomputable def ExistsAttempt.dfn (φ : SetTheorySemiformula V 2) : SetTheorySemiformula V 1 :=
  f“α. ∃ f, !(IsAttempt.dfn φ) α f”

lemma ExistsAttempt.defined (F : V → V) (hF : ℒₛₑₜ-function₁ F) :
    IsDefinedByWithParam (fun v ↦ ExistsAttempt F (v 0)) (ExistsAttempt.dfn (Classical.choose hF.definable)) := by
  intro v
  simp [ExistsAttempt.dfn, IsAttempt.defined]
  rfl

/-- `ExistsAttempt` implies `∃!`. -/
lemma existsUnique_of_ExistsAttempt (F : V → V) (α : V) (hex : ExistsAttempt F α) :
    ∃! f : V, IsAttempt F α f := by
  rcases hex with ⟨f, hf⟩
  have : IsFunction f := hf.2.1
  refine ⟨f, hf, ?_⟩
  intro g hg
  have : IsFunction g := hg.2.1
  /- TODO: Sort out conflicts with α being either of type V or of type Ordinal V in this file.
  This currently works but is inelegant. -/
  have hα : IsOrdinal α := hf.1
  let αo : Ordinal V := IsOrdinal.toOrdinal α
  apply (attempt_function_unique (α := αo) hf hg).symm

instance ExistsAttempt.definable
    (F : V → V) [hFdef : ℒₛₑₜ-function₁[V] F] :
    ℒₛₑₜ-predicate[V] (ExistsAttempt F) :=
  Language.Definable.exs
    (Language.Definable.retraction
      (IsAttempt.definable F)
      ![1, 0])

/--
This lemma is originally by tosiaki
-/
lemma attemptOrEmpty_exists (F : V → V) (α : V) : ∃! y,
    (ExistsAttempt F α ∧ IsAttempt F α y) ∨
    (¬ ExistsAttempt F α ∧ y = ∅) := by
  by_cases hexists : ExistsAttempt F α
  · refine existsUnique_of_exists_of_unique ?_ ?_
    · exact ⟨Classical.choose hexists, Or.inl ⟨hexists, Classical.choose_spec hexists⟩⟩
    · intro y₁ y₂
      simp only [hexists, true_and, not_true_eq_false, false_and, or_false]
      intro hy₁ hy₂
      rcases hy₁.1, hy₁.2.1, hy₂.2.1 with ⟨hα, _, _⟩
      let αo : Ordinal V := IsOrdinal.toOrdinal α
      rw [← toOrdinal_val α] at hy₁
      exact attempt_function_unique hy₁ hy₂
  · refine existsUnique_of_exists_of_unique ?_ ?_
    · exact ⟨∅, Or.inr ⟨hexists, rfl⟩⟩
    · intro y₁ y₂
      simp only [hexists, false_and, not_false_eq_true, true_and, false_or]
      exact fun (hy₁ : y₁ = ∅) (hy₂ : y₂ = ∅) ↦ hy₂ ▸ hy₁

/--
An attempt of length `α`, or `∅` if one doesn't exist.
This definition is by tosiaki
-/
noncomputable def attemptOrEmpty (F : V → V) (α : V) : V :=
  Classical.choose! (attemptOrEmpty_exists F α)

noncomputable def attemptOrEmpty.dfn (F : V → V)
    (hF : ℒₛₑₜ-function₁[V] F) : SetTheorySemiformula V 2 :=
  f“y α. !(ExistsAttempt.dfn F hF) α ∧ !(IsAttempt.dfn F) α y
    -- ∨ ¬ !(ExistsAttempt.dfn F hF) α ∧ ∀ z, z ∉ y”
    ∨ ¬ !(ExistsAttempt.dfn F hF) α ∧ !isEmpty' y”
    /- Cast `kpair.dfn` and `restrict.dfn` to a type that allows parameters, to work with `Semiformula.nestFormulaeFunc`. -/
    where
      isEmpty' : SetTheorySemiformula V 1 := (Rew.rewriteMap (Empty.elim : Empty → V)) ▹ isEmpty

lemma attemptOrEmpty.defined (F : V → V)
    (hF : ℒₛₑₜ-function₁[V] F) :
    IsDefinedByWithParam (fun v ↦ v 0 = attemptOrEmpty F (v 1)) (attemptOrEmpty.dfn F hF) := by
  have hdefined := Classical.choose_spec hF.definable
  intro v
  simp_all [attemptOrEmpty, attemptOrEmpty.dfn, ExistsAttempt.defined, IsAttempt.defined,
    dfn.isEmpty', Semiformula.eval_rewriteMap]

instance attemptOrEmpty.definable (F : V → V)
    [hF : ℒₛₑₜ-function₁[V] F] :
    ℒₛₑₜ-function₁[V] (attemptOrEmpty F) := by
  use attemptOrEmpty.dfn F hF
  apply attemptOrEmpty.defined

/--
A pair `⟨α, F f⟩ₖ` of an ordinal `α` and the value of `F` on `attemptOrEmpty F α`.
This is a technical definition needed for the proof of the transfinite recursion theorem.
-/
noncomputable def pairValueAttempt (F : V → V) (α : V) : V :=
  ⟨α, F (attemptOrEmpty F α)⟩ₖ

noncomputable def pairValueAttempt.dfn (F : V → V) (hF : ℒₛₑₜ-function₁ F) : SetTheorySemiformula V 2 :=
  f“y α. y = !kpair.dfn' α (!(Classical.choose hF.definable) (!(attemptOrEmpty.dfn F hF) α))”
  /- Cast `kpair.dfn` and `restrict.dfn` to a type that allows parameters, to work with `Semiformula.nestFormulaeFunc`. -/
  where
    kpair.dfn' : SetTheorySemiformula V 3 := (Rew.rewriteMap (Empty.elim : Empty → V)) ▹ kpair.dfn

lemma pairValueAttempt.defined (F : V → V) (hF : ℒₛₑₜ-function₁ F) :
    IsDefinedByWithParam (fun v ↦ v 0 = pairValueAttempt F (v 1)) (pairValueAttempt.dfn F hF) := by
  intro v
  simp_all [pairValueAttempt.dfn, pairValueAttempt, dfn.kpair.dfn', Semiformula.eval_rewriteMap]
  sorry

instance pairValueAttempt.definable (F : V → V) [hF : ℒₛₑₜ-function₁ F] :
    ℒₛₑₜ-function₁ (pairValueAttempt F) := by
  use pairValueAttempt.dfn F hF
  apply pairValueAttempt.defined

lemma eq_of_kpair_eq_pairValueAttempt {F : V → V} {α : V} {x y : V} (h : ⟨x, y⟩ₖ = pairValueAttempt F α) :
    x = α := by
  simp only [pairValueAttempt, kpair_iff] at h
  exact h.1

-- lemma isPairValueAttempt_unique_of_ExistsAttempt
--     (F : V → V) (α : V) :
--     ExistsAttempt F α → ∃! p, IsPairValueAttempt F α p := by
--   intro h
--   let ⟨f, hf⟩ := h
--   have : IsOrdinal α := hf.1
--   have : IsFunction f := hf.2.1
--   let αo : Ordinal V := IsOrdinal.toOrdinal α
--   apply existsUnique_of_ExistsAttempt at h
--   refine ExistsUnique.intro ⟨α, F f⟩ₖ ?_ ?_
--   · simp only [IsPairValueAttempt, kpair_iff, true_and]
--     use f
--   · simp only [IsPairValueAttempt, forall_exists_index, and_imp]
--     intro p₂ f₂ hp₂ hf₂
--     have : IsFunction f₂ := hf₂.2.1
--     simp_all only [attempt_function_unique (α := αo) hf hf₂]

-- /--
-- A characterization of when the right argument of `IsPairValueAttempt` is unique.
-- -/
-- @[simp] lemma isPairValueAttempt_unique_eq_ExistsAttempt
--     (F : V → V) (α : V) :
--     (∃! p, IsPairValueAttempt F α p) = ExistsAttempt F α := by
--   apply eq_iff_iff.mpr
--   constructor <;> intro h
--   · simp only [IsPairValueAttempt] at h
--     apply ExistsUnique.exists at h
--     rcases h with ⟨p, f, hfleft, hfright⟩
--     use f
--   · exact isPairValueAttempt_unique_of_ExistsAttempt F α h

-- /--
-- A trivial lemma which maybe I can remove if I convert everything to use `α : Ordinal V` instead of `α : V`.
-- TODO: Remove this if I decide to use `Ordinal V` instead.
-- -/
-- lemma forall_ExistsAttmept_of_mem
--     (F : V → V) {α : V} [hα : IsTransitive α] {β : V} (hβα : β ∈ α)
--     (h : ∀ γ ∈ α, ExistsAttempt F γ) : ∀ γ ∈ β, ExistsAttempt F γ := by
--   exact fun γ hγβ ↦ (h γ (IsTransitive.mem_trans hα hγβ hβα))

section Replacement

/--
Function that outputs an attempt of length `α`, subject to the assumption that for all `β < α`, there is an attempt of length `β`.
This is a big function constructed using replacement.
-/
noncomputable def replOfExistsAttempt
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (F : V → V) [hFdef : ℒₛₑₜ-function₁[V] F]
    (α : V) : V :=
  repl (pairValueAttempt F) α

-- TODO: Might not be necessary, might be replacable with simp
@[simp] lemma mem_replOfExistsAttempt_iff
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (F : V → V) (α : V)
    [hFdef : ℒₛₑₜ-function₁[V] F]
    (p : V) :
    p ∈ replOfExistsAttempt F α ↔ ∃ β ∈ α, p = pairValueAttempt F β := by
  apply repl_spec

@[simp] lemma kpair_mem_replOfExistsAttempt_iff
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    {F : V → V} {α : Ordinal V}
    [hFdef : ℒₛₑₜ-function₁[V] F]
    {β y : V} :
    ⟨β, y⟩ₖ ∈ replOfExistsAttempt F α ↔ β ∈ α.val ∧ ⟨β, y⟩ₖ = pairValueAttempt F β := by
  simp only [mem_replOfExistsAttempt_iff]
  constructor <;> intro h
  · obtain ⟨β, hβα, h⟩ := h
    rw [eq_of_kpair_eq_pairValueAttempt h] at *
    exact ⟨hβα, h⟩
  · use β

/- Some definability lemmas, TODO: Might move these to `ZF.lean`. -/
def repl.dfn (φ : SetTheorySemiformula V 2) : SetTheorySemiformula V 2 :=
  f“Y X. ∀ y, y ∈ Y ↔ ∃ x ∈ X, y = !φ x”

def replRel.dfn [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (φ : SetTheorySemiformula V 2) : SetTheorySemiformula V 2 :=
  f“Y X. ∀ y, y ∈ Y ↔ ∃ x ∈ X, !φ x y”

def replRelOverSet.dfn [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (φ : SetTheorySemiformula V 2) : SetTheorySemiformula V 2 :=
  f“Y X. ∀ y, y ∈ Y ↔ ∃ x ∈ X, !φ x y”

def replOfExistsAttempt.dfn [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (φ : SetTheorySemiformula V 2) :
    SetTheorySemiformula V 2 :=
  f“α Y. ∀ y, y ∈ Y ↔ ∃ β ∈ α, y = !φ β”

instance repl.defined [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (F : V → V) (hF : IsDefinedByWithParam (fun v ↦ v 0 = F (v 1)) φ) :
  ℒₛₑₜ-function₁ fun X ↦ repl F X via repl.dfn φ := by
  use repl.dfn φ
  intro v
  simp_all [repl, repl.dfn]

instance replRel.definable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (R : V → V → Prop) (h : ∀ x, ∃! y, R x y) (hR : ℒₛₑₜ-relation R) : ℒₛₑₜ-function₁ fun X ↦ replRel X R h := by
  have hdefined := Classical.choose_spec hR.definable
  use replRel.dfn R hR
  intro v
  simp_all [replRel, replRel.dfn]

/--
Unfortunately this definability instance has a modified `h` condition. TODO: See if thi can be replaced with a usual one as in `replRelOverSet`.
-/
instance replRelOverSet.definable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (R : V → V → Prop) (h : (X : V) → ∀ x ∈ X, ∃! y, R x y) (hR : ℒₛₑₜ-relation R) :
    ℒₛₑₜ-function₁ fun X ↦ replRelOverSet R X (h X) := by
  have hdefined := Classical.choose_spec hR.definable
  use replRelOverSet.dfn R hR
  intro v
  simp_all [replRelOverSet, replRelOverSet.dfn]

lemma replOfExistsAttempt.defined
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (F : V → V) (hF : ℒₛₑₜ-function₁[V] F) :
    -- ℒₛₑₜ-relation fun (α y : V) ↦ ∀ (hexists : ∀ β ∈ α, ExistsAttempt F β), y = replOfExistsAttempt F α hexists := by
    IsDefinedByWithParam (fun (v : Fin 2 → V) ↦ v 1 = replOfExistsAttempt F (v 0)) (replOfExistsAttempt.dfn F hF) := by
  intro v
  simp_all [replOfExistsAttempt, replOfExistsAttempt.dfn]
  -- TODO: See if I can simplify this
  constructor <;> intro h₂
  · ext z
    simp_all [pairValueAttempt.defined]
  · simp_all [pairValueAttempt.defined]

instance replOfExistsAttempt.definable
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (F : V → V) [hF : ℒₛₑₜ-function₁[V] F] :
    ℒₛₑₜ-function₁[V] (replOfExistsAttempt F (hFdef := hF)) := by
  sorry

example
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (F : V → V) (α : Ordinal V)
    [hFdef : ℒₛₑₜ-function₁[V] F]
    (β y : V) :
    ⟨β, y⟩ₖ ∈ replOfExistsAttempt F α ↔ β ∈ α.val ∧ ∃ f, y = F f ∧ IsAttempt F β f := by
  simp [kpair_mem_replOfExistsAttempt_iff, pairValueAttempt]

lemma domain_replOfExistsAttempt_eq
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (F : V → V) (α : Ordinal V)
    [hFdef : ℒₛₑₜ-function₁[V] F] :
    domain (replOfExistsAttempt F α) = α.val := by
  ext z
  simp only [mem_domain_iff, mem_replOfExistsAttempt_iff]
  constructor <;> intro h
  · rcases h with ⟨y, β, hβα, hβ⟩
    exact eq_of_kpair_eq_pairValueAttempt hβ ▸ hβα
  · use F (attemptOrEmpty F z)
    use z
    simp_all only [true_and, pairValueAttempt, true_and]

instance [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (F : V → V) (α : Ordinal V)
    [hFdef : ℒₛₑₜ-function₁[V] F] :
    IsFunction (replOfExistsAttempt F α) := by
  -- Name it for brevity
  let f := replOfExistsAttempt F α
  have hdomain : domain f = α.val := domain_replOfExistsAttempt_eq F α
  apply isFunction_iff.mpr
  apply mem_function_iff.mpr
  constructor
  · -- Show that `f` contains only ordered pairs
    intro p hpf
    obtain ⟨β, hβα, f, rfl, hf⟩ := (replRelOverSet_spec (by definability)).mp hpf
    apply kpair_mem_iff.mpr
    exact And.intro (mem_domain_of_kpair_mem hpf) (mem_range_of_kpair_mem hpf)
  · -- Show well-definedness of `f`
    intro x hx
    -- TODO: Can I shorten this by rewriting using `replRelOfMemExistsUnique_spec` first, before applying `existsUnique_of_exists_of_unique`?
    apply existsUnique_of_exists_of_unique
    · rw [hdomain] at hx
      use F (attemptOrEmpty F x)
      apply (replRelOverSet_spec (by definability)).mpr
      use x
      simp only [hx, pairValueAttempt, true_and]
      use Classical.choose (hexists x hx)
      simp only [true_and]
      apply Classical.choose_spec
    · intro y₁ y₂
      simp_all only [mem_replOfExistsAttempt_iff, pairValueAttempt, kpair_iff,
        ↓existsAndEq, true_and, exists_and_left, forall_exists_index, and_imp]
      intro hxα f₁ hy₁f₁ hf₁ f₂ hy₂f₂ hf₂
      have ⟨_, _, _⟩ := hf₁
      have ⟨_, _, _⟩ := hf₂
      let xo : Ordinal V := IsOrdinal.toOrdinal x
      rw [attempt_function_unique (α := xo) hf₁ hf₂]

/--
An auxiliary lemma about `replOfExistsAttempt`.
-/
lemma replOfExistsAttempt_aux
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (F : V → V) (hF : ℒₛₑₜ-function₁[V] F) :
    (α : Ordinal V) →
    IsAttempt F α (replOfExistsAttempt F α) := by
  let motive (α : V) : Prop := IsAttempt F α (replOfExistsAttempt F α)

  have motive_definable : ℒₛₑₜ-predicate motive := by definability

  refine transfinite_induction motive motive_definable ?_
  -- Now I just need to prove the transfinite induction.
  intro α ih
  have hα := Ordinal.ordinal α

  -- The case of (i) for `α`. This follows from ih for (ii) (i.e. `∀ β < α, ((ii) for β)`).
  have h_i : ((β : V) → (hβα : β ∈ α.val) → IsAttempt F β ((replOfExistsAttempt F α) ↾ β)) := by
    intro β hβα
    have hβ : IsOrdinal β := IsOrdinal.of_mem hβα
    let βo : Ordinal V := IsOrdinal.toOrdinal β
    -- Get a case of (ii) that's been proven up to this point in the transfinite induction
    have h_ii := ih βo hβα

    suffices h : (replOfExistsAttempt F α) ↾ β = replOfExistsAttempt F β from h ▸ h_ii
    ext p
    simp only [mem_restrict_iff, mem_replOfExistsAttempt_iff]
    constructor <;> intro h
    · rcases h with ⟨⟨γ, hγα, hγ⟩, ⟨x, hxβ, y, rfl⟩⟩
      use x
      refine And.intro hxβ ?_
      exact (eq_of_kpair_eq_pairValueAttempt hγ).symm ▸ hγ
    · rcases h with ⟨γ, hγβ, hγ⟩
      refine And.intro ?_ ?_
      · use γ
        exact And.intro (IsTransitive.mem_trans IsOrdinal.toIsTransitive hγβ hβα) hγ
      · exact ⟨γ, hγβ, F (attemptOrEmpty F γ), hγ⟩
  -- Proving (ii) for `α`
  refine ⟨hα, inferInstance, domain_replOfExistsAttempt_eq F α, ?_⟩
  intro β hβα y
  have hβ : IsOrdinal β := IsOrdinal.of_mem hβα
  let βo : Ordinal V := IsOrdinal.toOrdinal β

  suffices h : ⟨β, y⟩ₖ ∈ replOfExistsAttempt F α.val ↔ ∃ f, y = F f ∧ IsAttempt F β f from by
    constructor <;> intro h₂
    · obtain ⟨f, rfl, hf⟩ := h.mp h₂
      have : IsFunction f := hf.2.1
      have : IsFunction ((replOfExistsAttempt F (↑α)) ↾ ↑βo) := inferInstance
      simp only [attempt_function_unique hf (h_i βo hβα), toOrdinal_val, βo]
    · apply h.mpr
      use (replOfExistsAttempt F (↑α)) ↾ β
      simp only [h₂, true_and]
      exact h_i βo hβα
  have hexists : ExistsAttempt F β := ⟨replOfExistsAttempt F β, ih βo hβα⟩
  simp_all only [mem_replOfExistsAttempt_iff, pairValueAttempt, kpair_iff, ↓existsAndEq, true_and,
    motive]
  have hattempt : IsAttempt F β (attemptOrEmpty F β) := by
    simp_all [attemptOrEmpty, Classical.choose!_spec]
  sorry

/--
For any ordinal `α`, there exists an attempt function of length `α`.
-/
lemma attempt_function_exists
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (F : V → V) (hF : ℒₛₑₜ-function₁[V] F) :
    (α : Ordinal V) → ExistsAttempt F α := by
  let motive (α : V) : Prop := ExistsAttempt F α
  refine transfinite_induction motive inferInstance ?_
  intro α ih
  have hexists : ∀ β ∈ α.val, motive β := by
    intro β hβα
    have : IsOrdinal β := IsOrdinal.of_mem hβα
    exact ih (IsOrdinal.toOrdinal β) hβα
  use replOfExistsAttempt F α
  exact replOfExistsAttempt_aux F hF α

end LO.FirstOrder.SetTheory.IsOrdinal.Replacement
