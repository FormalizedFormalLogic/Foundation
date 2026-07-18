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

-- noncomputable def IsAttempt.dfn (F : V → V) [hFdef : ℒₛₑₜ-function₁ F] : SetTheorySemiformula V 2 :=
--   f“α f. ∀ β y, !kpair.dfn' β y ∈ f ↔ y = !(hFdef.definable.choose) (!restrict.dfn' f β)”
--   /- Cast `kpair.dfn` and `restrict.dfn` to a type that allows parameters, to work with `Semiformula.nestFormulaeFunc`. -/
--   where
--     kpair.dfn' : SetTheorySemiformula V 3 := (Rew.rewriteMap (Empty.elim : Empty → V)) ▹ kpair.dfn
--     restrict.dfn' : SetTheorySemiformula V 3 := (Rew.rewriteMap (Empty.elim : Empty → V)) ▹ restrict.dfn

/-
TODO: Find a way to make `hFdef` not a typeclass without getting an error.
-/
instance IsAttempt_definable (F : V → V) [hFdef : ℒₛₑₜ-function₁ F] :
    ℒₛₑₜ-relation[V] (fun β f ↦ IsAttempt F β f) := by
  definability

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

instance ExistsAttempt_definable
    (F : V → V)
    [hFdef : ℒₛₑₜ-function₁[V] F] :
    ℒₛₑₜ-predicate[V] (ExistsAttempt F) :=
  Language.Definable.exs
    (Language.Definable.retraction
      (IsAttempt_definable F)
      ![1, 0])

/--
`p` is a pair `⟨α, F f⟩ₖ` of an ordinal `α` and the value of `F` on an attempt `f` of length `α`.
This is a technical definition needed for the proof of the transfinite recursion theorem.
-/
def IsPairValueAttempt (F : V → V) (α : V) (p : V) : Prop :=
  ∃ f, p = ⟨α, F f⟩ₖ ∧ IsAttempt F α f

instance IsPairValueAttempt_definable (F : V → V)
    [hFdef : ℒₛₑₜ-function₁[V] F] :
    ℒₛₑₜ-relation[V] (IsPairValueAttempt F) :=
  by definability

-- I'm too lazy to explicitly construct one, so I'll choose a formula which works
noncomputable def IsPairValueAttempt.dfn (F : V → V) [hFdef : ℒₛₑₜ-function₁ F] : SetTheorySemiformula V 2 :=
  Classical.choose (IsPairValueAttempt_definable F).definable

lemma IsPairValueAttempt.defined (F : V → V) [hFdef : ℒₛₑₜ-function₁ F] :
    IsDefinedByWithParam (fun v ↦ IsPairValueAttempt F (v 0) (v 1)) (IsPairValueAttempt.dfn F) := by
  simpa [dfn] using Classical.choose_spec (IsPairValueAttempt_definable F).definable

lemma eq_of_IsPairValueAttempt {F : V → V} {α : V} {x y : V} (h : IsPairValueAttempt F α ⟨x, y⟩ₖ) :
    x = α := by
  simp only [IsPairValueAttempt, kpair_iff] at h
  rcases h with ⟨_, ⟨h, -⟩, _⟩
  exact h

lemma isPairValueAttempt_unique_of_ExistsAttempt
    (F : V → V) (α : V) :
    ExistsAttempt F α → ∃! p, IsPairValueAttempt F α p := by
  intro h
  let ⟨f, hf⟩ := h
  have : IsOrdinal α := hf.1
  have : IsFunction f := hf.2.1
  let αo : Ordinal V := IsOrdinal.toOrdinal α
  apply existsUnique_of_ExistsAttempt at h
  refine ExistsUnique.intro ⟨α, F f⟩ₖ ?_ ?_
  · simp only [IsPairValueAttempt, kpair_iff, true_and]
    use f
  · simp only [IsPairValueAttempt, forall_exists_index, and_imp]
    intro p₂ f₂ hp₂ hf₂
    have : IsFunction f₂ := hf₂.2.1
    simp_all only [attempt_function_unique (α := αo) hf hf₂]

/--
A characterization of when the right argument of `IsPairValueAttempt` is unique.
-/
@[simp] lemma isPairValueAttempt_unique_eq_ExistsAttempt
    (F : V → V) (α : V) :
    (∃! p, IsPairValueAttempt F α p) = ExistsAttempt F α := by
  apply eq_iff_iff.mpr
  constructor <;> intro h
  · simp only [IsPairValueAttempt] at h
    apply ExistsUnique.exists at h
    rcases h with ⟨p, f, hfleft, hfright⟩
    use f
  · exact isPairValueAttempt_unique_of_ExistsAttempt F α h

/--
A helper lemma that currently exists since I can't get `▸` to work in this case.
TODO: Remove this
-/
lemma forall_isPairValueAttempt_unique_of_forall_existsAttempt
    (F : V → V) (α : V) (hex : ∀ β ∈ α, ExistsAttempt F β) :
    ∀ β ∈ α, (∃! p, IsPairValueAttempt F β p) := by
  exact fun β hβα ↦ isPairValueAttempt_unique_of_ExistsAttempt F β (hex β hβα)

/--
A trivial lemma which maybe I can remove if I convert everything to use `α : Ordinal V` instead of `α : V`.
TODO: Remove this if I decide to use `Ordinal V` instead.
-/
lemma forall_ExistsAttmept_of_mem
    (F : V → V) {α : V} [hα : IsTransitive α] {β : V} (hβα : β ∈ α)
    (h : ∀ γ ∈ α, ExistsAttempt F γ) : ∀ γ ∈ β, ExistsAttempt F γ := by
  exact fun γ hγβ ↦ (h γ (IsTransitive.mem_trans hα hγβ hβα))

section Replacement

/--
Function that outputs an attempt of length `α`, subject to the assumption that for all `β < α`, there is an attempt of length `β`.
This is a big function constructed using replacement.
-/
noncomputable def replOfExistsAttempt
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (F : V → V) (α : V)
    [hFdef : ℒₛₑₜ-function₁[V] F]
    (hexists : ∀ β ∈ α, ExistsAttempt F β) : V :=
  replRelOverSet α
    (IsPairValueAttempt F)
    (forall_isPairValueAttempt_unique_of_forall_existsAttempt F α hexists)

-- TODO: Might not be necessary, might be replacable with simp
@[simp] lemma mem_replOfExistsAttempt_iff
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (F : V → V) (α : V)
    [hFdef : ℒₛₑₜ-function₁[V] F]
    (hexists : ∀ β ∈ α, ExistsAttempt F β) (p : V) :
    p ∈ replOfExistsAttempt F α hexists ↔ ∃ β ∈ α, IsPairValueAttempt F β p := by
  apply replRelOverSet_spec

@[simp] lemma kpair_mem_replOfExistsAttempt_iff
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    {F : V → V} {α : Ordinal V}
    [hFdef : ℒₛₑₜ-function₁[V] F]
    {hexists : ∀ β ∈ α.val, ExistsAttempt F β} {β y : V} :
    ⟨β, y⟩ₖ ∈ replOfExistsAttempt F α hexists ↔ β ∈ α.val ∧ IsPairValueAttempt F β ⟨β, y⟩ₖ := by
  simp only [mem_replOfExistsAttempt_iff]
  constructor <;> intro h
  · obtain ⟨β, hβα, h⟩ := h
    rw [eq_of_IsPairValueAttempt h] at *
    exact ⟨hβα, h⟩
  · use β

/- Some definability lemmas, TODO: Might move these to `ZF.lean`. -/
noncomputable def repl.dfn [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (F : V → V) (hF : ℒₛₑₜ-function₁ F) : SetTheorySemiformula V 2 :=
  f“Y X. ∀ y, y ∈ Y ↔ ∃ x ∈ X, y = !(hF.definable.choose) x”

noncomputable def replRel.dfn [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (R : V → V → Prop) (hR : ℒₛₑₜ-relation R) : SetTheorySemiformula V 2 :=
  f“Y X. ∀ y, y ∈ Y ↔ ∃ x ∈ X, !(hR.definable.choose) x y”

noncomputable def replRelOverSet.dfn [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (R : V → V → Prop) (hR : ℒₛₑₜ-relation R) : SetTheorySemiformula V 2 :=
  f“Y X. ∀ y, y ∈ Y ↔ ∃ x ∈ X, !(hR.definable.choose) x y”

noncomputable def replOfExistsAttempt.dfn [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (F : V → V) (hF : ℒₛₑₜ-function₁[V] F) :
    SetTheorySemiformula V 2 :=
  f“α Y. ∀ y, y ∈ Y ↔ ∃ β ∈ α, !(IsPairValueAttempt.dfn F) β y”

instance repl.definable [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (F : V → V) (hP : ℒₛₑₜ-function₁ F) : ℒₛₑₜ-function₁ fun X ↦ repl X F := by
  have hdefined := Classical.choose_spec hP.definable
  use repl.dfn F hP
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
    ℒₛₑₜ-function₁ fun X ↦ replRelOverSet X R (h X) := by
  have hdefined := Classical.choose_spec hR.definable
  use replRelOverSet.dfn R hR
  intro v
  simp_all [replRelOverSet, replRelOverSet.dfn]

lemma replOfExistsAttempt_definable
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (F : V → V) (hF : ℒₛₑₜ-function₁[V] F) (hexists : ∀ β ∈ α, ExistsAttempt F β) :
    -- ℒₛₑₜ-relation fun (α y : V) ↦ ∀ (hexists : ∀ β ∈ α, ExistsAttempt F β), y = replOfExistsAttempt F α hexists := by
    Language.Definable ℒₛₑₜ fun (v : Fin 2 → V) ↦ ∀ (hexists : ∀ β ∈ v 0, ExistsAttempt F β), v 1 = replOfExistsAttempt F (v 0) hexists := by
  use replOfExistsAttempt.dfn F hF
  intro v
  simp_all [replOfExistsAttempt, replOfExistsAttempt.dfn]
  -- TODO: See if I can simplify this
  constructor <;> intro h₂
  · intro hexists
    ext z
    simp_all [IsPairValueAttempt.defined]
  · intro x
    simp [IsPairValueAttempt.defined, (mem_replOfExistsAttempt_iff F x (hexists x sorry))]
    sorry

example
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (F : V → V) (α : Ordinal V)
    [hFdef : ℒₛₑₜ-function₁[V] F]
    (hexists : ∀ β ∈ α.val, ExistsAttempt F β) (β y : V) :
    ⟨β, y⟩ₖ ∈ replOfExistsAttempt F α hexists ↔ β ∈ α.val ∧ ∃ f, y = F f ∧ IsAttempt F β f := by
  simp [IsPairValueAttempt]

lemma domain_replOfExistsAttempt_eq
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (F : V → V) (α : Ordinal V)
    [hFdef : ℒₛₑₜ-function₁[V] F]
    (hexists : ∀ β ∈ α.val, ExistsAttempt F β) :
    domain (replOfExistsAttempt F α hexists) = α.val := by
  ext z
  simp only [mem_domain_iff, mem_replOfExistsAttempt_iff]
  constructor <;> intro h
  · rcases h with ⟨y, β, hβα, hβ⟩
    exact eq_of_IsPairValueAttempt hβ ▸ hβα
  · specialize hexists z h
    use F (Classical.choose hexists)
    use z
    simp_all only [true_and, IsPairValueAttempt, kpair_iff, true_and]
    grind only [usr Exists.choose_spec]

instance [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (F : V → V) (α : Ordinal V)
    [hFdef : ℒₛₑₜ-function₁[V] F]
    (hexists : ∀ β ∈ α.val, ExistsAttempt F β) :
    IsFunction (replOfExistsAttempt F α hexists) := by
  -- Name it for brevity
  let f := replOfExistsAttempt F α hexists
  have hdomain : domain f = α.val := domain_replOfExistsAttempt_eq F α hexists
  apply isFunction_iff.mpr
  apply mem_function_iff.mpr
  constructor
  · -- Show that `f` contains only ordered pairs
    intro p hpf
    let P := replacement_rel_exists_of_mem_existsUnique α.val
      (IsPairValueAttempt F)
      (forall_isPairValueAttempt_unique_of_forall_existsAttempt F α hexists)
    obtain ⟨β, hβα, f, rfl, hf⟩ := (replRelOverSet_spec (by definability)).mp hpf
    apply kpair_mem_iff.mpr
    exact And.intro (mem_domain_of_kpair_mem hpf) (mem_range_of_kpair_mem hpf)
  · -- Show well-definedness of `f`
    intro x hx
    -- TODO: Can I shorten this by rewriting using `replRelOfMemExistsUnique_spec` first, before applying `existsUnique_of_exists_of_unique`?
    apply existsUnique_of_exists_of_unique
    · rw [hdomain] at hx
      use F (Classical.choose (hexists x hx))
      apply (replRelOverSet_spec (by definability)).mpr
      use x
      simp only [hx, IsPairValueAttempt, kpair_iff, true_and]
      use Classical.choose (hexists x hx)
      simp only [true_and]
      apply Classical.choose_spec
    · intro y₁ y₂
      simp_all only [mem_replOfExistsAttempt_iff, IsPairValueAttempt, kpair_iff,
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
    (α : Ordinal V) → (hα : IsOrdinal α.val) →
    (hexists : ∀ β ∈ α.val, ExistsAttempt F β) →
    IsAttempt F α (replOfExistsAttempt F α hexists) := by
  -- Motive of transfinite induction
  let motive (α : V) : Prop := (hα : IsOrdinal α) →
    (hexists : ∀ β ∈ α, ExistsAttempt F β) →
    IsAttempt F α (replOfExistsAttempt F α hexists)

  have motive_definable : ℒₛₑₜ-predicate motive := by
    refine Language.Definable.imp ?_ ?_
    · exact IsOrdinal.definable
    · have := replOfExistsAttempt_definable F hF hexists
      --refine Language.Definable.imp ?_ ?_
      sorry

  refine transfinite_induction motive motive_definable ?_
  -- Now I just need to prove the transfinite induction.
  intro α ih hα hexists

  -- The case of (i) for `α`. This follows from ih for (ii) (i.e. `∀ β < α, ((ii) for β)`).
  have h_i : ((β : V) → (hβα : β ∈ α.val) → IsAttempt F β ((replOfExistsAttempt F α hexists) ↾ β)) := by
    intro β hβα
    have hβ : IsOrdinal β := IsOrdinal.of_mem hβα
    let βo : Ordinal V := IsOrdinal.toOrdinal β
    -- Get a case of (ii) that's been proven up to this point in the transfinite induction
    have h_ii := ih βo hβα hβ (forall_ExistsAttmept_of_mem F hβα hexists)

    suffices h : (replOfExistsAttempt F α hexists) ↾ β = replOfExistsAttempt F β (forall_ExistsAttmept_of_mem F hβα hexists) from h ▸ h_ii
    ext p
    simp only [mem_restrict_iff, mem_replOfExistsAttempt_iff]
    constructor <;> intro h
    · rcases h with ⟨⟨γ, hγα, hγ⟩, ⟨x, hxβ, y, rfl⟩⟩
      use x
      refine And.intro hxβ ?_
      exact (eq_of_IsPairValueAttempt hγ).symm ▸ hγ
    · rcases h with ⟨γ, hγβ, hγ⟩
      refine And.intro ?_ ?_
      · use γ
        exact And.intro (IsTransitive.mem_trans IsOrdinal.toIsTransitive hγβ hβα) hγ
      · simp only [IsPairValueAttempt] at hγ
        aesop
  -- Proving (ii) for `α`
  refine ⟨hα, inferInstance, domain_replOfExistsAttempt_eq F α hexists, ?_⟩
  intro β hβα y
  have hβ : IsOrdinal β := IsOrdinal.of_mem hβα
  let βo : Ordinal V := IsOrdinal.toOrdinal β

  suffices h : ⟨β, y⟩ₖ ∈ replOfExistsAttempt F α.val hexists ↔ ∃ f, y = F f ∧ IsAttempt F β f from by
    constructor <;> intro h₂
    · obtain ⟨f, rfl, hf⟩ := h.mp h₂
      have : IsFunction f := hf.2.1
      have : IsFunction ((replOfExistsAttempt F (↑α) hexists) ↾ ↑βo) := inferInstance
      simp only [attempt_function_unique hf (h_i βo hβα), toOrdinal_val, βo]
    · apply h.mpr
      use (replOfExistsAttempt F (↑α) hexists) ↾ β
      simp only [h₂, true_and]
      exact h_i βo hβα
  simp_all only [kpair_mem_replOfExistsAttempt_iff, true_and, IsPairValueAttempt, kpair_iff, true_and, motive]

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
  use replOfExistsAttempt F α hexists
  exact replOfExistsAttempt_aux F hF α inferInstance hexists

end LO.FirstOrder.SetTheory.IsOrdinal.Replacement
