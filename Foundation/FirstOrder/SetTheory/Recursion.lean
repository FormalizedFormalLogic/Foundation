module

public import Foundation.FirstOrder.SetTheory.Ordinal.Basic

@[expose] public section

namespace LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V ⊧ₘ* 𝗭]

namespace IsOrdinal

variable {α β γ : V}

/--
Domain of a union of functions: if each member has domain included in `α`, and every point of `α`
appears in some member domain, then the union has domain exactly `α`.
-/
lemma domain_sUnion_eq_of_domain_subset_and_cover
    {α C : V} (hsubset : ∀ f ∈ C, IsFunction f ∧ domain f ⊆ α)
    (hcover : ∀ x ∈ α, ∃ f ∈ C, x ∈ domain f) :
    domain (⋃ˢ C) = α := by
  apply subset_antisymm
  · intro x hxU
    rcases mem_domain_iff.mp hxU with ⟨y, hxyU⟩
    rcases mem_sUnion_iff.mp hxyU with ⟨f, hfC, hxyf⟩
    exact (hsubset f hfC).2 _ (mem_domain_of_kpair_mem hxyf)
  · intro x hxα
    rcases hcover x hxα with ⟨f, hfC, hxd⟩
    rcases mem_domain_iff.mp hxd with ⟨y, hxyf⟩
    refine mem_domain_iff.mpr ⟨y, ?_⟩
    exact mem_sUnion_iff.mpr ⟨f, hfC, hxyf⟩

/-! ### Attempt functions -/

/--
`f` is an attempt of length `α` for the relation `φ`, meaning that the domain of `f` is `α`, and for all `β` < `α`, it holds that `f(β) = y` iff `φ (f ↾ β) y`.
The "attempt" terminology may be due to Paul Taylor.
-/
def IsAttempt (φ : V → V → Prop) (α f : V) : Prop :=
  IsOrdinal α ∧ IsFunction f ∧ domain f = α ∧
    ∀ β ∈ α, ∀ y, ⟨β, y⟩ₖ ∈ f ↔ φ y (f ↾ β)

/-- A version of `IsAttempt` for a function `F : V → V`. -/
def IsAttemptGraph (F : V → V) (α f : V) : Prop :=
  IsAttempt (Function.Graph F) α f

def IsAttemptGraphOn (F : V → V) (α : Ordinal V) (f : V) : Prop :=
  IsAttemptGraph F α.val f

@[simp] lemma isAttemptGraphOn_val
    (F : V → V) (α : Ordinal V) (f : V) :
    IsAttemptGraphOn F α f ↔ IsAttemptGraph F α.val f := Iff.rfl

instance isAttemptGraph_definable
    (F : V → V) (hFdef : ℒₛₑₜ-function₁[V] F) :
    ℒₛₑₜ-relation[V] (fun β f ↦ IsAttemptGraph F β f) := by
  definability

/--
An existential property that characterized the biconditional property in `IsAttemptGraph`.
-/
lemma attempt_iff_iff_exists_ord (F : V → V) (α : Ordinal V) {f : V} [IsFunction f] (hdf : domain f = α.val) :
    (∀ β ∈ α.val, ∃ z, ⟨β, z⟩ₖ ∈ f ∧ Function.Graph F z (f ↾ β)) ↔
    ∀ β ∈ α.val, ∀ y, ⟨β, y⟩ₖ ∈ f ↔ Function.Graph F y (f ↾ β) := by
  constructor <;> intro h
  · intro β hβα y
    rcases h β hβα with ⟨z, hβz, hzF⟩
    constructor
    · intro hβy
      have hyz : y = z := IsFunction.unique hβy hβz
      simpa [hyz] using hzF
    · intro hyF
      have huniq := functionGraph_functionLike F (f ↾ β)
      have hyz : y = z := huniq.unique hyF hzF
      simpa [hyz] using hβz
  · intro β hβα
    specialize h β hβα
    apply (mem_ext_iff.mp hdf β).mpr at hβα
    apply mem_domain_iff.mp at hβα
    obtain ⟨y, hy⟩ := hβα
    use y
    simp_all only [and_self]

/--
Getting isAttemptGraph from a sufficient condition.
-/
lemma isAttemptGraph_of_ordinal_domain_exists_ord (F : V → V) (α : Ordinal V) {f : V} [IsFunction f] (hdf : domain f = α.val)
    (hrec : ∀ β ∈ α.val, ∃ z, ⟨β, z⟩ₖ ∈ f ∧ Function.Graph F z (f ↾ β)) :
    IsAttemptGraph F α f := by
  rename IsFunction f => hf
  have hα : IsOrdinal α.val := Ordinal.instIsOrdinalVal
  have hrec' : ∀ β ∈ α.val, ∀ (y : V), ⟨β, y⟩ₖ ∈ f ↔ Function.Graph F y (f ↾ β) :=
    (attempt_iff_iff_exists_ord F α hdf).mp hrec
  exact ⟨hα, hf, hdf, hrec'⟩

/-! #### Uniqueness of attempt functions -/

lemma attempt_function_coherent (F : V → V) (α : Ordinal V) {f g : V} [IsFunction f] [IsFunction g]
    (hf : IsAttemptGraph F α f) (hg : IsAttemptGraph F α g) :
    ∀ β : Ordinal V, β.val ⊆ α.val → f ↾ β.val = g ↾ β.val := by
  rcases hf with ⟨_, _, _, _⟩
  rcases hg with ⟨_, _, _, _⟩
  refine transfinite_induction (P := fun x ↦ x ⊆ α.val → f ↾ x = g ↾ x) (by definability) ?_
  intro β ihβ hβα
  apply mem_ext_iff.mpr
  simp only [mem_restrict_iff, and_congr_left_iff, forall_exists_index, and_imp]
  intro p x hxβ y rfl
  have : IsOrdinal x := IsOrdinal.of_mem hxβ
  let ξ : Ordinal V := IsOrdinal.toOrdinal x
  have hxα : x ∈ α.val := hβα x hxβ
  have hξα : ξ.val ⊆ α.val := by
    exact subset_trans (β.ordinal.toIsTransitive.transitive x hxβ) hβα
  have hfξgξ : f ↾ ξ = g ↾ ξ := by
    exact ihβ ξ (by aesop) (by aesop)
  simp_all only [toOrdinal_val, ξ]

/--
An attempt function of length `α`, if existing, is unique.
-/
lemma attempt_function_unique_on (F : V → V) (α : Ordinal V) {f g : V} [IsFunction f] [IsFunction g]
    (hf : IsAttemptGraph F α f) (hg : IsAttemptGraph F α g) :
    f = g := by
  have hrestr :
      ∀ β : Ordinal V, β.val ⊆ α.val → f ↾ β.val = g ↾ β.val := by
    apply attempt_function_coherent <;> assumption
  have hαfg : f ↾ α.val = g ↾ α.val := hrestr α (subset_refl α.val)
  have hfα : f ↾ α.val = f := IsFunction.restrict_eq_self f α.val (subset_of_eq hf.2.2.1)
  have hgα : g ↾ α.val = g := IsFunction.restrict_eq_self g α.val (subset_of_eq hg.2.2.1)
  simp_all

/--
If two functions with the same ordinal domain satisfy the same recursive clause at each stage,
then they are equal.
-/
lemma attempt_function_unique_of_exists_on (F : V → V) (α : Ordinal V) {f g : V} [IsFunction f] [IsFunction g]
    (hf : IsAttemptGraph F α f)
    (hg : IsAttemptGraph F α g) :
    f = g := by
  apply attempt_function_unique_on F α hf hg

/-- Two recursion-function graphs on the same ordinal domain are equal. -/
lemma isAttemptGraph_unique_on (F : V → V) {α : Ordinal V} {f g : V}
    (hf : IsAttemptGraphOn F α f)
    (hg : IsAttemptGraphOn F α g) :
    f = g := by
  let : IsFunction f := hf.2.1
  let : IsFunction g := hg.2.1
  exact attempt_function_unique_of_exists_on F α hf hg

/--
Coherence: if `β ∈ α`, an attempt function on `α` restricts to the attmept function on `β`.
-/
lemma attempt_function_restrict_eq_of_mem_on
    (F : V → V)
    {α β : Ordinal V} {f g : V} [IsFunction f] [IsFunction g]
    (hβα : β < α)
    (hf : IsAttemptGraph F α f)
    (hg : IsAttemptGraph F β g) :
    f ↾ β.val = g := by
  rcases hf with ⟨_, _, hdf, hrecf⟩
  have hdg := hg.2.2.1
  have : IsFunction (f ↾ β.val) := IsFunction.restrict f β.val
  have hsubseteq : β.val ⊆ α.val := by
    apply le_of_lt at hβα
    apply Ordinal.le_def.mp at hβα
    assumption
  have hαβ : α.val ∩ β.val = β.val := inter_eq_right_of_subset hsubseteq
  suffices IsAttemptGraph F β (f ↾ β.val) by
    rw [← restrict_restrict_of_subset (A := β.val) subset_rfl]
    rw [← IsFunction.restrict_eq_self (A := β.val) (f := g) (subset_of_eq hdg)]
    apply (attempt_function_coherent F β this hg β subset_rfl)
  unfold IsAttemptGraph IsAttempt
  simp only [Ordinal.instIsOrdinalVal, this, domain_restrict_eq, hdf, hαβ, true_and]
  intro γ hγβ y
  have hγα : γ ∈ α.val := by aesop
  have : IsOrdinal γ := of_mem hγβ
  have hγsusbetβ : γ ⊆ β.val := by grind
  simp_all [restrict_restrict_eq_restrict_inter, mem_restrict_iff]

/-- Any two attempt functions agree on overlapping inputs. -/
lemma attempt_function_coherent_on
    (F : V → V)
    {α β : Ordinal V} {f g x y₁ y₂ : V}
    [IsFunction f] [IsFunction g]
    -- (hrecf : ∀ ξ ∈ β.val, ∃ z, ⟨ξ, z⟩ₖ ∈ f ∧ Function.Graph F z (f ↾ ξ))
    -- (hrecg : ∀ ξ ∈ γ.val, ∃ z, ⟨ξ, z⟩ₖ ∈ g ∧ Function.Graph F z (g ↾ ξ))
    (hf : IsAttemptGraph F α f)
    (hg : IsAttemptGraph F β g)
    (hxy₁ : ⟨x, y₁⟩ₖ ∈ f) (hxy₂ : ⟨x, y₂⟩ₖ ∈ g) :
    y₁ = y₂ := by
  have := hf.2.1
  have := hg.2.1
  rcases IsOrdinal.mem_trichotomy α.val β.val with (hαβ | heq | hβα) <;> simp_all only [← Ordinal.lt_def]
  · have hrestrict := attempt_function_restrict_eq_of_mem_on F hαβ hg hf
    rw [← hrestrict] at hxy₁
    have hxy₁ := (kpair_mem_restrict_iff.mp hxy₁).1
    exact IsFunction.unique hxy₁ hxy₂
  · simp_all only [attempt_function_unique_on F β hf hg]
    simp only [IsFunction.unique hxy₁ hxy₂]
  · have hrestrict := attempt_function_restrict_eq_of_mem_on F hβα hf hg
    rw [← hrestrict] at hxy₂
    have hxy₂ := (kpair_mem_restrict_iff.mp hxy₂).1
    exact IsFunction.unique hxy₁ hxy₂

/-! #### Existence and choices of attempt functions -/

/--
Existence of attempt functions on arbitrary ordinal domains,
in existential-stage form.
-/
def ExistsAttempt (φ : V → V → Prop) (α : V) : Prop :=
  ∃ f : V, IsFunction f ∧ domain f = α ∧
    ∀ β ∈ α, ∃ z, ⟨β, z⟩ₖ ∈ f ∧ φ (f ↾ β) z

def ExistsAttemptOfFunction (F : V → V) (α : V) : Prop :=
  ∃ f : V, IsAttemptGraph F α f

/--
Ordinal-packaged form of `ExistsAttemptOfFunction`.
-/
def ExistsAttemptOfFunctionOn (F : V → V) (α : Ordinal V) : Prop :=
  ExistsAttemptOfFunction F α.val

/-- On ordinal domains, `ExistsAttemptOfFunction` implies `∃!`. -/
lemma existsAttemptOfFunction_existsUnique_on (F : V → V) (α : Ordinal V) (hex : ExistsAttemptOfFunctionOn F α) :
    ∃! f : V, IsAttemptGraphOn F α f := by
  rcases hex with ⟨f, hf⟩
  exact ⟨f, hf, fun g hg ↦ (isAttemptGraph_unique_on F (α := α) hf hg).symm⟩

instance existsAttemptOfFunction_definable
    (F : V → V)
    (hFdef : ℒₛₑₜ-function₁[V] F) :
    ℒₛₑₜ-predicate[V] (ExistsAttemptOfFunction F) :=
  Language.Definable.exs
    (Language.Definable.retraction
      (isAttemptGraph_definable F hFdef)
      ![1, 0])

/--
Choose an attempt function of length `β` if one exists.
Otherwise, return an arbitrary value.
-/
noncomputable def attemptOrDefault
    (F : V → V) (α : V) : V := by
  classical
  by_cases hα : IsOrdinal α ∧ ExistsAttemptOfFunction F α
  · exact Classical.choose hα.2
  · exact Classical.arbitrary V

/--
If there is an attempt of length `α`, then `attemptOrDefault F α.val` is an attempt graph.
-/
lemma attemptOrDefault_isAttemptGraph_of_exists
    (F : V → V) (α : Ordinal V)
    (hexists : ExistsAttemptOfFunctionOn F α) :
    IsAttemptGraphOn F α (attemptOrDefault F α.val) := by
  have hcond : IsOrdinal α.val ∧ ExistsAttemptOfFunction F α.val := ⟨α.ordinal, hexists⟩
  simp only [attemptOrDefault, hcond]
  exact Classical.choose_spec hexists

lemma attemptOrDefault_eq_iff
    (F : V → V) (β y : V) :
    y = attemptOrDefault F β ↔
      (IsOrdinal β ∧ ExistsAttemptOfFunction F β ∧
        IsAttemptGraph F β y) ∨
      (¬(IsOrdinal β ∧ ExistsAttemptOfFunction F β) ∧
        y = Classical.arbitrary V) := by
  constructor
  · intro hy; subst hy
    by_cases hcond : IsOrdinal β ∧ ExistsAttemptOfFunction F β
    · letI : IsOrdinal β := hcond.1
      let βo : Ordinal V := IsOrdinal.toOrdinal β
      have hexo : ExistsAttemptOfFunctionOn F βo := by
        simpa [ExistsAttemptOfFunctionOn, βo] using hcond.2
      left
      refine ⟨hcond.1, hcond.2, ?_⟩
      simpa [βo] using attemptOrDefault_isAttemptGraph_of_exists F βo hexo
    · right; exact ⟨hcond, by simp [attemptOrDefault, hcond]⟩
  · rintro (⟨hord, hex, hrecf⟩ | ⟨hnex, rfl⟩)
    · let βo : Ordinal V := IsOrdinal.toOrdinal β
      have hcond : IsOrdinal β ∧ ExistsAttemptOfFunction F β := ⟨hord, hex⟩
      simp only [attemptOrDefault, hcond]
      have hspec := Classical.choose_spec hex
      exact isAttemptGraph_unique_on (F := F) (α := βo) (by simpa [βo] using hrecf) (by simpa [βo] using hspec)
    · simp [attemptOrDefault, hnex]

instance attemptOrDefault_definable
    (F : V → V)
    (hFdef : ℒₛₑₜ-function₁[V] F) :
    ℒₛₑₜ-function₁[V] (attemptOrDefault F) := by
  letI : ℒₛₑₜ-function₁[V] F := hFdef
  have hRdef : ℒₛₑₜ-relation[V] (fun y β ↦
      (IsOrdinal β ∧ ExistsAttemptOfFunction F β ∧
        IsAttemptGraph F β y) ∨
      (¬(IsOrdinal β ∧ ExistsAttemptOfFunction F β) ∧
        y = Classical.arbitrary V)) := by
    unfold ExistsAttemptOfFunction IsAttemptGraph
    definability
  have hEq : (fun y β ↦ y = attemptOrDefault F β) =
      (fun y β ↦ (IsOrdinal β ∧ ExistsAttemptOfFunction F β ∧
        IsAttemptGraph F β y) ∨
      (¬(IsOrdinal β ∧ ExistsAttemptOfFunction F β) ∧
        y = Classical.arbitrary V)) := by
    funext y β
    exact propext (attemptOrDefault_eq_iff F β y)
  show ℒₛₑₜ-relation[V] (fun y β ↦ y = attemptOrDefault F β)
  exact hEq ▸ hRdef

/--
Successor step for transfinite-recursion functions in existential-stage form.
-/
lemma attempt_function_exists_succ_on
    (F : V → V) (α : Ordinal V) {f : V} [IsFunction f]
    (hdf : domain f = α.val)
    -- (hrec : ∀ β ∈ α.val, ∃ z, ⟨β, z⟩ₖ ∈ f ∧ Function.Graph F z (f ↾ β)) :
    (hf : IsAttemptGraph F α f) :
    ∃ g : V, IsAttemptGraph F (succ α.val) g := by
  -- rcases functionGraph_functionLike F f with ⟨y, hy, -⟩
  let g := insert ⟨α.val, F (f ↾ α.val)⟩ₖ f
  use g
  have hg : ⟨α.val, F (f ↾ α.val)⟩ₖ ∈ g := by
    simp_all only [mem_insert, true_or, g]
  have hαnd : α.val ∉ domain f := by simp [hdf]
  have : IsFunction g := IsFunction.insert f α.val (F (f ↾ α.val)) hαnd
  have hfrestrict : f ↾ α = f := by
    apply IsFunction.restrict_eq_self f α.val
    rw [hdf]
  have hgrestrict : g ↾ α = f := by
    rw [restrict_insert_kpair_eq_restrict_of_not_mem (mem_irrefl α.val), ← hdf]
    apply IsFunction.restrict_eq_self f (domain f)
    apply subset_refl
  have hrestricteq {β : V} (hβα : β ∈ α.val) : g ↾ β = f ↾ β := by
    simpa [g] using restrict_insert_kpair_eq_restrict_of_not_mem (mem_asymm hβα)
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply IsOrdinal.succ
  · assumption
  · simp_all only [g, domain_insert, succ]
  · intro β hβsucc
    rcases show β = α.val ∨ β ∈ α.val by simpa [mem_succ_iff] using hβsucc with (rfl | hβα)
    · intro y
      constructor <;> intro h
      · simp only [mem_irrefl, not_false_eq_true, restrict_insert_kpair_eq_restrict_of_not_mem, g]
        exact IsFunction.unique h hg
      · rw [h, hgrestrict, ← hfrestrict]
        simp_all only [mem_insert, true_or, mem_irrefl, not_false_eq_true, mem_succ_self, g]
    · intro y
      have hmemiff : ⟨β, y⟩ₖ ∈ g ↔ ⟨β, y⟩ₖ ∈ f := by
        rw [mem_insert]
        aesop
      simp [hrestricteq hβα, hmemiff]
      simpa [hrestricteq] using (hf.2.2.2 β hβα y)

/--
Using replacement, collect all predecessor attempt functions on an ordinal domain.
-/
lemma replacement_collect_predecessor_attempt_functions_on
    [V ⊧ₘ* 𝗭𝗙]
    (F : V → V)
    (α : Ordinal V)
    (G : V → V) (hGdef : ℒₛₑₜ-function₁[V] G)
    (hprev : ∀ β ∈ α.val, IsAttemptGraph F β (G β)) :
    ∃ C : V, ∀ f : V, f ∈ C ↔ ∃ β ∈ α.val, IsAttemptGraph F β f := by
  rcases replacement_exists_on_of_definableFunction α.val G hGdef with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro f
  constructor
  · intro hfC
    rcases (hC f).1 hfC with ⟨β, hβα, rfl⟩
    exact ⟨β, hβα, hprev β hβα⟩
  · rintro ⟨β, hβα, hrecf⟩
    have hGβ := hprev β hβα
    letI : IsOrdinal β := IsOrdinal.of_mem hβα
    letI : IsFunction f := hrecf.2.1
    letI : IsFunction (G β) := hGβ.2.1
    let βo : Ordinal V := IsOrdinal.toOrdinal β
    have hfg : f = G β := attempt_function_unique_of_exists_on
      F βo (hf := by simpa [βo]) (hg := by simpa [βo])
    exact (hC f).2 ⟨β, hβα, hfg⟩

/--
Limit-style union construction: from a collected predecessor family `C`,
build an attempt function on `α` by union, assuming every `x ∈ α` lies in some `β ∈ α`
and predecessor recursion functions exist for all ordinals in `α`.
-/
lemma attempt_function_exists_sUnion_of_collected_on
    (F : V → V)
    (α : Ordinal V)
    {C : V}
    (hC : ∀ f : V, f ∈ C ↔ ∃ β ∈ α.val, IsAttemptGraph F β f)
    (hprev : ∀ β ∈ α.val, ∃ g : V, IsAttemptGraph F β g)
    (hlimit : ∀ x ∈ α.val, ∃ β ∈ α.val, x ∈ β) :
    ∃ f : V, IsAttemptGraph F α f := by
  let f : V := ⋃ˢ C
  have hcoh : ∀ u₁ ∈ C, ∀ u₂ ∈ C, ∀ (x y₁ y₂ : V), ⟨x, y₁⟩ₖ ∈ u₁ → ⟨x, y₂⟩ₖ ∈ u₂ → y₁ = y₂ := by
    intro u huC v hvC x y₁ y₂ hxyu hxyv
    rcases (hC u).1 huC with ⟨β, hβα, hu⟩
    rcases (hC v).1 hvC with ⟨γ, hγα, hv⟩
    have : IsOrdinal β := IsOrdinal.of_mem hβα
    have : IsOrdinal γ := IsOrdinal.of_mem hγα
    have : IsFunction u := hu.2.1
    have : IsFunction v := hv.2.1
    let βo : Ordinal V := IsOrdinal.toOrdinal β
    let γo : Ordinal V := IsOrdinal.toOrdinal γ
    exact attempt_function_coherent_on F (α := βo) (β := γo)
      hu hv hxyu hxyv
  have hf_isFunction : IsFunction f := by
    refine IsFunction.sUnion_of_coherent (hfunc := ?_) (hcoh := ?_)
    · intro u huC
      rcases (hC u).1 huC with ⟨β, hβα, hu⟩
      exact hu.2.1
    · apply hcoh
  -- Helper: get a member of C with a given β ∈ α as its domain
  have hC_mem : ∀ β ∈ α.val, ∃ g ∈ C, IsAttemptGraph F β g := by
    intro β hβα
    rcases hprev β hβα with ⟨g, hg⟩
    exact ⟨g, (hC g).2 ⟨β, hβα, hg⟩, hg.1, hg.2.1, hg.2.2.1, hg.2.2.2⟩
  have hf_domain : domain f = α.val := by
    apply domain_sUnion_eq_of_domain_subset_and_cover
    · intro u huC
      rcases (hC u).1 huC with ⟨β, hβα, hu⟩
      have hβsubα : β ⊆ α.val := α.ordinal.toIsTransitive.transitive _ hβα
      exact ⟨hu.2.1, by simpa [hu.2.2.1] using hβsubα⟩
    · intro x hxα
      rcases hlimit x hxα with ⟨β, hβα, hxβ⟩
      rcases hC_mem β hβα with ⟨g, hgC, -, -, hgd, -⟩
      exact ⟨g, hgC, by simpa [hgd] using hxβ⟩
  refine ⟨f, Ordinal.instIsOrdinalVal, hf_isFunction, hf_domain, ?_⟩
  intro γ hγα
  have : IsOrdinal γ := IsOrdinal.of_mem hγα
  rcases hlimit γ hγα with ⟨β, hβα, hγβ⟩
  have : IsOrdinal β := IsOrdinal.of_mem hβα
  -- Pick some u ∈ C whose domain β contains γ
  rcases hC_mem β hβα with ⟨u, huC, _, hfu, hdu, hrecu⟩
  have hβinterγ : β ∩ γ = γ := by
    suffices γ ⊆ β by
      exact inter_eq_right_of_subset this
    simp only [subset_iff, hγβ, or_true]

  have : IsFunction (f ↾ β) := IsFunction.restrict f β
  have hrestrictβ : f ↾ β = u := by
    ext p
    constructor <;> intro h <;> rcases IsFunction.mem_eq_kpair h with ⟨x, y, rfl⟩ <;>
      simp only [mem_restrict_iff, kpair_iff, exists_and_left, ↓existsAndEq, and_true, exists_eq_right'] at *
    · rw [kpair_mem_sUnion_iff] at h
      rcases h with ⟨⟨u', hu'C, hxyu'⟩, hxβ⟩
      rw [← hdu] at hxβ
      rcases mem_domain_iff.mp hxβ with ⟨y', hy'⟩
      simpa [hcoh u' hu'C u huC x y y' hxyu' hy']
    · constructor
      · apply subset_sUnion_of_mem huC at h
        exact h
      · simp only [← hdu]
        exact mem_domain_of_kpair_mem h
  have hrestrictγ : f ↾ γ = u ↾ γ := by
    rw [← hβinterγ,
      ← restrict_restrict_eq_restrict_inter,
      hrestrictβ, hβinterγ]
  intro y
  constructor <;> intro h <;> specialize hrecu γ hγβ y
  · simp only [hrestrictγ] at *
    apply hrecu.mp
    simp [← hrestrictβ]
    subst hdu
    simp_all only [mem_sUnion_iff, and_self, f]
  · simp only [hrestrictγ] at *
    apply hrecu.mpr at h
    apply mem_sUnion_iff.mpr
    use u

lemma zero_or_succ_or_limit
    [SetStructure V]
    [V ⊧ₘ* 𝗭𝗙]
    [V ⊧ₘ* 𝗭]
    (α : Ordinal V) :
    α.val = ∅
    ∨ (∃ β : Ordinal V, succ β.val = α)
    ∨ ∀ x ∈ α.val, ∃ β ∈ α.val, x ∈ β := by
  by_cases hzero : α.val = ∅
  · simp [hzero]
  · right
    by_cases hsucc : ∃ β : Ordinal V, succ β.val = α.val
    · simp [hsucc]
    · right
      intro x hxα
      have : IsOrdinal x := IsOrdinal.of_mem hxα
      have : IsOrdinal (succ x) := IsOrdinal.succ
      let xo : Ordinal V := IsOrdinal.toOrdinal x
      use succ xo
      rw [(by simp_all [xo] : x = xo.val)] at *
      simp only [mem_succ_self, and_true]
      push_neg at hsucc
      specialize hsucc xo
      have htri := mem_trichotomy (succ xo.val) α.val
      simp only [hsucc, false_or] at htri
      have hαx : α.val ∉ succ xo.val := by
        by_contra
        apply mem_succ_iff.mp at this
        rcases this with hαeqxo | hαmemxo
        · exact mem_irrefl α.val (hαeqxo ▸ hxα)
        · exact mem_asymm hαmemxo hxα
      simpa only [hαx, or_false] using htri

lemma attempt_function_exists_on
    [SetStructure V]
    [V ⊧ₘ* 𝗭𝗙]
    [V ⊧ₘ* 𝗭]
    (F : V → V)
    (hFdef : ℒₛₑₜ-function₁[V] F)
    (α : Ordinal V) :
    ExistsAttemptOfFunctionOn F α := by
  apply transfinite_induction (P := ExistsAttemptOfFunction F) (hP := by definability)
  intro α ih
  have hαzerosucclim : α.val = ∅
      ∨ (∃ β : Ordinal V, succ β.val = α)
      ∨ ∀ x ∈ α.val, ∃ β ∈ α.val, x ∈ β := by
    apply zero_or_succ_or_limit
  rcases hαzerosucclim with hzero | hsucc | hlim
  · -- Zero case
    use ∅
    refine ⟨Ordinal.instIsOrdinalVal, ?_, ?_, ?_⟩
    · exact IsFunction.empty
    · simp only [domain_empty, hzero]
    · intro β hβα
      simp_all only [not_mem_empty]
  · -- Successor case
    rcases hsucc with ⟨β, hβsuccα⟩
    have hβα : β < α := by
      simp_all only [Ordinal.lt_def, ← hβsuccα, succ, mem_insert, mem_irrefl, or_false]
    rcases ih β hβα with ⟨f, hf⟩
    have : IsFunction f := hf.2.1
    simp only [← hβsuccα]
    apply attempt_function_exists_succ_on F β hf.2.2.1 hf
  · -- Limit case
    have hRecDef : ℒₛₑₜ-function₁[V] (attemptOrDefault F) :=
      attemptOrDefault_definable (F := F) hFdef
    rcases replacement_graph_exists_on_of_definableFunction
        (X := α.val) (F := attemptOrDefault F) hRecDef with
      ⟨gfun, hgfunFunc, hgfunDom, hgfunGraph⟩
    let G : V → V := fun β ↦ value gfun β
    have hGdef : ℒₛₑₜ-function₁[V] G := by
      definability
    have hprevG : ∀ β ∈ α.val, IsAttemptGraph F β (G β) := by
      intro β hβα
      letI : IsOrdinal β := IsOrdinal.of_mem hβα
      let βo : Ordinal V := IsOrdinal.toOrdinal β
      have hβlt : βo < α := Ordinal.lt_def.mpr (by simpa [βo] using hβα)
      let fβ : V := attemptOrDefault F β
      have hfβ : IsAttemptGraph F β fβ := by
        exact attemptOrDefault_isAttemptGraph_of_exists F βo (ih βo hβlt)
      have hβpair : ⟨β, fβ⟩ₖ ∈ gfun := (hgfunGraph β hβα fβ).2 rfl
      letI : IsFunction gfun := hgfunFunc
      have hGβeq : G β = fβ := by
        have hβd : β ∈ domain gfun := mem_domain_of_kpair_mem hβpair
        simpa [G] using (IsFunction.value_eq_iff_kpair_mem (f := gfun) (x := β) (y := fβ) hβd).2 hβpair
      simp only [hGβeq]
      exact hfβ
    rcases replacement_collect_predecessor_attempt_functions_on F α G hGdef hprevG with ⟨C, _⟩
    exact attempt_function_exists_sUnion_of_collected_on F α (by assumption) (by aesop) (by assumption)

lemma attempt_function_exists
    [V ⊧ₘ* 𝗭𝗙]
    (F : V → V)
    (hFdef : ℒₛₑₜ-function₁[V] F) :
    ∀ α : V, IsOrdinal α →
      ExistsAttemptOfFunction F α := by
  intro α hα
  let αo : Ordinal V := IsOrdinal.toOrdinal α
  simpa [ExistsAttemptOfFunctionOn, αo] using
    attempt_function_exists_on (F := F) hFdef αo

instance attemptOrDefault_definable_var
    (Φ : V → V → V)
    (hΦdef : ℒₛₑₜ-function₂[V] Φ) :
    ℒₛₑₜ-function₂[V] (fun a β ↦ attemptOrDefault (Φ a) β) := by
  letI : ℒₛₑₜ-function₂[V] Φ := hΦdef
  have hRdef : ℒₛₑₜ-relation₃[V] (fun y a β ↦
      (IsOrdinal β ∧ ExistsAttemptOfFunction (Φ a) β ∧
        IsAttemptGraph (Φ a) β y) ∨
      (¬(IsOrdinal β ∧ ExistsAttemptOfFunction (Φ a) β) ∧
        y = Classical.arbitrary V)) := by
    unfold ExistsAttemptOfFunction IsAttemptGraph
    definability
  have hEq : (fun y a β ↦ y = attemptOrDefault (Φ a) β) =
      (fun y a β ↦ (IsOrdinal β ∧ ExistsAttemptOfFunction (Φ a) β ∧
        IsAttemptGraph (Φ a) β y) ∨
      (¬(IsOrdinal β ∧ ExistsAttemptOfFunction (Φ a) β) ∧
        y = Classical.arbitrary V)) := by
    funext y a β
    exact propext (attemptOrDefault_eq_iff (Φ a) β y)
  show ℒₛₑₜ-relation₃[V] (fun y a β ↦ y = attemptOrDefault (Φ a) β)
  exact hEq ▸ hRdef

def AttemptOrDefaultNotDefaultBranch (F : V → V) (β : V) : Prop :=
  IsAttemptGraph F β (attemptOrDefault F β)

instance attemptOrDefault_notDefaultBranch_definable
    (F : V → V)
    (hFdef : ℒₛₑₜ-function₁[V] F) :
    ℒₛₑₜ-predicate[V] (AttemptOrDefaultNotDefaultBranch F) := by
  letI : ℒₛₑₜ-function₁[V] F := hFdef
  letI : ℒₛₑₜ-function₁[V] (attemptOrDefault F) :=
    attemptOrDefault_definable (F := F) hFdef
  unfold AttemptOrDefaultNotDefaultBranch IsAttemptGraph
  definability

/--
`y` is the transfinite-recursion value at `α` for stage function `F`.
-/
def IsTransfiniteRecursionValueOfFunction (F : V → V) (α y : V) : Prop :=
  ∃ f : V, IsAttemptGraph F α f ∧ Function.Graph F y f

instance isTransfiniteRecursionValueOfFunction_definable
    (F : V → V) (hFdef : ℒₛₑₜ-function₁[V] F) :
    ℒₛₑₜ-relation[V] (fun α y ↦ IsTransfiniteRecursionValueOfFunction F α y) := by
  letI : ℒₛₑₜ-function₁[V] F := hFdef
  unfold IsTransfiniteRecursionValueOfFunction IsAttemptGraph
  definability

/--
If attempt functions exist on ordinal domains, then recursion values are unique.
-/
lemma transfinite_recursion_value_existsUnique_of_function_exists
    (F : V → V)
    -- (hex :
    --   ∀ α : V, IsOrdinal α →
    --     ∃ f : V, IsFunction f ∧ domain f = α ∧
    --       (∀ β ∈ α, ∃ z, ⟨β, z⟩ₖ ∈ f ∧ Function.Graph F z (f ↾ β))) :
    (hf : ∀ α : V, IsOrdinal α → ∃ f : V, IsAttemptGraph F α f) :
    ∀ α : V, IsOrdinal α →
      ∃! y : V, IsTransfiniteRecursionValueOfFunction F α y := by
  intro α hα
  rcases hf α hα with ⟨f, hαord, hfuncf, hdf, hrecf⟩
  rcases functionGraph_functionLike F f with ⟨y, hy, -⟩
  refine ⟨y, ⟨f, ⟨hα, hfuncf, ⟨hdf, hrecf⟩⟩, hy⟩, ?_⟩
  intro y' hy'
  rcases hy' with ⟨g, hg, hyg⟩
  letI : IsOrdinal α := hα
  letI : IsFunction f := hfuncf
  letI : IsFunction g := hg.2.1
  let αo : Ordinal V := IsOrdinal.toOrdinal α
  have hfg : f = g := attempt_function_unique_of_exists_on
    F αo
    (hf := ⟨hαord, hfuncf, hdf, hrecf⟩) (hg := by simpa [αo])
  have : y' = y := by
    have hFuniq := functionGraph_functionLike F g
    exact hFuniq.unique hyg (by simpa [hfg] using hy)
  simpa using this

lemma attemptOrDefault_notDefaultBranch_on
    [V ⊧ₘ* 𝗭𝗙]
    (F : V → V)
    (hFdef : ℒₛₑₜ-function₁[V] F)
    (α : Ordinal V) :
    AttemptOrDefaultNotDefaultBranch F α.val := by
  exact attemptOrDefault_isAttemptGraph_of_exists (F := F) α
    (attempt_function_exists_on (F := F) hFdef α)

/--
Function-form recursion value based on `attemptOrDefault`.
-/
noncomputable def transfiniteRecursionValueFn (F : V → V) (α : V) : V :=
  F (attemptOrDefault F α)

lemma transfiniteRecursionValueFn_eq_apply_attemptOrDefault
    (F : V → V) (α : V) :
    F (attemptOrDefault F α) = transfiniteRecursionValueFn F α := rfl

lemma kpair_mem_attemptOrDefault_iff_eq_transfiniteRecursionValueFn_of_mem
    [V ⊧ₘ* 𝗭𝗙]
    (F : V → V) (hFdef : ℒₛₑₜ-function₁[V] F)
    {α β y : V} (hα : IsOrdinal α) (hβα : β ∈ α) :
    ⟨β, y⟩ₖ ∈ attemptOrDefault F α ↔ y = transfiniteRecursionValueFn F β := by
  have hrf : IsAttemptGraph F α (attemptOrDefault F α) :=
    by
      let αo : Ordinal V := IsOrdinal.toOrdinal α
      simpa [αo] using attemptOrDefault_notDefaultBranch_on (F := F) hFdef αo
  have hβord : IsOrdinal β := IsOrdinal.of_mem hβα
  have hrg : IsAttemptGraph F β (attemptOrDefault F β) :=
    by
      let βo : Ordinal V := IsOrdinal.toOrdinal β
      simpa [βo] using attemptOrDefault_notDefaultBranch_on (F := F) hFdef βo
  letI : IsOrdinal α := hα
  letI : IsOrdinal β := hβord
  letI : IsFunction (attemptOrDefault F α) := hrf.2.1
  letI : IsFunction (attemptOrDefault F β) := hrg.2.1
  have hrecIff : ∀ γ ∈ α, ∀ z,
      ⟨γ, z⟩ₖ ∈ attemptOrDefault F α ↔
        Function.Graph F z ((attemptOrDefault F α) ↾ γ) := by
    let αo : Ordinal V := IsOrdinal.toOrdinal α
    -- simpa [αo] using attempt_iff_of_exists_on (F := F) αo (hrec := hrf.2.2)
    exact hrf.2.2.2
  have hRestrEq : (attemptOrDefault F α) ↾ β = attemptOrDefault F β := by
    let αo : Ordinal V := IsOrdinal.toOrdinal α
    let βo : Ordinal V := IsOrdinal.toOrdinal β
    have hβltα : βo < αo := Ordinal.lt_def.mpr (by simpa [αo, βo] using hβα)
    exact attempt_function_restrict_eq_of_mem_on
      F (α := αo) (β := βo)
      (hβα := hβltα)
      hrf hrg
  constructor
  · intro hβy
    have hyGraph : Function.Graph F y ((attemptOrDefault F α) ↾ β) :=
      (hrecIff β hβα y).1 hβy
    simpa [transfiniteRecursionValueFn, Function.Graph, hRestrEq] using hyGraph
  · intro hy
    have hyGraph : Function.Graph F y ((attemptOrDefault F α) ↾ β) := by
      simpa [transfiniteRecursionValueFn, Function.Graph, hRestrEq] using hy
    exact (hrecIff β hβα y).2 hyGraph

/--
Parameterized function-form recursion value.
-/
noncomputable def transfiniteRecursionValueFnVar (Φ : V → V → V) (a α : V) : V :=
  transfiniteRecursionValueFn (Φ a) α

instance transfiniteRecursionValueFn_definable
    (F : V → V) (hFdef : ℒₛₑₜ-function₁[V] F) :
    ℒₛₑₜ-function₁[V] (transfiniteRecursionValueFn F) := by
  letI : ℒₛₑₜ-function₁[V] F := hFdef
  letI : ℒₛₑₜ-function₁[V] (attemptOrDefault F) :=
    attemptOrDefault_definable (F := F) hFdef
  unfold transfiniteRecursionValueFn
  definability

instance transfiniteRecursionValueFnVar_definable
    (Φ : V → V → V) (hΦdef : ℒₛₑₜ-function₂[V] Φ) :
    ℒₛₑₜ-function₂[V] (transfiniteRecursionValueFnVar Φ) := by
  letI : ℒₛₑₜ-function₂[V] Φ := hΦdef
  have hFdef : ℒₛₑₜ-function₂[V] (fun a α ↦ transfiniteRecursionValueFn (Φ a) α) := by
    letI : ℒₛₑₜ-function₂[V] (fun a α ↦ attemptOrDefault (Φ a) α) :=
      attemptOrDefault_definable_var (Φ := Φ) hΦdef
    definability
  show ℒₛₑₜ-function₂[V] (fun a α ↦ transfiniteRecursionValueFn (Φ a) α)
  exact hFdef

/--
Replacement graph of `β ↦ transfiniteRecursionValueFn F β` on domain `α`.
-/
noncomputable def transfiniteRecursionValueFnReplacementGraph
    [V ⊧ₘ* 𝗭𝗙]
    (F : V → V) (hFdef : ℒₛₑₜ-function₁[V] F) (α : V) : V := by
  classical
  exact Classical.choose <|
    replacement_graph_exists_on_of_definableFunction
      (X := α) (F := transfiniteRecursionValueFn F)
      (transfiniteRecursionValueFn_definable (F := F) hFdef)

lemma transfiniteRecursionValueFnReplacementGraph_spec
    [V ⊧ₘ* 𝗭𝗙]
    (F : V → V) (hFdef : ℒₛₑₜ-function₁[V] F) (α : V) :
    IsFunction (transfiniteRecursionValueFnReplacementGraph F hFdef α) ∧
      domain (transfiniteRecursionValueFnReplacementGraph F hFdef α) = α ∧
      ∀ β ∈ α, ∀ y,
        ⟨β, y⟩ₖ ∈ transfiniteRecursionValueFnReplacementGraph F hFdef α ↔
          y = transfiniteRecursionValueFn F β := by
  simpa [transfiniteRecursionValueFnReplacementGraph] using
    (Classical.choose_spec <|
      replacement_graph_exists_on_of_definableFunction
        (X := α) (F := transfiniteRecursionValueFn F)
        (transfiniteRecursionValueFn_definable (F := F) hFdef))

lemma transfiniteRecursionValueFnReplacementGraph_eq_attemptOrDefault_on
    [V ⊧ₘ* 𝗭𝗙]
    (F : V → V) (hFdef : ℒₛₑₜ-function₁[V] F)
    (α : Ordinal V) :
    transfiniteRecursionValueFnReplacementGraph F hFdef α.val =
      attemptOrDefault F α.val := by
  let g : V := transfiniteRecursionValueFnReplacementGraph F hFdef α.val
  have hg : IsFunction g ∧ domain g = α.val ∧
      ∀ β ∈ α.val, ∀ y, ⟨β, y⟩ₖ ∈ g ↔ y = transfiniteRecursionValueFn F β := by
    simpa [g] using transfiniteRecursionValueFnReplacementGraph_spec (F := F) hFdef α.val
  have hrf : IsAttemptGraph F α.val (attemptOrDefault F α.val) :=
    by
      simpa using attemptOrDefault_notDefaultBranch_on (F := F) hFdef α
  letI : IsFunction g := hg.1
  letI : IsFunction (attemptOrDefault F α.val) := hrf.2.1
  apply subset_antisymm
  · intro p hp
    rcases show ∃ x ∈ domain g, ∃ y ∈ range g, p = ⟨x, y⟩ₖ from by
        simpa [mem_prod_iff] using
          subset_prod_of_mem_function (IsFunction.mem_function g) p hp with
      ⟨x, hxd, y, -, rfl⟩
    have hxα : x ∈ α.val := by simpa [hg.2.1] using hxd
    have hyEq : y = transfiniteRecursionValueFn F x := (hg.2.2 x hxα y).1 hp
    exact
      (kpair_mem_attemptOrDefault_iff_eq_transfiniteRecursionValueFn_of_mem
        (F := F) hFdef α.ordinal hxα).2 hyEq
  · intro p hp
    rcases show ∃ x ∈ domain (attemptOrDefault F α.val), ∃ y ∈ range (attemptOrDefault F α.val),
        p = ⟨x, y⟩ₖ from by
        simpa [mem_prod_iff] using
          subset_prod_of_mem_function (IsFunction.mem_function (attemptOrDefault F α.val)) p hp with
      ⟨x, hxd, y, -, rfl⟩
    have hxα : x ∈ α.val := by simpa [hrf.2.2.1] using hxd
    have hyEq : y = transfiniteRecursionValueFn F x :=
      (kpair_mem_attemptOrDefault_iff_eq_transfiniteRecursionValueFn_of_mem
        (F := F) hFdef α.ordinal hxα).1 hp
    exact (hg.2.2 x hxα y).2 hyEq

lemma transfiniteRecursionValueFnReplacementGraph_eq_attemptOrDefault_of_ordinal
    [V ⊧ₘ* 𝗭𝗙]
    (F : V → V) (hFdef : ℒₛₑₜ-function₁[V] F)
    {α : V} (hα : IsOrdinal α) :
    transfiniteRecursionValueFnReplacementGraph F hFdef α = attemptOrDefault F α := by
  let αo : Ordinal V := IsOrdinal.toOrdinal α
  simpa [αo] using transfiniteRecursionValueFnReplacementGraph_eq_attemptOrDefault_on
    (F := F) hFdef αo

lemma transfiniteRecursionValueFn_eq_apply_replacementGraph_of_ordinal
    [V ⊧ₘ* 𝗭𝗙]
    (F : V → V) (hFdef : ℒₛₑₜ-function₁[V] F)
    {α : V} (hα : IsOrdinal α) :
    F (transfiniteRecursionValueFnReplacementGraph F hFdef α) = transfiniteRecursionValueFn F α := by
  rw [transfiniteRecursionValueFnReplacementGraph_eq_attemptOrDefault_of_ordinal
    (F := F) hFdef hα]
  exact transfiniteRecursionValueFn_eq_apply_attemptOrDefault F α

lemma transfiniteRecursionValueFn_eq_apply_replacementGraph_on
    [V ⊧ₘ* 𝗭𝗙]
    (F : V → V) (hFdef : ℒₛₑₜ-function₁[V] F)
    (α : Ordinal V) :
    F (transfiniteRecursionValueFnReplacementGraph F hFdef α.val) =
      transfiniteRecursionValueFn F α.val := by
  rw [transfiniteRecursionValueFnReplacementGraph_eq_attemptOrDefault_on
    (F := F) hFdef α]
  exact transfiniteRecursionValueFn_eq_apply_attemptOrDefault F α.val

lemma isTransfiniteRecursionValueOfFunction_iff_eq_transfiniteRecursionValueFn
    [V ⊧ₘ* 𝗭𝗙]
    (F : V → V) (hFdef : ℒₛₑₜ-function₁[V] F)
    {α y : V} (hα : IsOrdinal α) :
    IsTransfiniteRecursionValueOfFunction F α y ↔ y = transfiniteRecursionValueFn F α := by
  constructor
  · rintro ⟨f, hf, hyf⟩
    have hrf : IsAttemptGraph F α (attemptOrDefault F α) :=
      by
        let αo : Ordinal V := IsOrdinal.toOrdinal α
        simpa [αo] using attemptOrDefault_notDefaultBranch_on (F := F) hFdef αo
    have hEq : attemptOrDefault F α = f := by
      let αo : Ordinal V := IsOrdinal.toOrdinal α
      exact isAttemptGraph_unique_on (F := F) (α := αo) (by simpa [αo] using hrf) (by simpa [αo] using hf)
    simpa [transfiniteRecursionValueFn, Function.Graph, hEq] using hyf
  · intro hy
    refine ⟨attemptOrDefault F α, ?_, ?_⟩
    · let αo : Ordinal V := IsOrdinal.toOrdinal α
      simpa [αo] using attemptOrDefault_notDefaultBranch_on (F := F) hFdef αo
    · simpa [transfiniteRecursionValueFn, Function.Graph] using hy

lemma transfinite_recursion_value_existsUnique_eq_transfiniteRecursionValueFn_of_definableFunction_on
    [V ⊧ₘ* 𝗭𝗙]
    (F : V → V) (α : Ordinal V) :
    ∃! y : V, y = transfiniteRecursionValueFn F α.val := by
  refine ⟨transfiniteRecursionValueFn F α.val, rfl, ?_⟩
  · intro y hy
    exact hy

/-! ### Base/successor/limit transfinite recursion -/

/--
Specialized transfinite-recursion rule:
- initial stage (`domain r = ∅`): value is `a₀`,
- successor stage (`domain r = succ β`): value is given by `F` from the predecessor value,
- limit stage (neither empty nor successor): value is `⋃ˢ range r`.
-/
def SuccLimitRecursionRule (a₀ : V) (F : V → V) (y r : V) : Prop :=
  (domain r = ∅ ∧ y = a₀) ∨
  (∃ β x, domain r = succ β ∧ ⟨β, x⟩ₖ ∈ r ∧ y = F x) ∨
  (domain r ≠ ∅ ∧ (∀ β, domain r ≠ succ β) ∧ y = ⋃ˢ range r)

instance succLimitRecursionRule_definable_varInit
    (F : V → V) (hFdef : ℒₛₑₜ-function₁[V] F) :
    ℒₛₑₜ-relation₃[V] (fun a₀ r y ↦ SuccLimitRecursionRule a₀ F r y) := by
  letI : ℒₛₑₜ-function₁[V] F := hFdef
  unfold SuccLimitRecursionRule
  definability

instance succLimitRecursionRule_definable
    (a₀ : V) (F : V → V) (hFdef : ℒₛₑₜ-function₁[V] F) :
    ℒₛₑₜ-relation[V] (SuccLimitRecursionRule a₀ F) := by
  letI : ℒₛₑₜ-function₁[V] F := hFdef
  unfold SuccLimitRecursionRule
  definability

instance succLimitRecursionRule_definable_varStep
    (a₀ : V) (Φ : V → V → V) (hΦdef : ℒₛₑₜ-function₂[V] Φ) :
    ℒₛₑₜ-relation₃[V] (fun a r y ↦ SuccLimitRecursionRule a₀ (Φ a) r y) := by
  letI : ℒₛₑₜ-function₂[V] Φ := hΦdef
  unfold SuccLimitRecursionRule
  definability

lemma succLimitRecursionRule_functionLike
    (a₀ : V) (F : V → V) :
    ∀ r : V, IsFunction r → ∃! y : V, SuccLimitRecursionRule a₀ F y r := by
  intro r hr
  by_cases h0 : domain r = ∅
  · refine ⟨a₀, Or.inl ⟨h0, rfl⟩, ?_⟩
    intro y hy
    rcases hy with (hy0 | hyS | hyL)
    · simpa [hy0.1] using hy0.2
    · rcases hyS with ⟨β, x, hdb, -, -⟩
      have : succ β = (∅ : V) := by simpa [h0] using hdb.symm
      have : β ∈ (∅ : V) := by simpa [this] using (show β ∈ succ β by simp)
      exact (not_mem_empty this).elim
    · exact (hyL.1 h0).elim
  · by_cases hs : ∃ β : V, domain r = succ β
    · rcases hs with ⟨β, hdb⟩
      have hβd : β ∈ domain r := by simp [hdb]
      rcases mem_domain_iff.mp hβd with ⟨x, hβx⟩
      refine ⟨F x, Or.inr (Or.inl ⟨β, x, hdb, hβx, rfl⟩), ?_⟩
      intro y' hy'
      rcases hy' with (hy0 | hyS' | hyL)
      · exact (h0 hy0.1).elim
      · rcases hyS' with ⟨β', x', hdb', hβ'x', hx'y'⟩
        have hdbEq : succ β' = succ β := by simpa [hdb] using hdb'.symm
        have hβeq : β' = β := succ_inj hdbEq
        subst hβeq
        have hxEq : x' = x := IsFunction.unique hβ'x' hβx
        subst hxEq
        simp [hx'y']
      · exact (hyL.2.1 β hdb).elim
    · refine ⟨⋃ˢ range r, Or.inr (Or.inr ⟨h0, ?_, rfl⟩), ?_⟩
      · intro β hdb
        exact hs ⟨β, hdb⟩
      · intro y hy
        rcases hy with (hy0 | hyS | hyL)
        · exact (h0 hy0.1).elim
        · rcases hyS with ⟨β, x, hdb, -, -⟩
          exact (hs ⟨β, hdb⟩).elim
        · simpa using hyL.2.2

/--
Function-form specialized successor/limit recursion step.
-/
noncomputable def SuccLimitRecursionStep
    (a₀ : V) (F : V → V) (r : V) : V :=
  by
    classical
    by_cases h0 : domain r = ∅
    · exact a₀
    · by_cases hs : ∃ β : V, domain r = succ β
      · let β : V := Classical.choose hs
        exact F (value r β)
      · exact ⋃ˢ range r

lemma succLimitRecursionStep_spec
    (a₀ : V) (F : V → V)
    {r : V} (hr : IsFunction r) :
    SuccLimitRecursionRule a₀ F (SuccLimitRecursionStep a₀ F r) r := by
  classical
  by_cases h0 : domain r = ∅
  · left
    exact ⟨h0, by simp [SuccLimitRecursionStep, h0]⟩
  · by_cases hs : ∃ β : V, domain r = succ β
    · let ⟨β, hdb⟩ := hs
      have hβd : β ∈ domain r := by simp [hdb]
      rcases mem_domain_iff.mp hβd with ⟨x, hβx⟩
      have hVal : value r β = x := by
        have hβd : β ∈ domain r := mem_domain_of_kpair_mem hβx
        exact (IsFunction.value_eq_iff_kpair_mem (f := r) (x := β) (y := x) hβd).2 hβx
      right; left
      refine ⟨β, x, hdb, hβx, ?_⟩
      have hChoose : Classical.choose hs = β :=
        succ_inj ((Classical.choose_spec hs).symm.trans hdb)
      simp [SuccLimitRecursionStep, h0, hs, hChoose, hVal]
    · right; right
      refine ⟨h0, ?_, by simp [SuccLimitRecursionStep, h0, hs]⟩
      intro β hdb
      exact hs ⟨β, hdb⟩

lemma succLimitRecursionStep_eq_iff
    (a₀ : V) (F : V → V) (r y : V) :
    y = SuccLimitRecursionStep a₀ F r ↔
      (domain r = ∅ ∧ y = a₀) ∨
      (∃ β, domain r = succ β ∧ y = F (value r β)) ∨
      (domain r ≠ ∅ ∧ (∀ β, domain r ≠ succ β) ∧ y = ⋃ˢ range r) := by
  classical
  constructor
  · intro hy
    by_cases h0 : domain r = ∅
    · left
      refine ⟨h0, ?_⟩
      simpa [hy] using (by simp [SuccLimitRecursionStep, h0] : SuccLimitRecursionStep a₀ F r = a₀)
    · right
      by_cases hs : ∃ β : V, domain r = succ β
      · left
        refine ⟨Classical.choose hs, Classical.choose_spec hs, ?_⟩
        simpa [hy] using
          (by
            simp [SuccLimitRecursionStep, h0, hs] :
              SuccLimitRecursionStep a₀ F r = F (value r (Classical.choose hs)))
      · right
        refine ⟨h0, ?_, ?_⟩
        · intro β hdb
          exact hs ⟨β, hdb⟩
        · simpa [hy] using (by simp [SuccLimitRecursionStep, h0, hs] :
            SuccLimitRecursionStep a₀ F r = ⋃ˢ range r)
  · intro hy
    rcases hy with (hy0 | hyS | hyL)
    · simpa [SuccLimitRecursionStep, hy0.1] using hy0.2
    · rcases hyS with ⟨β, hdb, hy⟩
      have hs : ∃ β : V, domain r = succ β := ⟨β, hdb⟩
      have hβ : Classical.choose hs = β := succ_inj ((Classical.choose_spec hs).symm.trans hdb)
      show y = SuccLimitRecursionStep a₀ F r
      have h0 : ¬domain r = ∅ := by
        intro h; have h1 : succ β = (∅ : V) := by rw [← hdb, h]
        exact (not_mem_empty (x := β) (by rw [← h1]; simp)).elim
      simp only [SuccLimitRecursionStep, h0, hs, ↓reduceDIte]
      rw [hβ]
      exact hy
    · rcases hyL with ⟨h0, hs, hy⟩
      have hs' : ¬ ∃ β : V, domain r = succ β := by
        intro hs'
        rcases hs' with ⟨β, hdb⟩
        exact (hs β hdb).elim
      simpa [SuccLimitRecursionStep, h0, hs'] using hy

instance succLimitRecursionStep_definable_varInit
    (F : V → V) (hFdef : ℒₛₑₜ-function₁[V] F) :
    ℒₛₑₜ-function₂[V] (fun a₀ r ↦ SuccLimitRecursionStep a₀ F r) := by
  letI : ℒₛₑₜ-function₁[V] F := hFdef
  have hRdef : ℒₛₑₜ-relation₃[V] (fun y a₀ r ↦
      (domain r = ∅ ∧ y = a₀) ∨
      (∃ β, domain r = succ β ∧ y = F (value r β)) ∨
      (domain r ≠ ∅ ∧ (∀ β, domain r ≠ succ β) ∧ y = ⋃ˢ range r)) := by
    definability
  have hEq : (fun y a₀ r ↦ y = SuccLimitRecursionStep a₀ F r) =
      (fun y a₀ r ↦
        (domain r = ∅ ∧ y = a₀) ∨
        (∃ β, domain r = succ β ∧ y = F (value r β)) ∨
        (domain r ≠ ∅ ∧ (∀ β, domain r ≠ succ β) ∧ y = ⋃ˢ range r)) := by
    funext y a₀ r
    exact propext (succLimitRecursionStep_eq_iff a₀ F r y)
  show ℒₛₑₜ-relation₃[V] (fun y a₀ r ↦ y = SuccLimitRecursionStep a₀ F r)
  exact hEq ▸ hRdef

/--
Definability of `SuccLimitRecursionStep` when `a₀` is fixed and `F` is parameterized
by an external variable: `fun a r ↦ SuccLimitRecursionStep a₀ (F a) r`.
-/
instance succLimitRecursionStep_definable_varF
    (a₀ : V) (F : V → V → V) (hFdef : ℒₛₑₜ-function₂[V] F) :
    ℒₛₑₜ-function₂[V] (fun a r ↦ SuccLimitRecursionStep a₀ (F a) r) := by
  letI : ℒₛₑₜ-function₂[V] F := hFdef
  have hRdef : ℒₛₑₜ-relation₃[V] (fun y a r ↦
      (domain r = ∅ ∧ y = a₀) ∨
      (∃ β, domain r = succ β ∧ y = F a (value r β)) ∨
      (domain r ≠ ∅ ∧ (∀ β, domain r ≠ succ β) ∧ y = ⋃ˢ range r)) := by
    definability
  have hEq : (fun y a r ↦ y = SuccLimitRecursionStep a₀ (F a) r) =
      (fun y a r ↦
        (domain r = ∅ ∧ y = a₀) ∨
        (∃ β, domain r = succ β ∧ y = F a (value r β)) ∨
        (domain r ≠ ∅ ∧ (∀ β, domain r ≠ succ β) ∧ y = ⋃ˢ range r)) := by
    funext y a r
    exact propext (succLimitRecursionStep_eq_iff a₀ (F a) r y)
  show ℒₛₑₜ-relation₃[V] (fun y a r ↦ y = SuccLimitRecursionStep a₀ (F a) r)
  exact hEq ▸ hRdef

instance succLimitRecursionStep_definable
    (a₀ : V) (F : V → V) (hFdef : ℒₛₑₜ-function₁[V] F) :
    ℒₛₑₜ-function₁[V] (SuccLimitRecursionStep a₀ F) := by
  letI : ℒₛₑₜ-function₁[V] F := hFdef
  have hRdef : ℒₛₑₜ-relation[V] (fun y r ↦
      (domain r = ∅ ∧ y = a₀) ∨
      (∃ β, domain r = succ β ∧ y = F (value r β)) ∨
      (domain r ≠ ∅ ∧ (∀ β, domain r ≠ succ β) ∧ y = ⋃ˢ range r)) := by
    definability
  have hEq : (fun y r ↦ y = SuccLimitRecursionStep a₀ F r) =
      (fun y r ↦
        (domain r = ∅ ∧ y = a₀) ∨
        (∃ β, domain r = succ β ∧ y = F (value r β)) ∨
        (domain r ≠ ∅ ∧ (∀ β, domain r ≠ succ β) ∧ y = ⋃ˢ range r)) := by
    funext y r
    exact propext (succLimitRecursionStep_eq_iff a₀ F r y)
  show ℒₛₑₜ-relation[V] (fun y r ↦ y = SuccLimitRecursionStep a₀ F r)
  exact hEq ▸ hRdef

lemma transfinite_recursion_value_existsUnique_of_definableFunction_on
    [V ⊧ₘ* 𝗭𝗙]
    (F : V → V)
    (hFdef : ℒₛₑₜ-function₁[V] F)
    (α : Ordinal V) :
    ∃! y : V, IsTransfiniteRecursionValueOfFunction F α.val y := by
  refine ⟨transfiniteRecursionValueFn F α.val, ?_, ?_⟩
  · exact (isTransfiniteRecursionValueOfFunction_iff_eq_transfiniteRecursionValueFn
      (F := F) hFdef α.ordinal).2 rfl
  · intro y hy
    exact (isTransfiniteRecursionValueOfFunction_iff_eq_transfiniteRecursionValueFn
      (F := F) hFdef α.ordinal).1 hy

lemma transfinite_recursion_value_existsUnique_of_definableFunction
    [V ⊧ₘ* 𝗭𝗙]
    (F : V → V)
    (hFdef : ℒₛₑₜ-function₁[V] F) :
    ∀ α : V, IsOrdinal α →
      ∃! y : V, IsTransfiniteRecursionValueOfFunction F α y := by
  intro α hα
  let αo : Ordinal V := IsOrdinal.toOrdinal α
  simpa [αo] using transfinite_recursion_value_existsUnique_of_definableFunction_on
    (F := F) hFdef αo

lemma transfinite_recursion_value_existsUnique
    [V ⊧ₘ* 𝗭𝗙]
    (F : V → V)
    (hFdef : ℒₛₑₜ-function₁[V] F) :
    ∀ α : V, IsOrdinal α → ∃! y : V, IsTransfiniteRecursionValueOfFunction F α y := by
  exact transfinite_recursion_value_existsUnique_of_definableFunction F hFdef

lemma transfinite_recursion_value_existsUnique_var
    [V ⊧ₘ* 𝗭𝗙]
    (Φ : V → V → V)
    (hΦdef : ℒₛₑₜ-function₂[V] Φ) :
    ∀ a α : V, IsOrdinal α → ∃! y : V, IsTransfiniteRecursionValueOfFunction (Φ a) α y := by
  intro a α hα
  letI : ℒₛₑₜ-function₂[V] Φ := hΦdef
  have hFdef : ℒₛₑₜ-function₁[V] (Φ a) := by
    definability
  simpa using
    transfinite_recursion_value_existsUnique_of_definableFunction (F := Φ a) hFdef α hα

lemma succLimitRecursionStep_successor_transfiniteRecursionValueFn
    [V ⊧ₘ* 𝗭𝗙]
    (a₀ : V) (F : V → V) (hFdef : ℒₛₑₜ-function₁[V] F)
    {α : V} (hα : IsOrdinal α) :
    transfiniteRecursionValueFn (SuccLimitRecursionStep a₀ F) (succ α) =
      F (transfiniteRecursionValueFn (SuccLimitRecursionStep a₀ F) α) := by
  let G : V → V := SuccLimitRecursionStep a₀ F
  have hGdef : ℒₛₑₜ-function₁[V] G := succLimitRecursionStep_definable a₀ F hFdef
  let r : V := transfiniteRecursionValueFnReplacementGraph G hGdef (succ α)
  have hr : IsFunction r ∧ domain r = succ α ∧
      ∀ β ∈ succ α, ∀ y, ⟨β, y⟩ₖ ∈ r ↔ y = transfiniteRecursionValueFn G β := by
    simpa [r] using transfiniteRecursionValueFnReplacementGraph_spec (F := G) hGdef (succ α)
  letI : IsFunction r := hr.1
  have hPair : ⟨α, transfiniteRecursionValueFn G α⟩ₖ ∈ r := by
    exact (hr.2.2 α (by simp) (transfiniteRecursionValueFn G α)).2 rfl
  have hVal : value r α = transfiniteRecursionValueFn G α := by
    have hαd : α ∈ domain r := mem_domain_of_kpair_mem hPair
    exact (IsFunction.value_eq_iff_kpair_mem (f := r) (x := α)
      (y := transfiniteRecursionValueFn G α) hαd).2 hPair
  have h0 : domain r ≠ (∅ : V) := by
    intro h0; rw [hr.2.1] at h0
    exact not_mem_empty (x := α) (by rw [← h0]; simp)
  have hs : ∃ β : V, domain r = succ β := ⟨α, hr.2.1⟩
  have hChoose : Classical.choose hs = α := by
    exact succ_inj ((Classical.choose_spec hs).symm.trans hr.2.1)
  have hStep : G r = F (transfiniteRecursionValueFn G α) := by
    simp [G, SuccLimitRecursionStep, h0, hs, hChoose, hVal]
  have hLHS : transfiniteRecursionValueFn G (succ α) =
      G (transfiniteRecursionValueFnReplacementGraph G hGdef (succ α)) :=
    (transfiniteRecursionValueFn_eq_apply_replacementGraph_of_ordinal
      G hGdef (hα := IsOrdinal.succ (α := α))).symm
  simp only [G] at hLHS ⊢
  rw [hLHS]
  exact hStep

/--
Graph-level strict increase on ordinal indices:
if `β ∈ γ` and `f(β) = x`, `f(γ) = y`, then `x ∈ y`.
-/
def IsStrictIncreasingOrdinalGraph (f : V) : Prop :=
  IsFunction f ∧ ∀ β γ x y, β ∈ γ → ⟨β, x⟩ₖ ∈ f → ⟨γ, y⟩ₖ ∈ f → x ∈ y

/--
If each successor step is strict (`x ∈ F x`) and extends membership (`u ∈ x → u ∈ F x`),
then every recursion function for `SuccLimitRecursionRule a₀ F` is strictly increasing.
-/
lemma succLimitRecursion_strictIncreasing
    (a₀ : V) (F : V → V)
    (hFstrict : ∀ x, x ∈ F x)
    (hFextend : ∀ u x, u ∈ x → u ∈ F x)
    {α f : V}
    (hrec : IsAttempt (SuccLimitRecursionRule a₀ F) α f) :
    IsStrictIncreasingOrdinalGraph f := by
  obtain ⟨hα_ord, hf_func, hf_dom, hf_rec⟩ := hrec
  letI : IsFunction f := hf_func
  refine ⟨hf_func, ?_⟩
  let P : V → Prop := fun γ ↦
    ∀ β ∈ γ, ∀ x y, ⟨β, x⟩ₖ ∈ f → ⟨γ, y⟩ₖ ∈ f → x ∈ y
  have hPall : ∀ γo : Ordinal V, P γo.val := by
    refine transfinite_induction (P := P) (by definability) ?_
    intro γo ih β hβγ x y hβx hγy
    have hγα : γo.val ∈ α := by simpa [hf_dom] using mem_domain_of_kpair_mem hγy
    have hγsubα : γo.val ⊆ α := hα_ord.toIsTransitive.transitive _ hγα
    have hyRule : SuccLimitRecursionRule a₀ F y (f ↾ γo.val) :=
      -- (hf_rec γo.val hγα y).1 hγy
      (hf_rec γo.val hγα y).1 hγy
    rcases hyRule with (h0 | hs | hL)
    · have hdom : domain (f ↾ γo.val) = γo.val := by
        simp [domain_restrict_eq, hf_dom, inter_eq_right_of_subset hγsubα]
      have : γo.val = (∅ : V) := by simpa [hdom] using h0.1
      have : β ∈ (∅ : V) := by simp [this] at hβγ
      exact (not_mem_empty this).elim
    · rcases hs with ⟨δ, u, hdb, hδu, hyFu⟩
      have hdom : domain (f ↾ γo.val) = γo.val := by
        simp [domain_restrict_eq, hf_dom, inter_eq_right_of_subset hγsubα]
      have hγsucc : γo.val = succ δ := by simpa [hdom] using hdb
      have hδu_f : ⟨δ, u⟩ₖ ∈ f := (kpair_mem_restrict_iff.mp hδu).1
      rcases show β = δ ∨ β ∈ δ by simpa [hγsucc, mem_succ_iff] using hβγ with (rfl | hβδ)
      · have hxu : x = u := IsFunction.unique hβx hδu_f
        rw [hxu]
        rw [hyFu]
        exact hFstrict u
      · have hδord : IsOrdinal δ := by
          have hδγ : δ ∈ γo.val := by simp [hγsucc]
          exact IsOrdinal.of_mem hδγ
        have hδγ : IsOrdinal.toOrdinal δ < γo := Ordinal.lt_def.mpr (by simp [hγsucc])
        have hxu : x ∈ u := (ih (IsOrdinal.toOrdinal δ) hδγ) β hβδ x u hβx hδu_f
        rw [hyFu]
        exact hFextend x u hxu
    · have hsuccβsubγ : succ β ⊆ γo.val := by
        intro t ht
        rcases show t = β ∨ t ∈ β by simpa [mem_succ_iff] using ht with (rfl | htβ)
        · exact hβγ
        · exact γo.ordinal.toIsTransitive.transitive _ hβγ _ htβ
      have hsuccβneγ : succ β ≠ γo.val := by
        intro hEq
        have hdom : domain (f ↾ γo.val) = γo.val := by
          simp [domain_restrict_eq, hf_dom, inter_eq_right_of_subset hγsubα]
        exact (hL.2.1 β) (by rw [hdom, hEq])
      haveI : IsOrdinal β := IsOrdinal.of_mem hβγ
      haveI : IsOrdinal (succ β) := IsOrdinal.succ
      have hsuccβγ : succ β ∈ γo.val :=
        IsOrdinal.mem_of_ssubset (α := succ β) (β := γo.val) ⟨hsuccβsubγ, hsuccβneγ⟩
      have hsuccβα : succ β ∈ α := hα_ord.toIsTransitive.transitive _ hγα _ hsuccβγ
      rcases mem_domain_iff.mp (by rw [hf_dom]; exact hsuccβα) with ⟨z, hsuccβz⟩
      have hzRule : SuccLimitRecursionRule a₀ F z (f ↾ (succ β)) :=
        (hf_rec (succ β) hsuccβα z).1 hsuccβz
      have hxz : x ∈ z := by
        have hdom_succβ : domain (f ↾ (succ β)) = succ β := by
          simp [domain_restrict_eq, hf_dom,
            inter_eq_right_of_subset (subset_trans hsuccβsubγ hγsubα)]
        rcases hzRule with (h0' | hs' | hL')
        · have : succ β = (∅ : V) := by simpa [hdom_succβ] using h0'.1
          have : β ∈ (∅ : V) := by simpa [this] using (show β ∈ succ β by simp)
          exact (not_mem_empty this).elim
        · rcases hs' with ⟨δ, u, hdb', hδu, hzFu⟩
          have hdbEq : succ δ = succ β := by simpa [hdom_succβ] using hdb'.symm
          have hδβ : δ = β := succ_inj hdbEq
          rw [hδβ] at hδu
          have hβu_f : ⟨β, u⟩ₖ ∈ f := (kpair_mem_restrict_iff.mp hδu).1
          have hxu : x = u := IsFunction.unique hβx hβu_f
          rw [hxu]
          rw [hzFu]
          exact hFstrict u
        · exact (hL'.2.1 β (by simp [hdom_succβ])).elim
      have hsuccβz_restr : ⟨succ β, z⟩ₖ ∈ f ↾ γo.val :=
        kpair_mem_restrict_iff.mpr ⟨hsuccβz, hsuccβγ⟩
      have hzrange : z ∈ range (f ↾ γo.val) := mem_range_of_kpair_mem hsuccβz_restr
      simpa [hL.2.2] using mem_sUnion_iff.mpr ⟨z, hzrange, hxz⟩
  intro β γ x y hβγ hβx hγy
  have hγord : IsOrdinal γ := by
    have hγα : γ ∈ α := by rw [← hf_dom]; exact mem_domain_of_kpair_mem hγy
    exact IsOrdinal.of_mem hγα
  let γo : Ordinal V := IsOrdinal.toOrdinal γ
  have hPγ : P γ := by simpa [P, γo] using hPall γo
  exact hPγ β hβγ x y hβx hγy

/--
For a strictly-increasing succ/limit recursion graph with ordinal values and stage self-lower-bounds,
every ordinal bound `ξ` (above `a₀`) admits a maximal stage whose value is at most `ξ`,
provided `succ ξ` lies in the recursion domain.

The key construction is the least stage where the value first exceeds `ξ`,
which is shown to be successor (hence not limit).
-/
lemma succLimitRecursion_exists_max_stage_le
    (a₀ : V) (F : V → V)
    {α f : V}
    (hrec : IsAttempt (SuccLimitRecursionRule a₀ F) α f)
    (hstrict : IsStrictIncreasingOrdinalGraph f)
    (hValOrd : ∀ β y, β ∈ α → ⟨β, y⟩ₖ ∈ f → IsOrdinal y)
    (hself : ∀ β y, β ∈ α → ⟨β, y⟩ₖ ∈ f → β ⊆ y)
    {ξ : V} (hξord : IsOrdinal ξ) (ha₀le : a₀ ⊆ ξ) (hsuccξα : succ ξ ∈ α) :
    ∃ δ yδ, δ ∈ α ∧ ⟨δ, yδ⟩ₖ ∈ f ∧ yδ ⊆ ξ ∧
      ∀ γ yγ, γ ∈ α → ⟨γ, yγ⟩ₖ ∈ f → yγ ⊆ ξ → γ ⊆ δ := by
  obtain ⟨hαord, hfFunc, hfDom, hfRec⟩ := hrec
  let Cross : V → Prop := fun β ↦ β ∈ α ∧ ∃ y, ⟨β, y⟩ₖ ∈ f ∧ ξ ∈ y
  have hCrossDef : ℒₛₑₜ-predicate[V] Cross := by
    unfold Cross
    definability
  rcases mem_domain_iff.mp (by rw [hfDom]; exact hsuccξα) with ⟨yS, hSyS⟩
  have hsuccξ_sub_yS : succ ξ ⊆ yS := hself (succ ξ) yS hsuccξα hSyS
  have hξyS : ξ ∈ yS := hsuccξ_sub_yS _ (by simp)
  rcases exists_least_ordinal_of_exists (P := Cross) hCrossDef
      ⟨succ ξ, IsOrdinal.succ (α := ξ), ⟨hsuccξα, yS, hSyS, hξyS⟩⟩ with
    ⟨β₀, hβ₀ord, hβ₀Cross, hleast⟩
  rcases hβ₀Cross with ⟨hβ₀α, y₀, hβ₀y₀, hξy₀⟩
  have hy₀Rule : SuccLimitRecursionRule a₀ F y₀ (f ↾ β₀) := (hfRec β₀ hβ₀α y₀).1 hβ₀y₀
  have hβ₀_sub_α : β₀ ⊆ α := hαord.toIsTransitive.transitive _ hβ₀α
  have hdomβ₀ : domain (f ↾ β₀) = β₀ := by
    calc
      domain (f ↾ β₀) = domain f ∩ β₀ := domain_restrict_eq f β₀
      _ = α ∩ β₀ := by simp [hfDom]
      _ = β₀ := inter_eq_right_of_subset hβ₀_sub_α
  have hβ₀succ : ∃ δ, β₀ = succ δ := by
    rcases hy₀Rule with (h0 | hs | hL)
    · have hβ₀empty : β₀ = (∅ : V) := by simpa [hdomβ₀] using h0.1
      have hξa₀ : ξ ∈ a₀ := by simpa [h0.2] using hξy₀
      have : ξ ∈ ξ := ha₀le _ hξa₀
      exact ((mem_irrefl ξ) this).elim
    · rcases hs with ⟨δ, -, hdb, -, -⟩
      exact ⟨δ, by simpa [hdomβ₀] using hdb⟩
    · rcases hL with ⟨-, -, hyLim⟩
      have hξUnion : ξ ∈ ⋃ˢ range (f ↾ β₀) := by simpa [hyLim] using hξy₀
      rcases mem_sUnion_iff.mp hξUnion with ⟨z, hzRange, hξz⟩
      rcases mem_range_iff.mp hzRange with ⟨γ, hγz_restr⟩
      have hγz : ⟨γ, z⟩ₖ ∈ f := (mem_restrict_iff.mp hγz_restr).1
      have hγβ₀ : γ ∈ β₀ := (kpair_mem_restrict_iff.mp hγz_restr).2
      have hγα : γ ∈ α := hβ₀_sub_α _ hγβ₀
      have hCrossγ : Cross γ := ⟨hγα, z, hγz, hξz⟩
      have hβ₀_sub_γ : β₀ ⊆ γ := hleast γ (IsOrdinal.of_mem hγβ₀) hCrossγ
      have : γ ∈ γ := hβ₀_sub_γ _ hγβ₀
      exact ((mem_irrefl γ) this).elim
  rcases hβ₀succ with ⟨δ, hβ₀eq⟩
  have hδβ₀ : δ ∈ β₀ := by simp [hβ₀eq]
  have hδα : δ ∈ α := hβ₀_sub_α _ hδβ₀
  rcases mem_domain_iff.mp (by rw [hfDom]; exact hδα) with ⟨yδ, hδyδ⟩
  have hδord : IsOrdinal δ := IsOrdinal.of_mem hδβ₀
  have hnotCrossδ : ¬ Cross δ := by
    intro hC
    have hβ₀subδ : β₀ ⊆ δ := hleast δ hδord hC
    have hδβ₀ : δ ∈ β₀ := by simp [hβ₀eq]
    have : δ ∈ δ := hβ₀subδ _ hδβ₀
    exact (mem_irrefl δ) this
  have hξnotyδ : ¬ ξ ∈ yδ := by
    intro hξyδ
    exact hnotCrossδ ⟨hδα, yδ, hδyδ, hξyδ⟩
  have hyδord : IsOrdinal yδ := hValOrd δ yδ hδα hδyδ
  have hyδsubξ : yδ ⊆ ξ := by
    letI : IsOrdinal yδ := hyδord
    letI : IsOrdinal ξ := hξord
    rcases IsOrdinal.mem_trichotomy (α := yδ) (β := ξ) with (hyδξ | hEq | hξyδ)
    · exact (IsOrdinal.subset_iff (α := yδ) (β := ξ)).2 (Or.inr hyδξ)
    · simp [hEq]
    · exact (hξnotyδ hξyδ).elim
  refine ⟨δ, yδ, hδα, hδyδ, hyδsubξ, ?_⟩
  intro γ yγ hγα hγy hγsubξ
  have hγord : IsOrdinal γ := IsOrdinal.of_mem hγα
  letI : IsOrdinal γ := hγord
  letI : IsOrdinal δ := hδord
  by_contra hnot
  have hδsubγ : δ ⊆ γ := by
    rcases IsOrdinal.subset_or_supset (α := γ) (β := δ) with (hγsubδ | hδsubγ)
    · exact (hnot hγsubδ).elim
    · exact hδsubγ
  have hδneqγ : δ ≠ γ := by
    intro hEq
    apply hnot
    simp [hEq]
  have hδγ : δ ∈ γ := (IsOrdinal.ssubset_iff (α := δ) (β := γ)).1 ⟨hδsubγ, hδneqγ⟩
  have hsuccδ_sub_γ : succ δ ⊆ γ := by
    intro t ht
    rcases show t = δ ∨ t ∈ δ by simpa [mem_succ_iff] using ht with (rfl | htδ)
    · exact hδγ
    · exact hγord.toIsTransitive.transitive _ hδγ _ htδ
  have hsuccδ_eq_or_mem : succ δ = γ ∨ succ δ ∈ γ :=
    (IsOrdinal.subset_iff (α := succ δ) (β := γ)).1 hsuccδ_sub_γ
  have hξyγ : ξ ∈ yγ := by
    rcases hsuccδ_eq_or_mem with (hEq | hmem)
    · have hyγeq : yγ = y₀ := by
        have : γ = β₀ := by simpa [hβ₀eq] using hEq.symm
        subst this
        exact IsFunction.unique hγy hβ₀y₀
      simpa [hyγeq] using hξy₀
    · have hyγord : IsOrdinal yγ := hValOrd γ yγ hγα hγy
      have hy₀yγ : y₀ ∈ yγ := hstrict.2 β₀ γ y₀ yγ (by simpa [hβ₀eq] using hmem) hβ₀y₀ hγy
      exact hyγord.toIsTransitive.transitive _ hy₀yγ _ hξy₀
  have : ξ ∈ ξ := hγsubξ _ hξyγ
  exact (mem_irrefl ξ) this

lemma succLimitRecursion_stageValue_isOrdinal
    (a₀ : V) (F : V → V)
    (ha₀ : IsOrdinal a₀)
    (hFord : ∀ x : V, IsOrdinal x → IsOrdinal (F x))
    {α f : V}
    (hrec : IsAttempt (SuccLimitRecursionRule a₀ F) α f) :
    ∀ β y, β ∈ α → ⟨β, y⟩ₖ ∈ f → IsOrdinal y := by
  obtain ⟨hαord, hfFunc, hfDom, hfRec⟩ := hrec
  letI : IsFunction f := hfFunc
  let P : V → Prop := fun β ↦ β ⊆ α → ∀ y, ⟨β, y⟩ₖ ∈ f → IsOrdinal y
  have hPall : ∀ βo : Ordinal V, P βo.val := by
    refine transfinite_induction (P := P) (by definability) ?_
    intro βo ih hβα y hβy
    have hβα' : βo.val ∈ α := by simpa [hfDom] using mem_domain_of_kpair_mem hβy
    have hyRule : SuccLimitRecursionRule a₀ F y (f ↾ βo.val) := (hfRec βo.val hβα' y).1 hβy
    rcases hyRule with (h0 | hs | hL)
    · simpa [h0.2] using ha₀
    · rcases hs with ⟨δ, x, hdb, hδx_restr, hyFx⟩
      have hδβ : δ ∈ βo.val := (kpair_mem_restrict_iff.mp hδx_restr).2
      have hδx : ⟨δ, x⟩ₖ ∈ f := (kpair_mem_restrict_iff.mp hδx_restr).1
      have hδord : IsOrdinal δ := IsOrdinal.of_mem hδβ
      let δo : Ordinal V := IsOrdinal.toOrdinal δ
      have hδlt : δo < βo := Ordinal.lt_def.mpr (by simpa [δo] using hδβ)
      have hδsubβ : δ ⊆ βo.val := βo.ordinal.toIsTransitive.transitive _ hδβ
      have hδsubα : δ ⊆ α := subset_trans hδsubβ hβα
      have hxord : IsOrdinal x := (ih δo hδlt) hδsubα x hδx
      rw [hyFx]
      exact hFord x hxord
    · rw [hL.2.2]
      refine IsOrdinal.sUnion (V := V) ?_
      intro z hzRange
      rcases mem_range_iff.mp hzRange with ⟨δ, hδz_restr⟩
      have hδβ : δ ∈ βo.val := (kpair_mem_restrict_iff.mp hδz_restr).2
      have hδz : ⟨δ, z⟩ₖ ∈ f := (kpair_mem_restrict_iff.mp hδz_restr).1
      have hδord : IsOrdinal δ := IsOrdinal.of_mem hδβ
      let δo : Ordinal V := IsOrdinal.toOrdinal δ
      have hδlt : δo < βo := Ordinal.lt_def.mpr (by simpa [δo] using hδβ)
      have hδsubβ : δ ⊆ βo.val := βo.ordinal.toIsTransitive.transitive _ hδβ
      have hδsubα : δ ⊆ α := subset_trans hδsubβ hβα
      exact (ih δo hδlt) hδsubα z hδz
  intro β y hβα hβy
  have hβord : IsOrdinal β := IsOrdinal.of_mem hβα
  let βo : Ordinal V := IsOrdinal.toOrdinal β
  have hβsubα : β ⊆ α := hαord.toIsTransitive.transitive _ hβα
  exact (hPall βo) (by simpa [βo] using hβsubα) y (by simpa [βo] using hβy)

/--
Function-based strict increase for specialized succ/limit recursion values.
This is the function-level counterpart of `succLimitRecursion_strictIncreasing`,
using `transfiniteRecursionValueFn (SuccLimitRecursionStep a₀ F)`.
-/
lemma succLimitRecursion_strictIncreasing_fn
    [V ⊧ₘ* 𝗭𝗙]
    (a₀ : V) (F : V → V)
    (hFdef : ℒₛₑₜ-function₁[V] F)
    (hFstrict : ∀ x, x ∈ F x)
    (hFextend : ∀ u x, u ∈ x → u ∈ F x)
    {α : V} (hα : IsOrdinal α) :
    ∀ β γ, β ∈ γ → γ ∈ α →
      transfiniteRecursionValueFn (SuccLimitRecursionStep a₀ F) β ∈
        transfiniteRecursionValueFn (SuccLimitRecursionStep a₀ F) γ := by
  let G : V → V := SuccLimitRecursionStep a₀ F
  have hGdef : ℒₛₑₜ-function₁[V] G := succLimitRecursionStep_definable a₀ F hFdef
  let f : V := attemptOrDefault G α
  let αo : Ordinal V := IsOrdinal.toOrdinal α
  have hfRecGraph : IsAttemptGraph G α f :=
    by
      simpa [αo] using attemptOrDefault_notDefaultBranch_on (F := G) hGdef αo
  -- Convert the function-graph recursion for `G` into the specialized rule recursion.
  have hrec : IsAttempt (SuccLimitRecursionRule a₀ F) α f := by
    letI : IsFunction f := hfRecGraph.2.1
    refine ⟨hα, hfRecGraph.2.1, hfRecGraph.2.2.1, ?_⟩
    intro β hβα y
    have hiffG : ⟨β, y⟩ₖ ∈ f ↔ Function.Graph G y (f ↾ β) :=
      hfRecGraph.2.2.2 β hβα y
    constructor
    · intro hβy
      have hyG : Function.Graph G y (f ↾ β) := hiffG.1 hβy
      have hyEq : y = SuccLimitRecursionStep a₀ F (f ↾ β) := by
        simpa [G, Function.Graph] using hyG
      have hstep :
          SuccLimitRecursionRule a₀ F (SuccLimitRecursionStep a₀ F (f ↾ β)) (f ↾ β) :=
        succLimitRecursionStep_spec a₀ F (hr := IsFunction.restrict _ _)
      rwa [← hyEq] at hstep
    · intro hyRule
      have hstep :
          SuccLimitRecursionRule a₀ F (SuccLimitRecursionStep a₀ F (f ↾ β)) (f ↾ β) :=
        succLimitRecursionStep_spec a₀ F (hr := IsFunction.restrict _ _)
      have hyEq :
          y = SuccLimitRecursionStep a₀ F (f ↾ β) :=
        (succLimitRecursionRule_functionLike a₀ F (f ↾ β) (IsFunction.restrict _ _)).unique
          hyRule hstep
      exact hiffG.2 (by simp [G, Function.Graph, hyEq])
  have hStrictGraph : IsStrictIncreasingOrdinalGraph f :=
    succLimitRecursion_strictIncreasing a₀ F hFstrict hFextend hrec
  intro β γ hβγ hγα
  have hβα : β ∈ α := hα.toIsTransitive.transitive _ hγα _ hβγ
  have hβpair : ⟨β, transfiniteRecursionValueFn G β⟩ₖ ∈ f := by
    exact (kpair_mem_attemptOrDefault_iff_eq_transfiniteRecursionValueFn_of_mem
      (F := G) hGdef hα hβα).2 rfl
  have hγpair : ⟨γ, transfiniteRecursionValueFn G γ⟩ₖ ∈ f := by
    exact (kpair_mem_attemptOrDefault_iff_eq_transfiniteRecursionValueFn_of_mem
      (F := G) hGdef hα hγα).2 rfl
  simpa [G] using hStrictGraph.2 β γ
    (transfiniteRecursionValueFn G β) (transfiniteRecursionValueFn G γ) hβγ hβpair hγpair

/--
Function-based stage ordinality for specialized succ/limit recursion values.
This is the function-level counterpart of `succLimitRecursion_stageValue_isOrdinal`.
-/
lemma succLimitRecursion_stageValue_isOrdinal_fn
    [V ⊧ₘ* 𝗭𝗙]
    (a₀ : V) (F : V → V)
    (hFdef : ℒₛₑₜ-function₁[V] F)
    (ha₀ : IsOrdinal a₀)
    (hFord : ∀ x : V, IsOrdinal x → IsOrdinal (F x))
    {α : V} (hα : IsOrdinal α) :
    ∀ β, β ∈ α →
      IsOrdinal (transfiniteRecursionValueFn (SuccLimitRecursionStep a₀ F) β) := by
  let G : V → V := SuccLimitRecursionStep a₀ F
  have hGdef : ℒₛₑₜ-function₁[V] G := succLimitRecursionStep_definable a₀ F hFdef
  let f : V := attemptOrDefault G α
  let αo : Ordinal V := IsOrdinal.toOrdinal α
  have hfRecGraph : IsAttemptGraph G α f :=
    by
      simpa [αo] using attemptOrDefault_notDefaultBranch_on (F := G) hGdef αo
  -- Same conversion bridge as in the strict-increase theorem.
  have hrec : IsAttempt (SuccLimitRecursionRule a₀ F) α f := by
    -- TODO: This looks similar to earlier code, is it compressible?
    letI : IsFunction f := hfRecGraph.2.1
    refine ⟨hα, hfRecGraph.2.1, hfRecGraph.2.2.1, ?_⟩
    intro β hβα y
    have hiffG : ⟨β, y⟩ₖ ∈ f ↔ Function.Graph G y (f ↾ β) :=
      hfRecGraph.2.2.2 β hβα y
    constructor
    · intro hβy
      have hyG : Function.Graph G y (f ↾ β) := hiffG.1 hβy
      have hyEq : y = SuccLimitRecursionStep a₀ F (f ↾ β) := by
        simpa [G, Function.Graph] using hyG
      have hstep :
          SuccLimitRecursionRule a₀ F (SuccLimitRecursionStep a₀ F (f ↾ β)) (f ↾ β) :=
        succLimitRecursionStep_spec a₀ F (hr := IsFunction.restrict _ _)
      rwa [← hyEq] at hstep
    · intro hyRule
      have hstep :
          SuccLimitRecursionRule a₀ F (SuccLimitRecursionStep a₀ F (f ↾ β)) (f ↾ β) :=
        succLimitRecursionStep_spec a₀ F (hr := IsFunction.restrict _ _)
      have hyEq :
          y = SuccLimitRecursionStep a₀ F (f ↾ β) :=
        (succLimitRecursionRule_functionLike a₀ F (f ↾ β) (IsFunction.restrict _ _)).unique
          hyRule hstep
      exact hiffG.2 (by simp [G, Function.Graph, hyEq])
  have hValOrdGraph :
      ∀ β y, β ∈ α → ⟨β, y⟩ₖ ∈ f → IsOrdinal y :=
    succLimitRecursion_stageValue_isOrdinal a₀ F ha₀ hFord hrec
  intro β hβα
  have hβpair : ⟨β, transfiniteRecursionValueFn G β⟩ₖ ∈ f := by
    exact (kpair_mem_attemptOrDefault_iff_eq_transfiniteRecursionValueFn_of_mem
      (F := G) hGdef hα hβα).2 rfl
  simpa [G] using hValOrdGraph β (transfiniteRecursionValueFn G β) hβα hβpair

/--
Function-based maximal-stage theorem for specialized succ/limit recursion values.
This is the function-level counterpart of `succLimitRecursion_exists_max_stage_le`.
-/
lemma succLimitRecursion_exists_max_stage_le_fn
    [V ⊧ₘ* 𝗭𝗙]
    (a₀ : V) (F : V → V)
    (hFdef : ℒₛₑₜ-function₁[V] F)
    {α : V} (hα : IsOrdinal α)
    (hstrict :
      ∀ β γ, β ∈ γ → γ ∈ α →
        transfiniteRecursionValueFn (SuccLimitRecursionStep a₀ F) β ∈
          transfiniteRecursionValueFn (SuccLimitRecursionStep a₀ F) γ)
    (hValOrd :
      ∀ β, β ∈ α →
        IsOrdinal (transfiniteRecursionValueFn (SuccLimitRecursionStep a₀ F) β))
    (hself :
      ∀ β, β ∈ α →
        β ⊆ transfiniteRecursionValueFn (SuccLimitRecursionStep a₀ F) β)
    {ξ : V} (hξord : IsOrdinal ξ) (ha₀le : a₀ ⊆ ξ) (hsuccξα : succ ξ ∈ α) :
    ∃ δ, δ ∈ α ∧
      transfiniteRecursionValueFn (SuccLimitRecursionStep a₀ F) δ ⊆ ξ ∧
      ∀ γ, γ ∈ α →
        transfiniteRecursionValueFn (SuccLimitRecursionStep a₀ F) γ ⊆ ξ → γ ⊆ δ := by
  let G : V → V := SuccLimitRecursionStep a₀ F
  have hGdef : ℒₛₑₜ-function₁[V] G := succLimitRecursionStep_definable a₀ F hFdef
  let f : V := attemptOrDefault G α
  let αo : Ordinal V := IsOrdinal.toOrdinal α
  have hfRecGraph : IsAttemptGraph G α f :=
    by
      simpa [αo] using attemptOrDefault_notDefaultBranch_on (F := G) hGdef αo
  -- Build graph-level hypotheses from function-level hypotheses via pair/value correspondence.
  have hstrictGraph : IsStrictIncreasingOrdinalGraph f := by
    refine ⟨hfRecGraph.2.1, ?_⟩
    intro β γ x y hβγ hβx hγy
    have hγα : γ ∈ α := by simpa [hfRecGraph.2.2.1] using mem_domain_of_kpair_mem hγy
    have hβα : β ∈ α := hα.toIsTransitive.transitive _ hγα _ hβγ
    have hx :
        x = transfiniteRecursionValueFn G β := by
      exact (kpair_mem_attemptOrDefault_iff_eq_transfiniteRecursionValueFn_of_mem
        (F := G) hGdef hα hβα).1 hβx
    have hy :
        y = transfiniteRecursionValueFn G γ := by
      exact (kpair_mem_attemptOrDefault_iff_eq_transfiniteRecursionValueFn_of_mem
        (F := G) hGdef hα hγα).1 hγy
    simpa [G, hx, hy] using hstrict β γ hβγ hγα
  have hValOrdGraph :
      ∀ β y, β ∈ α → ⟨β, y⟩ₖ ∈ f → IsOrdinal y := by
    intro β y hβα hβy
    have hy : y = transfiniteRecursionValueFn G β :=
      (kpair_mem_attemptOrDefault_iff_eq_transfiniteRecursionValueFn_of_mem
        (F := G) hGdef hα hβα).1 hβy
    simpa [G, hy] using hValOrd β hβα
  have hselfGraph :
      ∀ β y, β ∈ α → ⟨β, y⟩ₖ ∈ f → β ⊆ y := by
    intro β y hβα hβy
    have hy : y = transfiniteRecursionValueFn G β :=
      (kpair_mem_attemptOrDefault_iff_eq_transfiniteRecursionValueFn_of_mem
        (F := G) hGdef hα hβα).1 hβy
    simpa [G, hy] using hself β hβα
  -- Convert `IsAttemptGraph` to specialized recursion-function form.
  have hrec : IsAttempt (SuccLimitRecursionRule a₀ F) α f := by
    -- TODO: This looks similar to earlier code, is it compressible?
    letI : IsFunction f := hfRecGraph.2.1
    refine ⟨hα, hfRecGraph.2.1, hfRecGraph.2.2.1, ?_⟩
    intro β hβα y
    have hiffG : ⟨β, y⟩ₖ ∈ f ↔ Function.Graph G y (f ↾ β) :=
      hfRecGraph.2.2.2 β hβα y
    constructor
    · intro hβy
      have hyG : Function.Graph G y (f ↾ β) := hiffG.1 hβy
      have hyEq : y = SuccLimitRecursionStep a₀ F (f ↾ β) := by
        simpa [G, Function.Graph] using hyG
      have hstep :
          SuccLimitRecursionRule a₀ F (SuccLimitRecursionStep a₀ F (f ↾ β)) (f ↾ β) :=
        succLimitRecursionStep_spec a₀ F (hr := IsFunction.restrict _ _)
      rwa [← hyEq] at hstep
    · intro hyRule
      have hstep :
          SuccLimitRecursionRule a₀ F (SuccLimitRecursionStep a₀ F (f ↾ β)) (f ↾ β) :=
        succLimitRecursionStep_spec a₀ F (hr := IsFunction.restrict _ _)
      have hyEq :
          y = SuccLimitRecursionStep a₀ F (f ↾ β) :=
        (succLimitRecursionRule_functionLike a₀ F (f ↾ β) (IsFunction.restrict _ _)).unique
          hyRule hstep
      exact hiffG.2 (by simp [G, Function.Graph, hyEq])
  rcases succLimitRecursion_exists_max_stage_le
      (a₀ := a₀) (F := F) (hrec := hrec) hstrictGraph hValOrdGraph hselfGraph
      hξord ha₀le hsuccξα with
    ⟨δ, yδ, hδα, hδyδ, hyδle, hmax⟩
  have hyδ :
      yδ = transfiniteRecursionValueFn G δ :=
    (kpair_mem_attemptOrDefault_iff_eq_transfiniteRecursionValueFn_of_mem
      (F := G) hGdef hα hδα).1 hδyδ
  refine ⟨δ, hδα, ?_, ?_⟩
  · simpa [G, hyδ] using hyδle
  · intro γ hγα hγle
    have hγpair : ⟨γ, transfiniteRecursionValueFn G γ⟩ₖ ∈ f := by
      exact (kpair_mem_attemptOrDefault_iff_eq_transfiniteRecursionValueFn_of_mem
        (F := G) hGdef hα hγα).2 rfl
    exact hmax γ (transfiniteRecursionValueFn G γ) hγα hγpair (by simpa [G] using hγle)

end LO.FirstOrder.SetTheory.IsOrdinal
