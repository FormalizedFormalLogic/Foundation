module

public import Foundation.FirstOrder.SetTheory.Ordinal

namespace LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V ⊧ₘ* 𝗭]

namespace IsOrdinal

variable {α β γ : V}
/--
`f` is an attempt of length `α` for the relation `φ`, meaning that the domain of `f` is `α`, and for all `β` < `α`, it holds that `f(β) = y` iff `φ (f ↾ β) y`.
The "attempt" terminology is due to Hamkins.
-/
def IsAttempt (φ : V → V → Prop) (α f : V) : Prop :=
  IsOrdinal α ∧ IsFunction f ∧ domain f = α ∧
    ∀ β ∈ α, ∀ y, ⟨β, y⟩ₖ ∈ f ↔ φ (f ↾ β) y

/--
`f` is the attempt graph on domain `β` for the stage map `F`.
-/
def IsAttemptGraph (F : V → V) (β f : V) : Prop :=
  IsFunction f ∧ domain f = β ∧
    ∀ γ ∈ β, ∃ z, ⟨γ, z⟩ₖ ∈ f ∧ Function.Graph F z (f ↾ γ)

/--
Ordinal-packaged form of `IsAttemptGraph`.
-/
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
If `IsAttemptGraph`'s existential property holds, then `IsAttempt`'s biconditional property holds.
-/
lemma attempt_iff_of_exists_on (F : V → V) (α : Ordinal V) {f : V} [IsFunction f]
    (hrec : ∀ β ∈ α.val, ∃ z, ⟨β, z⟩ₖ ∈ f ∧ Function.Graph F z (f ↾ β)) :
    ∀ β ∈ α.val, ∀ y, ⟨β, y⟩ₖ ∈ f ↔ Function.Graph F y (f ↾ β) := by
  intro β hβα y
  rcases hrec β hβα with ⟨z, hβz, hzF⟩
  constructor
  · intro hβy
    have hyz : y = z := IsFunction.unique hβy hβz
    simpa [hyz] using hzF
  · intro hyF
    have huniq := functionGraph_functionLike F (f ↾ β)
    have hyz : y = z := huniq.unique hyF hzF
    simpa [hyz] using hβz

lemma attempt_function_unique_on (F : V → V) (α : Ordinal V) {f g : V} [hf : IsFunction f] [hg : IsFunction g] (hdf : domain f = α.val) (hdg : domain g = α.val)
    (hrecf : ∀ β ∈ α.val, ∀ y, ⟨β, y⟩ₖ ∈ f ↔ Function.Graph F y (f ↾ β))
    (hrecg : ∀ β ∈ α.val, ∀ y, ⟨β, y⟩ₖ ∈ g ↔ Function.Graph F y (g ↾ β)) :
    f = g := by
  have hrestr :
      ∀ β : Ordinal V, β.val ⊆ α.val → f ↾ β.val = g ↾ β.val := by
    refine transfinite_induction (P := fun x ↦ x ⊆ α.val → f ↾ x = g ↾ x) (by definability) ?_
    intro β ihβ hβα
    apply subset_antisymm
    · intro p hp
      rcases mem_restrict_iff.mp hp with ⟨hpf, x, hxβ, y, rfl⟩
      have hxα : x ∈ α.val := hβα x hxβ
      have hfxgx : f ↾ x = g ↾ x := by
        have : IsOrdinal x := IsOrdinal.of_mem hxβ
        let ξ : Ordinal V := IsOrdinal.toOrdinal x
        have hξβ : ξ < β := Ordinal.lt_def.mpr <| by simpa [ξ] using hxβ
        have hξα : ξ.val ⊆ α.val := by
          exact subset_trans (β.ordinal.toIsTransitive.transitive x hxβ) hβα
        simpa [ξ] using ihβ ξ hξβ hξα
      have hφ : Function.Graph F y (g ↾ x) := by
        have : Function.Graph F y (f ↾ x) := (hrecf x hxα y).1 hpf
        simpa [hfxgx] using this
      have hpg : ⟨x, y⟩ₖ ∈ g := (hrecg x hxα y).2 hφ
      exact mem_restrict_iff.mpr ⟨hpg, x, hxβ, y, rfl⟩
    · intro p hp
      rcases mem_restrict_iff.mp hp with ⟨hpg, x, hxβ, y, rfl⟩
      have hxα : x ∈ α.val := hβα x hxβ
      have hfxgx : f ↾ x = g ↾ x := by
        have : IsOrdinal x := IsOrdinal.of_mem hxβ
        let ξ : Ordinal V := IsOrdinal.toOrdinal x
        have hξβ : ξ < β := Ordinal.lt_def.mpr <| by simpa [ξ] using hxβ
        have hξα : ξ.val ⊆ α.val := by
          exact subset_trans (β.ordinal.toIsTransitive.transitive x hxβ) hβα
        simpa [ξ] using ihβ ξ hξβ hξα
      have hφ : Function.Graph F y (f ↾ x) := by
        have : Function.Graph F y (g ↾ x) := (hrecg x hxα y).1 hpg
        simpa [hfxgx] using this
      have hpf : ⟨x, y⟩ₖ ∈ f := (hrecf x hxα y).2 hφ
      exact mem_restrict_iff.mpr ⟨hpf, x, hxβ, y, rfl⟩
  have hαfg : f ↾ α.val = g ↾ α.val := by
    simpa using hrestr α (subset_refl α.val)
  have hfα : f ↾ α.val = f := by
    apply subset_antisymm
    · intro p hp
      exact (mem_restrict_iff.mp hp).1
    · intro p hp
      rcases show ∃ x ∈ domain f, ∃ y ∈ range f, p = ⟨x, y⟩ₖ from by
          simpa [mem_prod_iff] using subset_prod_of_mem_function (IsFunction.mem_function f) p hp with
        ⟨x, hxd, y, -, rfl⟩
      have hxα : x ∈ α.val := by simpa [hdf] using hxd
      exact mem_restrict_iff.mpr ⟨hp, x, hxα, y, rfl⟩
  have hgα : g ↾ α.val = g := by
    apply subset_antisymm
    · intro p hp
      exact (mem_restrict_iff.mp hp).1
    · intro p hp
      rcases show ∃ x ∈ domain g, ∃ y ∈ range g, p = ⟨x, y⟩ₖ from by
          simpa [mem_prod_iff] using subset_prod_of_mem_function (IsFunction.mem_function g) p hp with
        ⟨x, hxd, y, -, rfl⟩
      have hxα : x ∈ α.val := by simpa [hdg] using hxd
      exact mem_restrict_iff.mpr ⟨hp, x, hxα, y, rfl⟩
  calc
    f = f ↾ α.val := hfα.symm
    _ = g ↾ α.val := hαfg
    _ = g := hgα

/--
If two functions with the same ordinal domain satisfy the same recursive clause at each stage,
then they are equal.
-/
lemma attempt_function_unique_of_exists_on
    (F : V → V)
    (α : Ordinal V)
    {f g : V} [hf : IsFunction f] [hg : IsFunction g]
    (hdf : domain f = α.val) (hdg : domain g = α.val)
    (hrecf : ∀ β ∈ α.val, ∃ y : V, ⟨β, y⟩ₖ ∈ f ∧ Function.Graph F y (f ↾ β))
    (hrecg : ∀ β ∈ α.val, ∃ y : V, ⟨β, y⟩ₖ ∈ g ∧ Function.Graph F y (g ↾ β)) :
    f = g := by
  apply attempt_function_unique_on (F := F) (hdf := hdf) (hdg := hdg)
  · exact attempt_iff_of_exists_on F α hrecf
  · exact attempt_iff_of_exists_on F α hrecg

/-- Two recursion-function graphs on the same ordinal domain are equal. -/
lemma isAttemptGraph_unique_on
    (F : V → V) {α : Ordinal V} {f g : V}
    (hf : IsAttemptGraphOn F α f)
    (hg : IsAttemptGraphOn F α g) :
    f = g := by
  letI : IsFunction f := hf.1
  letI : IsFunction g := hg.1
  exact attempt_function_unique_of_exists_on
    (F := F) (α := α) (hdf := hf.2.1) (hdg := hg.2.1) (hrecf := hf.2.2) (hrecg := hg.2.2)

/--
Existence of transfinite-recursion functions on arbitrary ordinal domains,
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
  exact ⟨f, hf, fun g hg ↦ (isAttemptGraph_unique_on (F := F) (α := α) hf hg).symm⟩

instance existsAttemptOfFunction_definable
    (F : V → V)
    (hFdef : ℒₛₑₜ-function₁[V] F) :
    ℒₛₑₜ-predicate[V] (ExistsAttemptOfFunction F) :=
  Language.Definable.exs
    (Language.Definable.retraction
      (isAttemptGraph_definable (F := F) hFdef)
      ![1, 0])

/--
Choose a recursion-function graph at input `β` if one exists.
Otherwise, return an arbitrary value.
-/
noncomputable def recursionFunctionOrDefault
    (F : V → V) (β : V) : V := by
  classical
  by_cases hβ : IsOrdinal β ∧ ExistsAttemptOfFunction F β
  · exact Classical.choose hβ.2
  · exact Classical.arbitrary V

lemma recursionFunctionOrDefault_spec_on
    (F : V → V) (β : Ordinal V)
    (hex : ExistsAttemptOfFunctionOn F β) :
    IsAttemptGraphOn F β (recursionFunctionOrDefault F β.val) := by
  have hcond : IsOrdinal β.val ∧ ExistsAttemptOfFunction F β.val := ⟨β.ordinal, hex⟩
  simp only [recursionFunctionOrDefault, hcond]
  exact Classical.choose_spec hex

lemma recursionFunctionOrDefault_eq_iff
    (F : V → V) (β y : V) :
    y = recursionFunctionOrDefault F β ↔
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
      simpa [βo] using recursionFunctionOrDefault_spec_on (F := F) βo hexo
    · right; exact ⟨hcond, by simp [recursionFunctionOrDefault, hcond]⟩
  · rintro (⟨hord, hex, hrecf⟩ | ⟨hnex, rfl⟩)
    · let βo : Ordinal V := IsOrdinal.toOrdinal β
      have hcond : IsOrdinal β ∧ ExistsAttemptOfFunction F β := ⟨hord, hex⟩
      simp only [recursionFunctionOrDefault, hcond]
      have hspec := Classical.choose_spec hex
      exact isAttemptGraph_unique_on (F := F) (α := βo) (by simpa [βo] using hrecf) (by simpa [βo] using hspec)
    · simp [recursionFunctionOrDefault, hnex]

instance recursionFunctionOrDefault_definable
    (F : V → V)
    (hFdef : ℒₛₑₜ-function₁[V] F) :
    ℒₛₑₜ-function₁[V] (recursionFunctionOrDefault F) := by
  letI : ℒₛₑₜ-function₁[V] F := hFdef
  have hRdef : ℒₛₑₜ-relation[V] (fun y β ↦
      (IsOrdinal β ∧ ExistsAttemptOfFunction F β ∧
        IsAttemptGraph F β y) ∨
      (¬(IsOrdinal β ∧ ExistsAttemptOfFunction F β) ∧
        y = Classical.arbitrary V)) := by
    unfold ExistsAttemptOfFunction IsAttemptGraph
    definability
  have hEq : (fun y β ↦ y = recursionFunctionOrDefault F β) =
      (fun y β ↦ (IsOrdinal β ∧ ExistsAttemptOfFunction F β ∧
        IsAttemptGraph F β y) ∨
      (¬(IsOrdinal β ∧ ExistsAttemptOfFunction F β) ∧
        y = Classical.arbitrary V)) := by
    funext y β
    exact propext (recursionFunctionOrDefault_eq_iff F β y)
  show ℒₛₑₜ-relation[V] (fun y β ↦ y = recursionFunctionOrDefault F β)
  exact hEq ▸ hRdef

instance recursionFunctionOrDefault_definable_var
    (Φ : V → V → V)
    (hΦdef : ℒₛₑₜ-function₂[V] Φ) :
    ℒₛₑₜ-function₂[V] (fun a β ↦ recursionFunctionOrDefault (Φ a) β) := by
  letI : ℒₛₑₜ-function₂[V] Φ := hΦdef
  have hRdef : ℒₛₑₜ-relation₃[V] (fun y a β ↦
      (IsOrdinal β ∧ ExistsAttemptOfFunction (Φ a) β ∧
        IsAttemptGraph (Φ a) β y) ∨
      (¬(IsOrdinal β ∧ ExistsAttemptOfFunction (Φ a) β) ∧
        y = Classical.arbitrary V)) := by
    unfold ExistsAttemptOfFunction IsAttemptGraph
    definability
  have hEq : (fun y a β ↦ y = recursionFunctionOrDefault (Φ a) β) =
      (fun y a β ↦ (IsOrdinal β ∧ ExistsAttemptOfFunction (Φ a) β ∧
        IsAttemptGraph (Φ a) β y) ∨
      (¬(IsOrdinal β ∧ ExistsAttemptOfFunction (Φ a) β) ∧
        y = Classical.arbitrary V)) := by
    funext y a β
    exact propext (recursionFunctionOrDefault_eq_iff (Φ a) β y)
  show ℒₛₑₜ-relation₃[V] (fun y a β ↦ y = recursionFunctionOrDefault (Φ a) β)
  exact hEq ▸ hRdef

def AttemptOrDefaultNotDefaultBranch (F : V → V) (β : V) : Prop :=
  IsAttemptGraph F β (recursionFunctionOrDefault F β)

instance recursionFunctionOrDefault_notDefaultBranch_definable
    (F : V → V)
    (hFdef : ℒₛₑₜ-function₁[V] F) :
    ℒₛₑₜ-predicate[V] (AttemptOrDefaultNotDefaultBranch F) := by
  letI : ℒₛₑₜ-function₁[V] F := hFdef
  letI : ℒₛₑₜ-function₁[V] (recursionFunctionOrDefault F) :=
    recursionFunctionOrDefault_definable (F := F) hFdef
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
If recursion functions exist on ordinal domains, then recursion values are unique.
-/
lemma transfinite_recursion_value_existsUnique_of_function_exists
    (F : V → V)
    (hex :
      ∀ α : V, IsOrdinal α →
        ∃ f : V, IsFunction f ∧ domain f = α ∧
          (∀ β ∈ α, ∃ z, ⟨β, z⟩ₖ ∈ f ∧ Function.Graph F z (f ↾ β))) :
    ∀ α : V, IsOrdinal α →
      ∃! y : V, IsTransfiniteRecursionValueOfFunction F α y := by
  intro α hα
  rcases hex α hα with ⟨f, hff, hdf, hrecf⟩
  rcases functionGraph_functionLike F f with ⟨y, hy, -⟩
  refine ⟨y, ⟨f, ⟨hff, hdf, hrecf⟩, hy⟩, ?_⟩
  intro y' hy'
  rcases hy' with ⟨g, hg, hyg⟩
  letI : IsOrdinal α := hα
  letI : IsFunction f := hff
  letI : IsFunction g := hg.1
  let αo : Ordinal V := IsOrdinal.toOrdinal α
  have hfg : f = g := attempt_function_unique_of_exists_on
    (F := F) αo (hdf := by simpa [αo] using hdf) (hdg := by simpa [αo] using hg.2.1)
    (hrecf := by simpa [αo] using hrecf) (hrecg := by simpa [αo] using hg.2.2)
  have : y' = y := by
    have hφuniq := functionGraph_functionLike F g
    exact hφuniq.unique hyg (by simpa [hfg] using hy)
  simpa using this

/--
Successor step for transfinite-recursion functions in existential-stage form.
-/
lemma transfinite_recursion_function_exists_succ_on
    (F : V → V) (α : Ordinal V) {f : V} [hf : IsFunction f]
    (hdf : domain f = α.val)
    (hrec : ∀ β ∈ α.val, ∃ z, ⟨β, z⟩ₖ ∈ f ∧ Function.Graph F z (f ↾ β)) :
    ∃ g : V, IsFunction g ∧ domain g = succ α.val ∧
      (∀ β ∈ succ α.val, ∃ z, ⟨β, z⟩ₖ ∈ g ∧ Function.Graph F z (g ↾ β)) := by
  rcases functionGraph_functionLike F f with ⟨y, hy, -⟩
  let g : V := insert ⟨α.val, y⟩ₖ f
  have hαnd : α.val ∉ domain f := by simp [hdf]
  have hg : IsFunction g := by
    simpa [g] using (IsFunction.insert f α.val y hαnd)
  refine ⟨g, hg, ?_, ?_⟩
  · simp [g, hdf, succ]
  · intro β hβsucc
    rcases show β = α.val ∨ β ∈ α.val by simpa [mem_succ_iff] using hβsucc with (rfl | hβα)
    · refine ⟨y, ?_, ?_⟩
      · simp [g]
      · have hga : g ↾ α.val = f := by
          calc
            g ↾ α.val = f ↾ α.val := by
              simpa [g] using restrict_insert_kpair_eq_restrict_of_not_mem
                (f := f) (x := α.val) (y := y) (A := α.val) (by simp)
            _ = f := by
              exact IsFunction.restrict_eq_self f α.val (by simp [hdf])
        rw [hga]; exact hy
    · rcases hrec β hβα with ⟨z, hβz, hzφ⟩
      refine ⟨z, by simp [g, hβz], ?_⟩
      have hαβ : α.val ∉ β := mem_asymm hβα
      have hgb : g ↾ β = f ↾ β := by
        simpa [g] using restrict_insert_kpair_eq_restrict_of_not_mem
          (f := f) (x := α.val) (y := y) (A := β) hαβ
      simpa [hgb] using hzφ

/--
Coherence: if `β ∈ α`, a recursion function on `α` restricts to the recursion function on `β`.
-/
lemma transfinite_recursion_function_restrict_eq_of_mem_on
    (F : V → V)
    {α β : Ordinal V} {f g : V} [hf : IsFunction f] [hg : IsFunction g]
    (hβα : β < α)
    (hdf : domain f = α.val) (hdg : domain g = β.val)
    (hrecf : ∀ γ ∈ α.val, ∃ z, ⟨γ, z⟩ₖ ∈ f ∧ Function.Graph F z (f ↾ γ))
    (hrecg : ∀ γ ∈ β.val, ∃ z, ⟨γ, z⟩ₖ ∈ g ∧ Function.Graph F z (g ↾ γ)) :
    f ↾ β.val = g := by
  have hβsubα : β.val ⊆ α.val := α.ordinal.toIsTransitive.transitive _ (Ordinal.lt_def.mp hβα)
  have hdfβ : domain (f ↾ β.val) = β.val := by
    calc
      domain (f ↾ β.val) = domain f ∩ β.val := domain_restrict_eq f β.val
      _ = α.val ∩ β.val := by simp [hdf]
      _ = β.val := inter_eq_right_of_subset hβsubα
  have hrecfβ : ∀ γ ∈ β.val, ∃ z, ⟨γ, z⟩ₖ ∈ (f ↾ β.val) ∧ Function.Graph F z ((f ↾ β.val) ↾ γ) := by
    intro γ hγβ
    have hγα : γ ∈ α.val := hβsubα _ hγβ
    rcases hrecf γ hγα with ⟨z, hγz, hzφ⟩
    have hγsubβ : γ ⊆ β.val := β.ordinal.toIsTransitive.transitive _ hγβ
    refine ⟨z, ?_, ?_⟩
    · exact kpair_mem_restrict_iff.mpr ⟨hγz, hγβ⟩
    · simpa [restrict_restrict_of_subset hγsubβ] using hzφ
  haveI : IsFunction (f ↾ β.val) := IsFunction.restrict f β.val
  have hfg : f ↾ β.val = g := attempt_function_unique_of_exists_on
    (F := F) β (hdf := by simpa using hdfβ) (hdg := by simpa using hdg)
    (hrecf := by simpa using hrecfβ) (hrecg := by simpa using hrecg)
  exact hfg

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

/-- Any two transfinite-recursion functions agree on overlapping inputs. -/
lemma transfinite_recursion_function_coherent_on
    (F : V → V)
    {β γ : Ordinal V} {f g x y₁ y₂ : V}
    [hf : IsFunction f] [hg : IsFunction g]
    (hdf : domain f = β.val) (hdg : domain g = γ.val)
    (hrecf : ∀ ξ ∈ β.val, ∃ z, ⟨ξ, z⟩ₖ ∈ f ∧ Function.Graph F z (f ↾ ξ))
    (hrecg : ∀ ξ ∈ γ.val, ∃ z, ⟨ξ, z⟩ₖ ∈ g ∧ Function.Graph F z (g ↾ ξ))
    (hxy₁ : ⟨x, y₁⟩ₖ ∈ f) (hxy₂ : ⟨x, y₂⟩ₖ ∈ g) :
    y₁ = y₂ := by
  have hxβ : x ∈ β.val := by simpa [hdf] using mem_domain_of_kpair_mem hxy₁
  have hxγ : x ∈ γ.val := by simpa [hdg] using mem_domain_of_kpair_mem hxy₂
  rcases IsOrdinal.mem_trichotomy (α := β.val) (β := γ.val) with (hβγ | hEq | hγβ)
  · have hgb : g ↾ β.val = f := transfinite_recursion_function_restrict_eq_of_mem_on
      (F := F) (α := γ) (β := β)
      (hβα := Ordinal.lt_def.mpr hβγ)
      (hdf := hdg) (hdg := hdf) (hrecf := hrecg) (hrecg := hrecf)
    have hxy₂' : ⟨x, y₂⟩ₖ ∈ g ↾ β.val := kpair_mem_restrict_iff.mpr ⟨hxy₂, hxβ⟩
    have hxy₂f : ⟨x, y₂⟩ₖ ∈ f := by simpa [hgb] using hxy₂'
    exact IsFunction.unique hxy₁ hxy₂f
  · have hfg : f = g := attempt_function_unique_of_exists_on
      (F := F) β
      (hdf := by simpa [hEq] using hdf) (hdg := by simpa [hEq] using hdg)
      (hrecf := hrecf) (hrecg := by simpa [hEq] using hrecg)
    simpa [hfg] using IsFunction.unique hxy₁ (by simpa [hfg] using hxy₂)
  · have hfb : f ↾ γ.val = g := transfinite_recursion_function_restrict_eq_of_mem_on
      (F := F) (α := β) (β := γ)
      (hβα := Ordinal.lt_def.mpr hγβ)
      (hdf := hdf) (hdg := hdg) (hrecf := hrecf) (hrecg := hrecg)
    have hxy₁' : ⟨x, y₁⟩ₖ ∈ f ↾ γ.val := kpair_mem_restrict_iff.mpr ⟨hxy₁, hxγ⟩
    have hxy₁g : ⟨x, y₁⟩ₖ ∈ g := by simpa [hfb] using hxy₁'
    exact (IsFunction.unique hxy₂ hxy₁g).symm

/--
Using replacement, collect all predecessor recursion functions on an ordinal domain.
-/
lemma replacement_collect_predecessor_recursion_functions_on
    [V ⊧ₘ* 𝗭𝗙]
    (F : V → V)
    (α : Ordinal V)
    (G : V → V) (hGdef : ℒₛₑₜ-function₁[V] G)
    (hprev : ∀ β ∈ α.val, IsAttemptGraph F β (G β)) :
    ∃ C : V, ∀ f : V, f ∈ C ↔ ∃ β ∈ α.val, IsAttemptGraph F β f := by
  rcases replacement_exists_on_of_definableFunction (X := α.val) G hGdef with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro f
  constructor
  · intro hfC
    rcases (hC f).1 hfC with ⟨β, hβα, rfl⟩
    exact ⟨β, hβα, hprev β hβα⟩
  · rintro ⟨β, hβα, hrecf⟩
    have hGβ := hprev β hβα
    letI : IsOrdinal β := IsOrdinal.of_mem hβα
    letI : IsFunction f := hrecf.1
    letI : IsFunction (G β) := hGβ.1
    let βo : Ordinal V := IsOrdinal.toOrdinal β
    have hfg : f = G β := attempt_function_unique_of_exists_on
      (F := F) βo
      (hdf := by simpa [βo] using hrecf.2.1) (hdg := by simpa [βo] using hGβ.2.1)
      (hrecf := by simpa [βo] using hrecf.2.2) (hrecg := by simpa [βo] using hGβ.2.2)
    exact (hC f).2 ⟨β, hβα, hfg⟩

/--
Limit-style union construction: from a collected predecessor family `C`,
build a recursion function on `α` by union, assuming every `x ∈ α` lies in some `β ∈ α`
and predecessor recursion functions exist for all ordinals in `α`.
-/
lemma transfinite_recursion_function_exists_sUnion_of_collected_on
    (F : V → V)
    (α : Ordinal V)
    {C : V}
    (hC : ∀ f : V, f ∈ C ↔ ∃ β ∈ α.val, IsAttemptGraph F β f)
    (hprev : ∀ β ∈ α.val, ∃ g : V, IsAttemptGraph F β g)
    (hcover : ∀ x ∈ α.val, ∃ β ∈ α.val, x ∈ β) :
    ∃ f : V, IsFunction f ∧ domain f = α.val ∧
      ∀ γ ∈ α.val, ∃ z, ⟨γ, z⟩ₖ ∈ f ∧ Function.Graph F z (f ↾ γ) := by
  let f : V := ⋃ˢ C
  have hf_isFunction : IsFunction f := by
    refine IsFunction.sUnion_of_coherent
      (hfunc := ?_)
      (hcoh := ?_)
    · intro u huC
      rcases (hC u).1 huC with ⟨β, hβα, hu⟩
      exact hu.1
    · intro u huC v hvC x y₁ y₂ hxyu hxyv
      rcases (hC u).1 huC with ⟨β, hβα, hu⟩
      rcases (hC v).1 hvC with ⟨γ, hγα, hv⟩
      letI : IsOrdinal β := IsOrdinal.of_mem hβα
      letI : IsOrdinal γ := IsOrdinal.of_mem hγα
      letI : IsFunction u := hu.1
      letI : IsFunction v := hv.1
      let βo : Ordinal V := IsOrdinal.toOrdinal β
      let γo : Ordinal V := IsOrdinal.toOrdinal γ
      exact transfinite_recursion_function_coherent_on
        (F := F) (β := βo) (γ := γo)
        (hdf := by simpa [βo] using hu.2.1) (hdg := by simpa [γo] using hv.2.1)
        (hrecf := by simpa [βo] using hu.2.2) (hrecg := by simpa [γo] using hv.2.2)
        hxyu hxyv
  -- Helper: get a member of C with a given domain β ∈ α
  have hC_mem : ∀ β ∈ α.val, ∃ g ∈ C, domain g = β ∧ IsFunction g ∧
      ∀ γ ∈ β, ∃ z, ⟨γ, z⟩ₖ ∈ g ∧ Function.Graph F z (g ↾ γ) := by
    intro β hβα
    rcases hprev β hβα with ⟨g, hg⟩
    exact ⟨g, (hC g).2 ⟨β, hβα, hg⟩, hg.2.1, hg.1, hg.2.2⟩
  have hf_domain : domain f = α.val := by
    apply domain_sUnion_eq_of_domain_subset_and_cover
    · intro u huC
      rcases (hC u).1 huC with ⟨β, hβα, hu⟩
      have hβsubα : β ⊆ α.val := α.ordinal.toIsTransitive.transitive _ hβα
      exact ⟨hu.1, by simpa [hu.2.1] using hβsubα⟩
    · intro x hxα
      rcases hcover x hxα with ⟨β, hβα, hxβ⟩
      rcases hC_mem β hβα with ⟨g, hgC, hgd, -, -⟩
      exact ⟨g, hgC, by simpa [hgd] using hxβ⟩
  refine ⟨f, hf_isFunction, hf_domain, ?_⟩
  intro γ hγα
  -- Pick some u ∈ C whose domain β contains γ
  rcases hcover γ hγα with ⟨β, hβα, hγβ⟩
  rcases hC_mem β hβα with ⟨u, huC, hdu, huf, hrecu⟩
  rcases hrecu γ hγβ with ⟨z, hγzu, hzφu⟩
  refine ⟨z, ?_, ?_⟩
  -- z is in f because u ∈ C and ⟨γ, z⟩ₖ ∈ u
  · exact mem_sUnion_iff.mpr ⟨u, huC, hγzu⟩
  -- `Function.Graph F z (f ↾ γ)`: we know it for `u ↾ γ`, and `f ↾ γ = u ↾ γ` by coherence.
  · have hγsubβ : γ ⊆ β := (IsOrdinal.of_mem hβα).toIsTransitive.transitive _ hγβ
    have hγsubα : γ ⊆ α.val := subset_trans hγsubβ (α.ordinal.toIsTransitive.transitive _ hβα)
    suffices h : f ↾ γ = u ↾ γ by rwa [h]
    letI : IsOrdinal β := IsOrdinal.of_mem hβα
    letI : IsFunction u := huf
    -- u ⊆ f since u ∈ C and f = ⋃ˢ C
    have hu_sub_f : u ⊆ f := fun p hp ↦ mem_sUnion_iff.mpr ⟨u, huC, hp⟩
    apply subset_antisymm
    · -- f ↾ γ ⊆ u ↾ γ: any ⟨a, b⟩ₖ ∈ f with a ∈ γ must be in u
      intro p hp
      rcases mem_restrict_iff.mp hp with ⟨hpf, a, haγ, b, rfl⟩
      have haβ : a ∈ β := hγsubβ _ haγ
      have hadu : a ∈ domain u := by simpa [hdu] using haβ
      rcases mem_domain_iff.mp hadu with ⟨b', hab'u⟩
      have hab'f : ⟨a, b'⟩ₖ ∈ f := hu_sub_f _ hab'u
      have hbb' : b = b' := IsFunction.unique (hf := hf_isFunction) hpf hab'f
      rw [hbb']
      exact kpair_mem_restrict_iff.mpr ⟨hab'u, haγ⟩
    · -- u ↾ γ ⊆ f ↾ γ: immediate from u ⊆ f
      intro p hp
      rcases mem_restrict_iff.mp hp with ⟨hpu, a, haγ, b, rfl⟩
      exact kpair_mem_restrict_iff.mpr ⟨hu_sub_f _ hpu, haγ⟩

lemma transfinite_recursion_function_exists_on
    [V ⊧ₘ* 𝗭𝗙]
    (F : V → V)
    (hFdef : ℒₛₑₜ-function₁[V] F)
    (α : Ordinal V) :
    ExistsAttemptOfFunctionOn F α := by
  let R : V → V → Prop := fun β f ↦ IsAttemptGraph F β f
  have hP : ℒₛₑₜ-predicate[V] (AttemptOrDefaultNotDefaultBranch F) :=
    recursionFunctionOrDefault_notDefaultBranch_definable (F := F) hFdef
  have hrec : ∀ α : Ordinal V, AttemptOrDefaultNotDefaultBranch F α.val := by
    refine transfinite_induction
      (P := AttemptOrDefaultNotDefaultBranch F)
      hP
      ?_
    intro α ih
    have hex : ExistsAttemptOfFunction F α.val := by
      change ∃ f, R α.val f
      by_cases hzero : α.val = ∅
      · refine ⟨∅, (inferInstance : IsFunction (∅ : V)), ?_, ?_⟩
        · simp [hzero]
        · intro β hβα
          have : β ∈ (∅ : V) := by simp [hzero] at hβα
          exact (not_mem_empty this).elim
      · by_cases hsucc : ∃ β : V, α.val = succ β
        · rcases hsucc with ⟨β, hαβ⟩
          have hβα : β ∈ succ β := by simp
          have hβord : IsOrdinal β := IsOrdinal.of_mem (by rw [← hαβ] at hβα; exact hβα)
          let βo : Ordinal V := IsOrdinal.toOrdinal β
          have hβlt : βo < α := by
            exact Ordinal.lt_def.mpr (by simp [βo, hαβ])
          have hβrec : R β (recursionFunctionOrDefault F β) := by
            simpa [R, βo] using ih βo hβlt
          let f : V := recursionFunctionOrDefault F β
          have hff : IsFunction f := hβrec.1
          have hdf : domain f = β := hβrec.2.1
          have hstage : ∀ γ ∈ β, ∃ z, ⟨γ, z⟩ₖ ∈ f ∧ Function.Graph F z (f ↾ γ) := hβrec.2.2
          letI : IsOrdinal β := hβord
          letI : IsFunction f := hff
          rcases transfinite_recursion_function_exists_succ_on
              (F := F) βo (f := f)
              (hdf := by simpa [βo] using hdf)
              (hrec := by simpa [βo] using hstage) with ⟨g, hg⟩
          refine ⟨g, ?_⟩
          rwa [hαβ]
        · have hprev : ∀ β ∈ α.val, ∃ g : V, IsFunction g ∧ domain g = β ∧
              ∀ γ ∈ β, ∃ z, ⟨γ, z⟩ₖ ∈ g ∧ Function.Graph F z (g ↾ γ) := by
            intro β hβα
            letI : IsOrdinal β := IsOrdinal.of_mem hβα
            let βo : Ordinal V := IsOrdinal.toOrdinal β
            have hβlt : βo < α := Ordinal.lt_def.mpr (by simpa [βo] using hβα)
            let g : V := recursionFunctionOrDefault F β
            have hg : R β g := by
              simpa [R, βo, g] using ih βo hβlt
            exact ⟨g, by simpa [R, βo] using hg⟩
          have hcover : ∀ x ∈ α.val, ∃ β ∈ α.val, x ∈ β := by
            intro x hxα
            have hsx_subset : succ x ⊆ α.val := by
              intro t ht
              rcases show t = x ∨ t ∈ x by simpa [mem_succ_iff] using ht with (rfl | htx)
              · exact hxα
              · exact α.ordinal.toIsTransitive.transitive _ hxα _ htx
            have hsx_mem : succ x ∈ α.val := by
              haveI : IsOrdinal x := IsOrdinal.of_mem hxα
              haveI : IsOrdinal (succ x) := IsOrdinal.succ
              rcases IsOrdinal.subset_iff.mp hsx_subset with (hsx_eq | hsx_mem)
              · exact (hsucc ⟨x, hsx_eq.symm⟩).elim
              · exact hsx_mem
            exact ⟨succ x, hsx_mem, by simp⟩
          have hRecDef : ℒₛₑₜ-function₁[V] (recursionFunctionOrDefault F) :=
            recursionFunctionOrDefault_definable (F := F) hFdef
          rcases replacement_graph_exists_on_of_definableFunction
              (X := α.val) (F := recursionFunctionOrDefault F) hRecDef with
            ⟨gfun, hgfunFunc, hgfunDom, hgfunGraph⟩
          let G : V → V := fun β ↦ value gfun β
          have hGdef : ℒₛₑₜ-function₁[V] G := by
            change ℒₛₑₜ-function₁[V] (fun β ↦ value gfun β)
            definability
          have hprevG : ∀ β ∈ α.val, IsFunction (G β) ∧ domain (G β) = β ∧
              ∀ γ ∈ β, ∃ z, ⟨γ, z⟩ₖ ∈ (G β) ∧ Function.Graph F z ((G β) ↾ γ) := by
            intro β hβα
            letI : IsOrdinal β := IsOrdinal.of_mem hβα
            let βo : Ordinal V := IsOrdinal.toOrdinal β
            have hβlt : βo < α := Ordinal.lt_def.mpr (by simpa [βo] using hβα)
            let fβ : V := recursionFunctionOrDefault F β
            have hfβ : IsAttemptGraph F β fβ := by
              simpa [R, βo, fβ] using ih βo hβlt
            have hβpair : ⟨β, fβ⟩ₖ ∈ gfun := (hgfunGraph β hβα fβ).2 rfl
            letI : IsFunction gfun := hgfunFunc
            have hGβeq : G β = fβ := by
              have hβd : β ∈ domain gfun := mem_domain_of_kpair_mem hβpair
              simpa [G] using (IsFunction.value_eq_iff_kpair_mem (f := gfun) (x := β) (y := fβ) hβd).2 hβpair
            simpa [hGβeq] using hfβ
          rcases replacement_collect_predecessor_recursion_functions_on
              (F := F) α (G := G) hGdef hprevG with ⟨C, hC⟩
          rcases transfinite_recursion_function_exists_sUnion_of_collected_on
              (F := F) α (C := C) hC hprev hcover with ⟨f, hf⟩
          exact ⟨f, hf⟩
    exact recursionFunctionOrDefault_spec_on (F := F) α hex
  exact ⟨recursionFunctionOrDefault F α.val, hrec α⟩

lemma transfinite_recursion_function_exists
    [V ⊧ₘ* 𝗭𝗙]
    (F : V → V)
    (hFdef : ℒₛₑₜ-function₁[V] F) :
    ∀ α : V, IsOrdinal α →
      ExistsAttemptOfFunction F α := by
  intro α hα
  let αo : Ordinal V := IsOrdinal.toOrdinal α
  simpa [ExistsAttemptOfFunctionOn, αo] using
    transfinite_recursion_function_exists_on (F := F) hFdef αo

lemma recursionFunctionOrDefault_notDefaultBranch_on
    [V ⊧ₘ* 𝗭𝗙]
    (F : V → V)
    (hFdef : ℒₛₑₜ-function₁[V] F)
    (α : Ordinal V) :
    AttemptOrDefaultNotDefaultBranch F α.val := by
  exact recursionFunctionOrDefault_spec_on (F := F) α
    (transfinite_recursion_function_exists_on (F := F) hFdef α)

/--
Function-form recursion value based on `recursionFunctionOrDefault`.
-/
noncomputable def transfiniteRecursionValueFn (F : V → V) (α : V) : V :=
  F (recursionFunctionOrDefault F α)

lemma transfiniteRecursionValueFn_eq_apply_recursionFunctionOrDefault
    (F : V → V) (α : V) :
    F (recursionFunctionOrDefault F α) = transfiniteRecursionValueFn F α := rfl

lemma kpair_mem_recursionFunctionOrDefault_iff_eq_transfiniteRecursionValueFn_of_mem
    [V ⊧ₘ* 𝗭𝗙]
    (F : V → V) (hFdef : ℒₛₑₜ-function₁[V] F)
    {α β y : V} (hα : IsOrdinal α) (hβα : β ∈ α) :
    ⟨β, y⟩ₖ ∈ recursionFunctionOrDefault F α ↔ y = transfiniteRecursionValueFn F β := by
  have hrf : IsAttemptGraph F α (recursionFunctionOrDefault F α) :=
    by
      let αo : Ordinal V := IsOrdinal.toOrdinal α
      simpa [αo] using recursionFunctionOrDefault_notDefaultBranch_on (F := F) hFdef αo
  have hβord : IsOrdinal β := IsOrdinal.of_mem hβα
  have hrg : IsAttemptGraph F β (recursionFunctionOrDefault F β) :=
    by
      let βo : Ordinal V := IsOrdinal.toOrdinal β
      simpa [βo] using recursionFunctionOrDefault_notDefaultBranch_on (F := F) hFdef βo
  letI : IsOrdinal α := hα
  letI : IsOrdinal β := hβord
  letI : IsFunction (recursionFunctionOrDefault F α) := hrf.1
  letI : IsFunction (recursionFunctionOrDefault F β) := hrg.1
  have hrecIff : ∀ γ ∈ α, ∀ z,
      ⟨γ, z⟩ₖ ∈ recursionFunctionOrDefault F α ↔
        Function.Graph F z ((recursionFunctionOrDefault F α) ↾ γ) := by
    let αo : Ordinal V := IsOrdinal.toOrdinal α
    simpa [αo] using attempt_iff_of_exists_on (F := F) αo (hrec := hrf.2.2)
  have hRestrEq : (recursionFunctionOrDefault F α) ↾ β = recursionFunctionOrDefault F β := by
    let αo : Ordinal V := IsOrdinal.toOrdinal α
    let βo : Ordinal V := IsOrdinal.toOrdinal β
    have hβltα : βo < αo := Ordinal.lt_def.mpr (by simpa [αo, βo] using hβα)
    exact transfinite_recursion_function_restrict_eq_of_mem_on
      (F := F) (α := αo) (β := βo)
      (hβα := hβltα)
      (hdf := by simpa [αo] using hrf.2.1) (hdg := by simpa [βo] using hrg.2.1)
      (hrecf := by simpa [αo] using hrf.2.2) (hrecg := by simpa [βo] using hrg.2.2)
  constructor
  · intro hβy
    have hyGraph : Function.Graph F y ((recursionFunctionOrDefault F α) ↾ β) :=
      (hrecIff β hβα y).1 hβy
    simpa [transfiniteRecursionValueFn, Function.Graph, hRestrEq] using hyGraph
  · intro hy
    have hyGraph : Function.Graph F y ((recursionFunctionOrDefault F α) ↾ β) := by
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
  letI : ℒₛₑₜ-function₁[V] (recursionFunctionOrDefault F) :=
    recursionFunctionOrDefault_definable (F := F) hFdef
  unfold transfiniteRecursionValueFn
  definability

instance transfiniteRecursionValueFnVar_definable
    (Φ : V → V → V) (hΦdef : ℒₛₑₜ-function₂[V] Φ) :
    ℒₛₑₜ-function₂[V] (transfiniteRecursionValueFnVar Φ) := by
  letI : ℒₛₑₜ-function₂[V] Φ := hΦdef
  have hFdef : ℒₛₑₜ-function₂[V] (fun a α ↦ transfiniteRecursionValueFn (Φ a) α) := by
    letI : ℒₛₑₜ-function₂[V] (fun a α ↦ recursionFunctionOrDefault (Φ a) α) :=
      recursionFunctionOrDefault_definable_var (Φ := Φ) hΦdef
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

lemma transfiniteRecursionValueFnReplacementGraph_eq_recursionFunctionOrDefault_on
    [V ⊧ₘ* 𝗭𝗙]
    (F : V → V) (hFdef : ℒₛₑₜ-function₁[V] F)
    (α : Ordinal V) :
    transfiniteRecursionValueFnReplacementGraph F hFdef α.val =
      recursionFunctionOrDefault F α.val := by
  let g : V := transfiniteRecursionValueFnReplacementGraph F hFdef α.val
  have hg : IsFunction g ∧ domain g = α.val ∧
      ∀ β ∈ α.val, ∀ y, ⟨β, y⟩ₖ ∈ g ↔ y = transfiniteRecursionValueFn F β := by
    simpa [g] using transfiniteRecursionValueFnReplacementGraph_spec (F := F) hFdef α.val
  have hrf : IsAttemptGraph F α.val (recursionFunctionOrDefault F α.val) :=
    by
      simpa using recursionFunctionOrDefault_notDefaultBranch_on (F := F) hFdef α
  letI : IsFunction g := hg.1
  letI : IsFunction (recursionFunctionOrDefault F α.val) := hrf.1
  apply subset_antisymm
  · intro p hp
    rcases show ∃ x ∈ domain g, ∃ y ∈ range g, p = ⟨x, y⟩ₖ from by
        simpa [mem_prod_iff] using
          subset_prod_of_mem_function (IsFunction.mem_function g) p hp with
      ⟨x, hxd, y, -, rfl⟩
    have hxα : x ∈ α.val := by simpa [hg.2.1] using hxd
    have hyEq : y = transfiniteRecursionValueFn F x := (hg.2.2 x hxα y).1 hp
    exact
      (kpair_mem_recursionFunctionOrDefault_iff_eq_transfiniteRecursionValueFn_of_mem
        (F := F) hFdef α.ordinal hxα).2 hyEq
  · intro p hp
    rcases show ∃ x ∈ domain (recursionFunctionOrDefault F α.val), ∃ y ∈ range (recursionFunctionOrDefault F α.val),
        p = ⟨x, y⟩ₖ from by
        simpa [mem_prod_iff] using
          subset_prod_of_mem_function (IsFunction.mem_function (recursionFunctionOrDefault F α.val)) p hp with
      ⟨x, hxd, y, -, rfl⟩
    have hxα : x ∈ α.val := by simpa [hrf.2.1] using hxd
    have hyEq : y = transfiniteRecursionValueFn F x :=
      (kpair_mem_recursionFunctionOrDefault_iff_eq_transfiniteRecursionValueFn_of_mem
        (F := F) hFdef α.ordinal hxα).1 hp
    exact (hg.2.2 x hxα y).2 hyEq

lemma transfiniteRecursionValueFnReplacementGraph_eq_recursionFunctionOrDefault_of_ordinal
    [V ⊧ₘ* 𝗭𝗙]
    (F : V → V) (hFdef : ℒₛₑₜ-function₁[V] F)
    {α : V} (hα : IsOrdinal α) :
    transfiniteRecursionValueFnReplacementGraph F hFdef α = recursionFunctionOrDefault F α := by
  let αo : Ordinal V := IsOrdinal.toOrdinal α
  simpa [αo] using transfiniteRecursionValueFnReplacementGraph_eq_recursionFunctionOrDefault_on
    (F := F) hFdef αo

lemma transfiniteRecursionValueFn_eq_apply_replacementGraph_of_ordinal
    [V ⊧ₘ* 𝗭𝗙]
    (F : V → V) (hFdef : ℒₛₑₜ-function₁[V] F)
    {α : V} (hα : IsOrdinal α) :
    F (transfiniteRecursionValueFnReplacementGraph F hFdef α) = transfiniteRecursionValueFn F α := by
  rw [transfiniteRecursionValueFnReplacementGraph_eq_recursionFunctionOrDefault_of_ordinal
    (F := F) hFdef hα]
  exact transfiniteRecursionValueFn_eq_apply_recursionFunctionOrDefault F α

lemma transfiniteRecursionValueFn_eq_apply_replacementGraph_on
    [V ⊧ₘ* 𝗭𝗙]
    (F : V → V) (hFdef : ℒₛₑₜ-function₁[V] F)
    (α : Ordinal V) :
    F (transfiniteRecursionValueFnReplacementGraph F hFdef α.val) =
      transfiniteRecursionValueFn F α.val := by
  rw [transfiniteRecursionValueFnReplacementGraph_eq_recursionFunctionOrDefault_on
    (F := F) hFdef α]
  exact transfiniteRecursionValueFn_eq_apply_recursionFunctionOrDefault F α.val

lemma isTransfiniteRecursionValueOfFunction_iff_eq_transfiniteRecursionValueFn
    [V ⊧ₘ* 𝗭𝗙]
    (F : V → V) (hFdef : ℒₛₑₜ-function₁[V] F)
    {α y : V} (hα : IsOrdinal α) :
    IsTransfiniteRecursionValueOfFunction F α y ↔ y = transfiniteRecursionValueFn F α := by
  constructor
  · rintro ⟨f, hf, hyf⟩
    have hrf : IsAttemptGraph F α (recursionFunctionOrDefault F α) :=
      by
        let αo : Ordinal V := IsOrdinal.toOrdinal α
        simpa [αo] using recursionFunctionOrDefault_notDefaultBranch_on (F := F) hFdef αo
    have hEq : recursionFunctionOrDefault F α = f := by
      let αo : Ordinal V := IsOrdinal.toOrdinal α
      exact isAttemptGraph_unique_on (F := F) (α := αo) (by simpa [αo] using hrf) (by simpa [αo] using hf)
    simpa [transfiniteRecursionValueFn, Function.Graph, hEq] using hyf
  · intro hy
    refine ⟨recursionFunctionOrDefault F α, ?_, ?_⟩
    · let αo : Ordinal V := IsOrdinal.toOrdinal α
      simpa [αo] using recursionFunctionOrDefault_notDefaultBranch_on (F := F) hFdef αo
    · simpa [transfiniteRecursionValueFn, Function.Graph] using hy

lemma transfinite_recursion_value_existsUnique_eq_transfiniteRecursionValueFn_of_definableFunction_on
    [V ⊧ₘ* 𝗭𝗙]
    (F : V → V) (α : Ordinal V) :
    ∃! y : V, y = transfiniteRecursionValueFn F α.val := by
  refine ⟨transfiniteRecursionValueFn F α.val, rfl, ?_⟩
  · intro y hy
    exact hy

/--
Specialized transfinite-recursion rule:
- initial stage (`domain r = ∅`): value is `a₀`,
- successor stage (`domain r = succ β`): value is given by `F` from the predecessor value,
- limit stage (neither empty nor successor): value is `⋃ˢ range r`.
-/
def SuccLimitRecursionRule (a₀ : V) (F : V → V) (r y : V) : Prop :=
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
    ∀ r : V, IsFunction r → ∃! y : V, SuccLimitRecursionRule a₀ F r y := by
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
    SuccLimitRecursionRule a₀ F r (SuccLimitRecursionStep a₀ F r) := by
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
if `β ∈ γ` and `f(β)=x`, `f(γ)=y`, then `x ∈ y`.
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
    have hyRule : SuccLimitRecursionRule a₀ F (f ↾ γo.val) y :=
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
      have hzRule : SuccLimitRecursionRule a₀ F (f ↾ (succ β)) z :=
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
  have hy₀Rule : SuccLimitRecursionRule a₀ F (f ↾ β₀) y₀ := (hfRec β₀ hβ₀α y₀).1 hβ₀y₀
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
    have hyRule : SuccLimitRecursionRule a₀ F (f ↾ βo.val) y := (hfRec βo.val hβα' y).1 hβy
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
  let f : V := recursionFunctionOrDefault G α
  let αo : Ordinal V := IsOrdinal.toOrdinal α
  have hfRecGraph : IsAttemptGraph G α f :=
    by
      simpa [αo] using recursionFunctionOrDefault_notDefaultBranch_on (F := G) hGdef αo
  -- Convert the function-graph recursion for `G` into the specialized rule recursion.
  have hrec : IsAttempt (SuccLimitRecursionRule a₀ F) α f := by
    letI : IsFunction f := hfRecGraph.1
    refine ⟨hα, hfRecGraph.1, hfRecGraph.2.1, ?_⟩
    intro β hβα y
    have hiffG : ⟨β, y⟩ₖ ∈ f ↔ Function.Graph G y (f ↾ β) :=
      attempt_iff_of_exists_on (F := G) (IsOrdinal.toOrdinal α) (hrec := hfRecGraph.2.2) β hβα y
    constructor
    · intro hβy
      have hyG : Function.Graph G y (f ↾ β) := hiffG.1 hβy
      have hyEq : y = SuccLimitRecursionStep a₀ F (f ↾ β) := by
        simpa [G, Function.Graph] using hyG
      have hstep :
          SuccLimitRecursionRule a₀ F (f ↾ β) (SuccLimitRecursionStep a₀ F (f ↾ β)) :=
        succLimitRecursionStep_spec a₀ F (hr := IsFunction.restrict _ _)
      rwa [← hyEq] at hstep
    · intro hyRule
      have hstep :
          SuccLimitRecursionRule a₀ F (f ↾ β) (SuccLimitRecursionStep a₀ F (f ↾ β)) :=
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
    exact (kpair_mem_recursionFunctionOrDefault_iff_eq_transfiniteRecursionValueFn_of_mem
      (F := G) hGdef hα hβα).2 rfl
  have hγpair : ⟨γ, transfiniteRecursionValueFn G γ⟩ₖ ∈ f := by
    exact (kpair_mem_recursionFunctionOrDefault_iff_eq_transfiniteRecursionValueFn_of_mem
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
  let f : V := recursionFunctionOrDefault G α
  let αo : Ordinal V := IsOrdinal.toOrdinal α
  have hfRecGraph : IsAttemptGraph G α f :=
    by
      simpa [αo] using recursionFunctionOrDefault_notDefaultBranch_on (F := G) hGdef αo
  -- Same conversion bridge as in the strict-increase theorem.
  have hrec : IsAttempt (SuccLimitRecursionRule a₀ F) α f := by
    letI : IsFunction f := hfRecGraph.1
    refine ⟨hα, hfRecGraph.1, hfRecGraph.2.1, ?_⟩
    intro β hβα y
    have hiffG : ⟨β, y⟩ₖ ∈ f ↔ Function.Graph G y (f ↾ β) :=
      attempt_iff_of_exists_on (F := G) (IsOrdinal.toOrdinal α) (hrec := hfRecGraph.2.2) β hβα y
    constructor
    · intro hβy
      have hyG : Function.Graph G y (f ↾ β) := hiffG.1 hβy
      have hyEq : y = SuccLimitRecursionStep a₀ F (f ↾ β) := by
        simpa [G, Function.Graph] using hyG
      have hstep :
          SuccLimitRecursionRule a₀ F (f ↾ β) (SuccLimitRecursionStep a₀ F (f ↾ β)) :=
        succLimitRecursionStep_spec a₀ F (hr := IsFunction.restrict _ _)
      rwa [← hyEq] at hstep
    · intro hyRule
      have hstep :
          SuccLimitRecursionRule a₀ F (f ↾ β) (SuccLimitRecursionStep a₀ F (f ↾ β)) :=
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
    exact (kpair_mem_recursionFunctionOrDefault_iff_eq_transfiniteRecursionValueFn_of_mem
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
  let f : V := recursionFunctionOrDefault G α
  let αo : Ordinal V := IsOrdinal.toOrdinal α
  have hfRecGraph : IsAttemptGraph G α f :=
    by
      simpa [αo] using recursionFunctionOrDefault_notDefaultBranch_on (F := G) hGdef αo
  -- Build graph-level hypotheses from function-level hypotheses via pair/value correspondence.
  have hstrictGraph : IsStrictIncreasingOrdinalGraph f := by
    refine ⟨hfRecGraph.1, ?_⟩
    intro β γ x y hβγ hβx hγy
    have hγα : γ ∈ α := by simpa [hfRecGraph.2.1] using mem_domain_of_kpair_mem hγy
    have hβα : β ∈ α := hα.toIsTransitive.transitive _ hγα _ hβγ
    have hx :
        x = transfiniteRecursionValueFn G β := by
      exact (kpair_mem_recursionFunctionOrDefault_iff_eq_transfiniteRecursionValueFn_of_mem
        (F := G) hGdef hα hβα).1 hβx
    have hy :
        y = transfiniteRecursionValueFn G γ := by
      exact (kpair_mem_recursionFunctionOrDefault_iff_eq_transfiniteRecursionValueFn_of_mem
        (F := G) hGdef hα hγα).1 hγy
    simpa [G, hx, hy] using hstrict β γ hβγ hγα
  have hValOrdGraph :
      ∀ β y, β ∈ α → ⟨β, y⟩ₖ ∈ f → IsOrdinal y := by
    intro β y hβα hβy
    have hy : y = transfiniteRecursionValueFn G β :=
      (kpair_mem_recursionFunctionOrDefault_iff_eq_transfiniteRecursionValueFn_of_mem
        (F := G) hGdef hα hβα).1 hβy
    simpa [G, hy] using hValOrd β hβα
  have hselfGraph :
      ∀ β y, β ∈ α → ⟨β, y⟩ₖ ∈ f → β ⊆ y := by
    intro β y hβα hβy
    have hy : y = transfiniteRecursionValueFn G β :=
      (kpair_mem_recursionFunctionOrDefault_iff_eq_transfiniteRecursionValueFn_of_mem
        (F := G) hGdef hα hβα).1 hβy
    simpa [G, hy] using hself β hβα
  -- Convert `IsAttemptGraph` to specialized recursion-function form.
  have hrec : IsAttempt (SuccLimitRecursionRule a₀ F) α f := by
    letI : IsFunction f := hfRecGraph.1
    refine ⟨hα, hfRecGraph.1, hfRecGraph.2.1, ?_⟩
    intro β hβα y
    have hiffG : ⟨β, y⟩ₖ ∈ f ↔ Function.Graph G y (f ↾ β) :=
      attempt_iff_of_exists_on (F := G) (IsOrdinal.toOrdinal α) (hrec := hfRecGraph.2.2) β hβα y
    constructor
    · intro hβy
      have hyG : Function.Graph G y (f ↾ β) := hiffG.1 hβy
      have hyEq : y = SuccLimitRecursionStep a₀ F (f ↾ β) := by
        simpa [G, Function.Graph] using hyG
      have hstep :
          SuccLimitRecursionRule a₀ F (f ↾ β) (SuccLimitRecursionStep a₀ F (f ↾ β)) :=
        succLimitRecursionStep_spec a₀ F (hr := IsFunction.restrict _ _)
      rwa [← hyEq] at hstep
    · intro hyRule
      have hstep :
          SuccLimitRecursionRule a₀ F (f ↾ β) (SuccLimitRecursionStep a₀ F (f ↾ β)) :=
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
    (kpair_mem_recursionFunctionOrDefault_iff_eq_transfiniteRecursionValueFn_of_mem
      (F := G) hGdef hα hδα).1 hδyδ
  refine ⟨δ, hδα, ?_, ?_⟩
  · simpa [G, hyδ] using hyδle
  · intro γ hγα hγle
    have hγpair : ⟨γ, transfiniteRecursionValueFn G γ⟩ₖ ∈ f := by
      exact (kpair_mem_recursionFunctionOrDefault_iff_eq_transfiniteRecursionValueFn_of_mem
        (F := G) hGdef hα hγα).2 rfl
    exact hmax γ (transfiniteRecursionValueFn G γ) hγα hγpair (by simpa [G] using hγle)

/-! ### Ordinal addition (initial/successor stage) -/

section ordinalAddition


/-- Successor-step function used for ordinal addition recursion. -/
noncomputable def OrdinalAddSuccStep (x : V) : V := succ x

instance ordinalAddSuccStep_definable :
    ℒₛₑₜ-function₁[V] OrdinalAddSuccStep := by
  show ℒₛₑₜ-function₁[V] (fun x ↦ succ x)
  definability

lemma ordinalAddSuccStep_strict :
    ∀ x : V, x ∈ OrdinalAddSuccStep x := by
  intro x
  simp [OrdinalAddSuccStep]

lemma ordinalAddSuccStep_extend :
    ∀ u x : V, u ∈ x → u ∈ OrdinalAddSuccStep x := by
  intro u x hux
  simp [OrdinalAddSuccStep, mem_succ_iff, hux]

variable [V ⊧ₘ* 𝗭𝗙]

/--
Set-level ordinal-addition value obtained by specialized transfinite recursion:
base value `a`, successor step `succ`, and limit step `⋃ˢ range`.
-/
noncomputable def ordinalAddValue (a b : V) : V :=
  transfiniteRecursionValueFn (SuccLimitRecursionStep a OrdinalAddSuccStep) b

lemma ordinalAddValue_isRecursionValueOfFunction (a b : V) (hb : IsOrdinal b) :
    IsTransfiniteRecursionValueOfFunction
      (SuccLimitRecursionStep a OrdinalAddSuccStep) b (ordinalAddValue a b) := by
  exact (isTransfiniteRecursionValueOfFunction_iff_eq_transfiniteRecursionValueFn
    (F := SuccLimitRecursionStep a OrdinalAddSuccStep)
    (succLimitRecursionStep_definable a OrdinalAddSuccStep ordinalAddSuccStep_definable)
    hb).2 rfl

omit [V ⊧ₘ* 𝗭𝗙] in
private instance ordinalAddSuccStep_definable_step :
    ℒₛₑₜ-function₁[V] (SuccLimitRecursionStep a OrdinalAddSuccStep) :=
  succLimitRecursionStep_definable a OrdinalAddSuccStep ordinalAddSuccStep_definable

omit [V ⊧ₘ* 𝗭𝗙] in
instance ordinalAddValue_definable (a : V) :
    ℒₛₑₜ-function₁[V] (ordinalAddValue a) :=
  transfiniteRecursionValueFn_definable
    (F := SuccLimitRecursionStep a OrdinalAddSuccStep)
    (succLimitRecursionStep_definable a OrdinalAddSuccStep ordinalAddSuccStep_definable)

omit [V ⊧ₘ* 𝗭𝗙] in
instance ordinalAddValue_definable_varInit :
    ℒₛₑₜ-function₂[V] (fun a b ↦ ordinalAddValue a b) :=
  transfiniteRecursionValueFnVar_definable
    (Φ := fun a ↦ SuccLimitRecursionStep a OrdinalAddSuccStep)
    (succLimitRecursionStep_definable_varInit
      (F := OrdinalAddSuccStep) ordinalAddSuccStep_definable)

omit [V ⊧ₘ* 𝗭𝗙] in
instance ordinalAddValue_definable_left (b : V) :
    ℒₛₑₜ-function₁[V] (fun a ↦ ordinalAddValue a b) := by
  letI : ℒₛₑₜ-function₂[V] (fun a b ↦ ordinalAddValue a b) :=
    ordinalAddValue_definable_varInit
  definability

@[simp] lemma ordinalAddValue_zero (a : V) :
    ordinalAddValue a 0 = a := by
  simp only [ordinalAddValue]
  -- transfiniteRecursionValueFn (SuccLimitRecursionStep a OrdinalAddSuccStep) 0
  -- = (SuccLimitRecursionStep a OrdinalAddSuccStep) (recursionFunctionOrDefault ... 0)
  -- The recursion function at 0 is ∅, so SuccLimitRecursionStep on ∅ = a₀ = a.
  unfold transfiniteRecursionValueFn
  have hSdef : ℒₛₑₜ-function₁[V] (SuccLimitRecursionStep a OrdinalAddSuccStep) :=
    ordinalAddSuccStep_definable_step
  let αo : Ordinal V := IsOrdinal.toOrdinal (0 : V)
  have hrf : IsAttemptGraph (SuccLimitRecursionStep a OrdinalAddSuccStep) 0
      (recursionFunctionOrDefault (SuccLimitRecursionStep a OrdinalAddSuccStep) 0) :=
    by
      simpa [αo] using recursionFunctionOrDefault_notDefaultBranch_on
        (F := SuccLimitRecursionStep a OrdinalAddSuccStep) hSdef αo
  have hdom : domain (recursionFunctionOrDefault
      (SuccLimitRecursionStep a OrdinalAddSuccStep) 0) = (0 : V) := hrf.2.1
  have hdomEmpty : domain (recursionFunctionOrDefault
      (SuccLimitRecursionStep a OrdinalAddSuccStep) 0) = (∅ : V) := by
    simpa [zero_def] using hdom
  simp [SuccLimitRecursionStep, hdomEmpty]

@[simp] lemma ordinalAddValue_succ (a β : V) (hβ : IsOrdinal β) :
    ordinalAddValue a (succ β) =
      succ (ordinalAddValue a β) := by
  simp only [ordinalAddValue]
  exact succLimitRecursionStep_successor_transfiniteRecursionValueFn
    a OrdinalAddSuccStep ordinalAddSuccStep_definable hβ

lemma ordinalAddValue_isOrdinal
    (a β : V) (ha : IsOrdinal a) (hβ : IsOrdinal β) :
    IsOrdinal (ordinalAddValue a β) := by
  simp only [ordinalAddValue]
  exact succLimitRecursion_stageValue_isOrdinal_fn
    a OrdinalAddSuccStep ordinalAddSuccStep_definable ha
    (fun x hx ↦ by simp only [OrdinalAddSuccStep]; exact IsOrdinal.succ (α := x))
    (IsOrdinal.succ (α := β)) β (by simp)

lemma ordinalAddValue_strictIncreasing_right
    (a : V) {β γ : V} (hγ : IsOrdinal γ) (hβγ : β ∈ γ) :
    ordinalAddValue a β ∈ ordinalAddValue a γ := by
  simp only [ordinalAddValue]
  exact succLimitRecursion_strictIncreasing_fn
    a OrdinalAddSuccStep ordinalAddSuccStep_definable
    ordinalAddSuccStep_strict ordinalAddSuccStep_extend
    (IsOrdinal.succ (α := γ)) β γ hβγ (by simp)

lemma ordinalAddValue_subset_right_of_initOrdinal
    (a β γ : V) (ha : IsOrdinal a) (hβ : IsOrdinal β) (hγ : IsOrdinal γ)
    (hβγ : β ⊆ γ) :
    ordinalAddValue a β ⊆ ordinalAddValue a γ := by
  by_cases hEq : β = γ
  · subst hEq
    simp
  · have hβmemγ : β ∈ γ := (IsOrdinal.ssubset_iff (α := β) (β := γ)).1 ⟨hβγ, hEq⟩
    have hlt : ordinalAddValue a β ∈ ordinalAddValue a γ :=
      ordinalAddValue_strictIncreasing_right (a := a) (hγ := hγ) (hβγ := hβmemγ)
    have hγord' : IsOrdinal (ordinalAddValue a γ) :=
      ordinalAddValue_isOrdinal a γ ha hγ
    exact hγord'.toIsTransitive.transitive _ hlt

omit [V ⊧ₘ* 𝗭𝗙] in
lemma ordinalAddRecursion_exists_max_right_le
    (a : V) {α f : V}
    (hrec : IsAttempt (SuccLimitRecursionRule a OrdinalAddSuccStep) α f)
    (hstrict : IsStrictIncreasingOrdinalGraph f)
    (hValOrd : ∀ β y, β ∈ α → ⟨β, y⟩ₖ ∈ f → IsOrdinal y)
    (hself : ∀ β y, β ∈ α → ⟨β, y⟩ₖ ∈ f → β ⊆ y)
    {γ : V} (hγ : IsOrdinal γ) (hale : a ⊆ γ) (hsuccγα : succ γ ∈ α) :
    ∃ δ yδ, δ ∈ α ∧ ⟨δ, yδ⟩ₖ ∈ f ∧ yδ ⊆ γ ∧
      ∀ η yη, η ∈ α → ⟨η, yη⟩ₖ ∈ f → yη ⊆ γ → η ⊆ δ :=
  succLimitRecursion_exists_max_stage_le
    (a₀ := a) (F := OrdinalAddSuccStep)
    hrec hstrict hValOrd hself hγ hale hsuccγα

omit [V ⊧ₘ* 𝗭𝗙] in
lemma ordinalAddRecursion_exists_max_right_eq
    (a : V) {γ α f : V}
    (hαeq : α = succ (succ γ))
    (hrec : IsAttempt (SuccLimitRecursionRule a OrdinalAddSuccStep) α f)
    (hstrict : IsStrictIncreasingOrdinalGraph f)
    (hValOrd : ∀ β y, β ∈ α → ⟨β, y⟩ₖ ∈ f → IsOrdinal y)
    (hself : ∀ β y, β ∈ α → ⟨β, y⟩ₖ ∈ f → β ⊆ y)
    (hγ : IsOrdinal γ) (hale : a ⊆ γ) :
    ∃ δ yδ, δ ∈ α ∧ ⟨δ, yδ⟩ₖ ∈ f ∧ yδ = γ ∧
      ∀ η yη, η ∈ α → ⟨η, yη⟩ₖ ∈ f → yη ⊆ γ → η ⊆ δ := by
  have hsuccγα : succ γ ∈ α := by rw [hαeq]; simp
  rcases ordinalAddRecursion_exists_max_right_le
      (a := a) (hrec := hrec) (hstrict := hstrict) (hValOrd := hValOrd) (hself := hself)
      (hγ := hγ) (hale := hale) (hsuccγα := hsuccγα) with
    ⟨δ, yδ, hδα, hδyδ, hyδle, hmax⟩
  obtain ⟨hαord, hfFunc, hfDom, hfRec⟩ := hrec
  letI : IsFunction f := hfFunc
  have hδord : IsOrdinal δ := IsOrdinal.of_mem hδα
  have hyδord : IsOrdinal yδ := hValOrd δ yδ hδα hδyδ
  by_cases hEq : yδ = γ
  · refine ⟨δ, yδ, hδα, hδyδ, hEq, hmax⟩
  · have hyδγ : yδ ∈ γ := by
      letI : IsOrdinal yδ := hyδord
      letI : IsOrdinal γ := hγ
      rcases IsOrdinal.subset_iff (α := yδ) (β := γ) |>.1 hyδle with (h | h)
      · exact (hEq h).elim
      · exact h
    have hδ_sub_yδ : δ ⊆ yδ := hself δ yδ hδα hδyδ
    have hδ_sub_γ : δ ⊆ γ := subset_trans hδ_sub_yδ (hγ.toIsTransitive.transitive _ hyδγ)
    have hδγ : δ ∈ γ := by
      letI : IsOrdinal δ := hδord
      letI : IsOrdinal γ := hγ
      rcases IsOrdinal.subset_iff (α := δ) (β := γ) |>.1 hδ_sub_γ with (hEq' | hMem')
      · rw [hEq'] at hδ_sub_yδ
        exact ((mem_irrefl yδ) (hδ_sub_yδ _ hyδγ)).elim
      · exact hMem'
    have hsuccδ_sub_γ : succ δ ⊆ γ := by
      intro t ht
      rcases show t = δ ∨ t ∈ δ by simpa [mem_succ_iff] using ht with (rfl | htδ)
      · exact hδγ
      · exact hγ.toIsTransitive.transitive _ hδγ _ htδ
    have hsuccδ_in_succγ : succ δ ∈ succ γ := by
      simp only [mem_succ_iff]
      haveI : IsOrdinal (succ δ) := IsOrdinal.succ
      haveI : IsOrdinal γ := hγ
      exact (IsOrdinal.subset_iff (α := succ δ) (β := γ)).1 hsuccδ_sub_γ
    have hsuccδ_in_α : succ δ ∈ α :=
      hαord.toIsTransitive.transitive _ hsuccγα _ hsuccδ_in_succγ
    have hsucc_sub_α : succ δ ⊆ α := hαord.toIsTransitive.transitive _ hsuccδ_in_α
    rcases mem_domain_iff.mp (by rw [hfDom]; exact hsuccδ_in_α) with ⟨yS, hsuccδyS⟩
    have hyS_rule : SuccLimitRecursionRule a OrdinalAddSuccStep (f ↾ (succ δ)) yS :=
      (hfRec (succ δ) hsuccδ_in_α yS).1 hsuccδyS
    have hdom_succδ : domain (f ↾ (succ δ)) = succ δ := by
      simp [domain_restrict_eq, hfDom, inter_eq_right_of_subset hsucc_sub_α]
    have hyS_eq : yS = succ yδ := by
      rcases hyS_rule with (h0 | hs | hL)
      · have : succ δ = (∅ : V) := by simpa [hdom_succδ] using h0.1
        have : δ ∈ (∅ : V) := by simpa [this] using (show δ ∈ succ δ by simp)
        exact (not_mem_empty this).elim
      · rcases hs with ⟨δ', x, hdb, hδ'x, hxyS⟩
        have hdb' : succ δ' = succ δ := by simpa [hdom_succδ] using hdb.symm
        have : δ' = δ := succ_inj hdb'
        rw [this] at hδ'x
        have hδx : ⟨δ, x⟩ₖ ∈ f := (kpair_mem_restrict_iff.mp hδ'x).1
        have : x = yδ := IsFunction.unique hδx hδyδ
        subst this
        have h := hxyS
        simp only [OrdinalAddSuccStep] at h
        exact h
      · exact (hL.2.1 δ (by simp [hdom_succδ])).elim
    have hySle : yS ⊆ γ := by
      have hsuccyδ_sub_γ : succ yδ ⊆ γ := by
        intro t ht
        rcases show t = yδ ∨ t ∈ yδ by simpa [mem_succ_iff] using ht with (rfl | htyδ)
        · exact hyδγ
        · exact hγ.toIsTransitive.transitive _ hyδγ _ htyδ
      simpa [hyS_eq] using hsuccyδ_sub_γ
    have hsuccδ_sub_δ : succ δ ⊆ δ := hmax (succ δ) yS hsuccδ_in_α hsuccδyS hySle
    have : δ ∈ δ := hsuccδ_sub_δ _ (by simp)
    exact ((mem_irrefl δ) this).elim

lemma ordinalAddValue_exists_right_eq_of_subset
    (a γ : V) (ha : IsOrdinal a) (hγ : IsOrdinal γ) (hale : a ⊆ γ) :
    ∃ δ : Ordinal V, ordinalAddValue a δ.val = γ := by
  let G : V → V := SuccLimitRecursionStep a OrdinalAddSuccStep
  have hGdef : ℒₛₑₜ-function₁[V] G := succLimitRecursionStep_definable a OrdinalAddSuccStep ordinalAddSuccStep_definable
  let f : V := recursionFunctionOrDefault G (succ (succ γ))
  let α := succ (succ γ)
  have hα : IsOrdinal α := IsOrdinal.succ
  let αo : Ordinal V := IsOrdinal.toOrdinal α
  have hfRecGraph : IsAttemptGraph G α f :=
    by
      simpa [αo] using recursionFunctionOrDefault_notDefaultBranch_on (F := G) hGdef αo
  -- Convert the function-graph recursion for `G` into the specialized rule recursion.
  have hrec : IsAttempt (SuccLimitRecursionRule a OrdinalAddSuccStep) α f := by
    letI : IsFunction f := hfRecGraph.1
    refine ⟨hα, hfRecGraph.1, hfRecGraph.2.1, ?_⟩
    intro β hβα y
    have hiffG : ⟨β, y⟩ₖ ∈ f ↔ Function.Graph G y (f ↾ β) :=
      attempt_iff_of_exists_on (F := G) (IsOrdinal.toOrdinal α) (hrec := hfRecGraph.2.2) β hβα y
    constructor
    · intro hβy
      have hyG : Function.Graph G y (f ↾ β) := hiffG.1 hβy
      have hyEq : y = SuccLimitRecursionStep a OrdinalAddSuccStep (f ↾ β) := by
        simpa [G, Function.Graph] using hyG
      have hstep :
          SuccLimitRecursionRule a OrdinalAddSuccStep (f ↾ β) (SuccLimitRecursionStep a OrdinalAddSuccStep (f ↾ β)) :=
        succLimitRecursionStep_spec a OrdinalAddSuccStep (hr := IsFunction.restrict _ _)
      rwa [← hyEq] at hstep
    · intro hyRule
      have hstep :
          SuccLimitRecursionRule a OrdinalAddSuccStep (f ↾ β) (SuccLimitRecursionStep a OrdinalAddSuccStep (f ↾ β)) :=
        succLimitRecursionStep_spec a OrdinalAddSuccStep (hr := IsFunction.restrict _ _)
      have hyEq :
          y = SuccLimitRecursionStep a OrdinalAddSuccStep (f ↾ β) :=
        (succLimitRecursionRule_functionLike a OrdinalAddSuccStep (f ↾ β) (IsFunction.restrict _ _)).unique
          hyRule hstep
      exact hiffG.2 (by simp [G, Function.Graph, hyEq])
  have hstrict : IsStrictIncreasingOrdinalGraph f :=
    succLimitRecursion_strictIncreasing
      (a₀ := a) (F := OrdinalAddSuccStep)
      ordinalAddSuccStep_strict ordinalAddSuccStep_extend hrec
  have hValOrd : ∀ β y, β ∈ α → ⟨β, y⟩ₖ ∈ f → IsOrdinal y :=
    succLimitRecursion_stageValue_isOrdinal
      (a₀ := a) (F := OrdinalAddSuccStep) ha
      (by
        intro x hx
        simp only [OrdinalAddSuccStep]
        exact IsOrdinal.succ (α := x))
      hrec
  have hAddDef : ℒₛₑₜ-function₁[V] (ordinalAddValue a) := ordinalAddValue_definable a
  have hstrictRel :
      ∀ β γ yβ yγ : V, IsOrdinal β → IsOrdinal γ → β ∈ γ →
        (yβ = ordinalAddValue a β) → (yγ = ordinalAddValue a γ) → yβ ∈ yγ := by
    intro β' γ' yβ yγ hβ hγ' hβγ hyβ hyγ
    rcases hyβ with rfl
    rcases hyγ with rfl
    exact ordinalAddValue_strictIncreasing_right (a := a) (hγ := hγ') (hβγ := hβγ)
  have hself : ∀ β y, β ∈ α → ⟨β, y⟩ₖ ∈ f → β ⊆ y := by
    intro β y hβα hβy
    have hβord : IsOrdinal β := IsOrdinal.of_mem hβα
    have hyord : IsOrdinal y := hValOrd β y hβα hβy
    have hy : y = transfiniteRecursionValueFn G β :=
      (kpair_mem_recursionFunctionOrDefault_iff_eq_transfiniteRecursionValueFn_of_mem
        (F := G) hGdef hα hβα).1 hβy
    have hyeqAdd : y = ordinalAddValue a β := by simpa [G, ordinalAddValue] using hy
    have hnot : ¬ y ∈ β := by
      intro hyβ
      have hnotAdd := strictIncreasing_function_no_value_lt_self
        (F := ordinalAddValue a)
        (hFdef := hAddDef)
        (hFstrict := by
          intro β' γ' hβ' hγ' hβγ'
          exact ordinalAddValue_strictIncreasing_right (a := a) (hγ := hγ') (hβγ := hβγ'))
        β hβord
      exact hnotAdd (by simpa [hyeqAdd] using hyβ)
    letI : IsOrdinal β := hβord
    letI : IsOrdinal y := hyord
    rcases IsOrdinal.mem_trichotomy (α := y) (β := β) with (hyβ | hEq | hβy)
    · exact (hnot hyβ).elim
    · simp [hEq]
    · exact (IsOrdinal.subset_iff (α := β) (β := y)).2 (Or.inr hβy)
  rcases ordinalAddRecursion_exists_max_right_eq
      (a := a) (γ := γ) (α := α) (f := f) (hαeq := rfl)
      (hrec := hrec) (hstrict := hstrict) (hValOrd := hValOrd) (hself := hself)
      (hγ := hγ) (hale := hale) with
    ⟨δ, yδ, hδα, hδyδ, hyδeqγ, hmax⟩
  have hδord : IsOrdinal δ := IsOrdinal.of_mem hδα
  have hyδ : yδ = transfiniteRecursionValueFn G δ :=
    (kpair_mem_recursionFunctionOrDefault_iff_eq_transfiniteRecursionValueFn_of_mem
      (F := G) hGdef hα hδα).1 hδyδ
  have hyδeqAdd : yδ = ordinalAddValue a δ := by simpa [G, ordinalAddValue] using hyδ
  refine ⟨⟨δ, hδord⟩, ?_⟩
  simpa [hyδeqγ] using hyδeqAdd.symm

end ordinalAddition

end IsOrdinal

namespace Ordinal

variable [V ⊧ₘ* 𝗭𝗙]

/--
Current set-level value of ordinal addition.
This is the first stage of ordinal arithmetic development: base and successor equations.
-/
noncomputable def addValue (α β : Ordinal V) : V :=
  IsOrdinal.ordinalAddValue α.val β.val

@[simp] lemma addValue_bot (α : Ordinal V) : addValue α ⊥ = α.val := by
  simp only [addValue, bot_val_eq]
  exact IsOrdinal.ordinalAddValue_zero (a := α.val)

@[simp] lemma addValue_succ (α β : Ordinal V) :
    addValue α β.succ = succ (addValue α β) := by
  simp [addValue, succ_val]

lemma addValue_strictIncreasing_right (α : Ordinal V) {β γ : Ordinal V} (hβγ : β < γ) :
    addValue α β ∈ addValue α γ := by
  simpa [addValue] using
    IsOrdinal.ordinalAddValue_strictIncreasing_right (a := α.val) (hγ := γ.ordinal) (hβγ := hβγ)

end Ordinal

namespace IsOrdinal

variable {α β γ : V}

/-! ### Ordinal multiplication (initial/successor stage) -/

section ordinalMultiplication

variable [V ⊧ₘ* 𝗭𝗙]

/-- Successor-step function for right-multiplication by `a`: maps `x` to `x + a`. -/
noncomputable def OrdinalMulSuccStep (a x : V) : V := ordinalAddValue x a

omit [V ⊧ₘ* 𝗭𝗙] in
instance ordinalMulSuccStep_definable (a : V) :
    ℒₛₑₜ-function₁[V] (OrdinalMulSuccStep a) := by
  show ℒₛₑₜ-function₁[V] (fun x ↦ ordinalAddValue x a)
  exact ordinalAddValue_definable_left a

omit [V ⊧ₘ* 𝗭𝗙] in
instance ordinalMulSuccStep_definable_varLeft :
    ℒₛₑₜ-function₂[V] (fun a x ↦ OrdinalMulSuccStep a x) := by
  show ℒₛₑₜ-function₂[V] (fun a x ↦ ordinalAddValue x a)
  letI : ℒₛₑₜ-function₂[V] (fun a b ↦ ordinalAddValue a b) :=
    ordinalAddValue_definable_varInit
  definability

lemma ordinalMulSuccStep_strict_of_pos
    (a : V) (ha : IsOrdinal a) (ha0 : (0 : V) ∈ a) :
    ∀ x : V, x ∈ OrdinalMulSuccStep a x := by
  intro x
  simp only [OrdinalMulSuccStep]
  have hxlt : ordinalAddValue x 0 ∈ ordinalAddValue x a :=
    ordinalAddValue_strictIncreasing_right (a := x) (hγ := ha) (hβγ := ha0)
  simpa using hxlt

omit [V ⊧ₘ* 𝗭𝗙] in
lemma ordinalMulSuccStep_extend_of_pos
    (a : V)
    (hStepExtend : ∀ u x : V, u ∈ x → u ∈ OrdinalMulSuccStep a x) :
    ∀ u x : V, u ∈ x → u ∈ OrdinalMulSuccStep a x := hStepExtend

/--
Set-level ordinal multiplication value (as recursion in the right argument):
base value `0`, successor step `x ↦ x + a`, and limit step `⋃ˢ range`.
-/
noncomputable def ordinalMulValue (a b : V) : V :=
  transfiniteRecursionValueFn (SuccLimitRecursionStep (0 : V) (OrdinalMulSuccStep a)) b

omit [V ⊧ₘ* 𝗭𝗙] in
private instance ordinalMulSuccStep_definable_step (a : V) :
    ℒₛₑₜ-function₁[V] (SuccLimitRecursionStep (0 : V) (OrdinalMulSuccStep a)) :=
  succLimitRecursionStep_definable (0 : V) (OrdinalMulSuccStep a) (ordinalMulSuccStep_definable a)

omit [V ⊧ₘ* 𝗭𝗙] in
instance ordinalMulValue_definable (a : V) :
    ℒₛₑₜ-function₁[V] (ordinalMulValue a) :=
  transfiniteRecursionValueFn_definable
    (F := SuccLimitRecursionStep (0 : V) (OrdinalMulSuccStep a))
    (ordinalMulSuccStep_definable_step a)

omit [V ⊧ₘ* 𝗭𝗙] in
instance ordinalMulValue_definable_varInit :
    ℒₛₑₜ-function₂[V] (fun a b ↦ ordinalMulValue a b) :=
  transfiniteRecursionValueFnVar_definable
    (Φ := fun a ↦ SuccLimitRecursionStep (0 : V) (OrdinalMulSuccStep a))
    (succLimitRecursionStep_definable_varF (0 : V)
      (F := fun a ↦ OrdinalMulSuccStep a) ordinalMulSuccStep_definable_varLeft)

@[simp] lemma ordinalMulValue_zero (a : V) :
    ordinalMulValue a 0 = (0 : V) := by
  simp only [ordinalMulValue]
  unfold transfiniteRecursionValueFn
  have hSdef : ℒₛₑₜ-function₁[V] (SuccLimitRecursionStep (0 : V) (OrdinalMulSuccStep a)) :=
    ordinalMulSuccStep_definable_step a
  let αo : Ordinal V := IsOrdinal.toOrdinal (0 : V)
  have hrf : IsAttemptGraph (SuccLimitRecursionStep (0 : V) (OrdinalMulSuccStep a)) 0
      (recursionFunctionOrDefault (SuccLimitRecursionStep (0 : V) (OrdinalMulSuccStep a)) 0) :=
    by
      simpa [αo] using recursionFunctionOrDefault_notDefaultBranch_on
        (F := SuccLimitRecursionStep (0 : V) (OrdinalMulSuccStep a)) hSdef αo
  have hdom : domain (recursionFunctionOrDefault
      (SuccLimitRecursionStep (0 : V) (OrdinalMulSuccStep a)) 0) = (0 : V) := hrf.2.1
  have hdomEmpty : domain (recursionFunctionOrDefault
      (SuccLimitRecursionStep (0 : V) (OrdinalMulSuccStep a)) 0) = (∅ : V) := by
    simpa [zero_def] using hdom
  simp [SuccLimitRecursionStep, hdomEmpty]

@[simp] lemma ordinalMulValue_succ (a β : V) (hβ : IsOrdinal β) :
    ordinalMulValue a (succ β) =
      ordinalAddValue (ordinalMulValue a β) a := by
  simp only [ordinalMulValue]
  exact succLimitRecursionStep_successor_transfiniteRecursionValueFn
    (0 : V) (OrdinalMulSuccStep a) (ordinalMulSuccStep_definable a) hβ

lemma ordinalMulValue_strictIncreasing_right_of_left_pos
    (a : V) (ha : IsOrdinal a) (ha0 : (0 : V) ∈ a)
    (hStepExtend : ∀ u x : V, u ∈ x → u ∈ OrdinalMulSuccStep a x)
    {β γ : V} (hγ : IsOrdinal γ) (hβγ : β ∈ γ) :
    ordinalMulValue a β ∈ ordinalMulValue a γ := by
  simp only [ordinalMulValue]
  exact succLimitRecursion_strictIncreasing_fn
    (0 : V) (OrdinalMulSuccStep a) (ordinalMulSuccStep_definable a)
    (ordinalMulSuccStep_strict_of_pos a ha ha0) hStepExtend
    (IsOrdinal.succ (α := γ)) β γ hβγ (by simp)

lemma ordinalMulValue_exists_right_mul_add_eq_of_pos
    (a γ : V) (ha : IsOrdinal a) (ha0 : (0 : V) ∈ a) (hγ : IsOrdinal γ)
    (hStepExtend : ∀ u x : V, u ∈ x → u ∈ OrdinalMulSuccStep a x) :
    ∃ δ ρ : Ordinal V,
      ordinalAddValue (ordinalMulValue a δ.val) ρ.val = γ ∧
      ρ.val ∈ a := by
  let G : V → V := SuccLimitRecursionStep (0 : V) (OrdinalMulSuccStep a)
  have hGdef : ℒₛₑₜ-function₁[V] G := ordinalMulSuccStep_definable_step a
  let f : V := recursionFunctionOrDefault G (succ (succ γ))
  let α := succ (succ γ)
  have hα : IsOrdinal α := IsOrdinal.succ
  let αo : Ordinal V := IsOrdinal.toOrdinal α
  have hfRecGraph : IsAttemptGraph G α f :=
    by
      simpa [αo] using recursionFunctionOrDefault_notDefaultBranch_on (F := G) hGdef αo
  have hrec : IsAttempt
      (SuccLimitRecursionRule (0 : V) (OrdinalMulSuccStep a)) α f := by
    letI : IsFunction f := hfRecGraph.1
    refine ⟨hα, hfRecGraph.1, hfRecGraph.2.1, ?_⟩
    intro β hβα y
    have hiffG : ⟨β, y⟩ₖ ∈ f ↔ Function.Graph G y (f ↾ β) :=
      attempt_iff_of_exists_on (F := G) (IsOrdinal.toOrdinal α) (hrec := hfRecGraph.2.2) β hβα y
    constructor
    · intro hβy
      have hyEq : y = SuccLimitRecursionStep (0 : V) (OrdinalMulSuccStep a) (f ↾ β) := by
        simpa [G, Function.Graph] using hiffG.1 hβy
      have hstep := succLimitRecursionStep_spec (0 : V) (OrdinalMulSuccStep a)
        (hr := IsFunction.restrict f β)
      rwa [← hyEq] at hstep
    · intro hyRule
      have hstep := succLimitRecursionStep_spec (0 : V) (OrdinalMulSuccStep a)
        (hr := IsFunction.restrict f β)
      have hyEq := (succLimitRecursionRule_functionLike (0 : V) (OrdinalMulSuccStep a)
        (f ↾ β) (IsFunction.restrict f β)).unique hyRule hstep
      exact hiffG.2 (by simp [G, Function.Graph, hyEq])
  have hstrict : IsStrictIncreasingOrdinalGraph f :=
    succLimitRecursion_strictIncreasing
      (a₀ := (0 : V)) (F := OrdinalMulSuccStep a)
      (ordinalMulSuccStep_strict_of_pos a ha ha0) hStepExtend hrec
  have hValOrd : ∀ β y, β ∈ α → ⟨β, y⟩ₖ ∈ f → IsOrdinal y :=
    succLimitRecursion_stageValue_isOrdinal
      (a₀ := (0 : V)) (F := OrdinalMulSuccStep a) (by infer_instance)
      (by
        intro x hx
        simp only [OrdinalMulSuccStep]
        exact ordinalAddValue_isOrdinal x a hx ha)
      hrec
  have hMulDef : ℒₛₑₜ-function₁[V] (ordinalMulValue a) := ordinalMulValue_definable a
  have hstrictRel :
      ∀ β γ yβ yγ : V, IsOrdinal β → IsOrdinal γ → β ∈ γ →
        (yβ = ordinalMulValue a β) → (yγ = ordinalMulValue a γ) → yβ ∈ yγ := by
    intro β' γ' yβ yγ hβ hγ' hβγ hyβ hyγ
    rcases hyβ with rfl; rcases hyγ with rfl
    exact ordinalMulValue_strictIncreasing_right_of_left_pos
      (a := a) (ha := ha) (ha0 := ha0) (hStepExtend := hStepExtend) (hγ := hγ') (hβγ := hβγ)
  have hself : ∀ β y, β ∈ α → ⟨β, y⟩ₖ ∈ f → β ⊆ y := by
    intro β y hβα hβy
    have hβord : IsOrdinal β := IsOrdinal.of_mem hβα
    have hyord : IsOrdinal y := hValOrd β y hβα hβy
    have hyeqMul : y = ordinalMulValue a β := by
      simpa [G, ordinalMulValue] using
        (kpair_mem_recursionFunctionOrDefault_iff_eq_transfiniteRecursionValueFn_of_mem
          (F := G) hGdef hα hβα).1 hβy
    have hnot : ¬ y ∈ β := by
      intro hyβ
      exact (strictIncreasing_function_no_value_lt_self
        (F := ordinalMulValue a)
        (hFdef := hMulDef)
        (hFstrict := by
          intro β' γ' hβ' hγ' hβγ'
          exact ordinalMulValue_strictIncreasing_right_of_left_pos
            (a := a) (ha := ha) (ha0 := ha0) (hStepExtend := hStepExtend) (hγ := hγ') (hβγ := hβγ'))
        β hβord) (by simpa [hyeqMul] using hyβ)
    letI : IsOrdinal β := hβord; letI : IsOrdinal y := hyord
    rcases IsOrdinal.mem_trichotomy (α := y) (β := β) with (hyβ | hEq | hβy)
    · exact (hnot hyβ).elim
    · simp [hEq]
    · exact (IsOrdinal.subset_iff (α := β) (β := y)).2 (Or.inr hβy)
  have hsuccγα : succ γ ∈ α := by simp [α]
  rcases succLimitRecursion_exists_max_stage_le
      (a₀ := (0 : V)) (F := OrdinalMulSuccStep a)
      (hrec := hrec) (hstrict := hstrict) (hValOrd := hValOrd) (hself := hself)
      (hξord := hγ) (ha₀le := empty_subset γ) (hsuccξα := hsuccγα) with
    ⟨δ, yδ, hδα, hδyδ, hyδleγ, hmax⟩
  have hδord : IsOrdinal δ := IsOrdinal.of_mem hδα
  have hyδord : IsOrdinal yδ := hValOrd δ yδ hδα hδyδ
  rcases ordinalAddValue_exists_right_eq_of_subset yδ γ hyδord hγ hyδleγ with ⟨ρ, hρeq⟩
  have hρord : IsOrdinal ρ.val := ρ.ordinal
  by_cases hρlt : ρ.val ∈ a
  · have hyδeqMul : yδ = ordinalMulValue a δ := by
      simpa [G, ordinalMulValue] using
        (kpair_mem_recursionFunctionOrDefault_iff_eq_transfiniteRecursionValueFn_of_mem
          (F := G) hGdef hα hδα).1 hδyδ
    refine ⟨⟨δ, hδord⟩, ρ, ?_, hρlt⟩
    simpa [hyδeqMul] using hρeq
  · have ha_sub_ρ : a ⊆ ρ.val := by
      letI : IsOrdinal a := ha; letI : IsOrdinal ρ.val := hρord
      rcases IsOrdinal.mem_trichotomy (α := ρ.val) (β := a) with (hρa | hEq | haρ)
      · exact (hρlt hρa).elim
      · simp [hEq]
      · exact hρord.toIsTransitive.transitive _ haρ
    have hsuccδ_in_α : succ δ ∈ α := by
      have hδ_sub_γ : δ ⊆ γ := subset_trans (hself δ yδ hδα hδyδ) hyδleγ
      letI : IsOrdinal δ := hδord; letI : IsOrdinal γ := hγ
      rcases (IsOrdinal.subset_iff (α := δ) (β := γ)).1 hδ_sub_γ with (hEq | hMem)
      · rw [hEq]; exact hsuccγα
      · have hsuccδ_sub_γ : succ δ ⊆ γ := by
          intro t ht
          rcases show t = δ ∨ t ∈ δ by simpa [mem_succ_iff] using ht with (rfl | htδ)
          · exact hMem
          · exact hγ.toIsTransitive.transitive _ hMem _ htδ
        haveI : IsOrdinal (succ δ) := IsOrdinal.succ
        rcases (IsOrdinal.subset_iff (α := succ δ) (β := γ)).1 hsuccδ_sub_γ with (hEq' | hMem')
        · rw [hEq']; exact hα.toIsTransitive.transitive _ hsuccγα _ (by simp)
        · exact hα.toIsTransitive.transitive _ hsuccγα _ (by simp [mem_succ_iff, hMem'])
    have hsucc_sub_α : succ δ ⊆ α := hα.toIsTransitive.transitive _ hsuccδ_in_α
    rcases mem_domain_iff.mp (by rw [hfRecGraph.2.1]; exact hsuccδ_in_α) with ⟨yS, hsuccδyS⟩
    have hySrule :=
      (hrec.2.2.2 (succ δ) hsuccδ_in_α yS).1 hsuccδyS
    have hdom_succδ : domain (f ↾ (succ δ)) = succ δ := by
      simp [domain_restrict_eq, hfRecGraph.2.1, inter_eq_right_of_subset hsucc_sub_α]
    have hyS_eq_add : yS = ordinalAddValue yδ a := by
      rcases hySrule with (h0 | hs | hL)
      · have : succ δ = (∅ : V) := by simpa [hdom_succδ] using h0.1
        have hδsucc : δ ∈ succ (V := V) δ := by simp
        have hδempty : δ ∈ (∅ : V) := by simpa only [this] using hδsucc
        exact (not_mem_empty hδempty).elim
      · rcases hs with ⟨δ', x, hdom', hδ'x, hxyS⟩
        have hδ' : δ' = δ := succ_inj (by simpa [hdom_succδ] using hdom'.symm)
        rw [hδ'] at hδ'x
        haveI : IsFunction f := hfRecGraph.1
        have hx_eq : x = yδ := IsFunction.unique (kpair_mem_restrict_iff.mp hδ'x).1 hδyδ
        subst hx_eq; exact hxyS
      · exact (hL.2.1 δ (by simp [hdom_succδ])).elim
    have hyS_sub_γ : yS ⊆ γ := by
      have : ordinalAddValue yδ a ⊆ ordinalAddValue yδ ρ.val :=
        ordinalAddValue_subset_right_of_initOrdinal yδ a ρ.val hyδord ha hρord ha_sub_ρ
      simpa [hyS_eq_add, hρeq] using this
    have hsuccδ_sub_δ : succ δ ⊆ δ := hmax (succ δ) yS hsuccδ_in_α hsuccδyS hyS_sub_γ
    exact (mem_irrefl δ (hsuccδ_sub_δ _ (by simp))).elim

end ordinalMultiplication

end IsOrdinal

namespace Ordinal

variable [V ⊧ₘ* 𝗭𝗙]

/-- Current set-level value of ordinal multiplication. -/
noncomputable def mulValue (α β : Ordinal V) : V :=
  IsOrdinal.ordinalMulValue α.val β.val

@[simp] lemma mulValue_bot (α : Ordinal V) : mulValue α ⊥ = (0 : V) := by
  simp only [mulValue, bot_val_eq]
  exact IsOrdinal.ordinalMulValue_zero (a := α.val)

@[simp] lemma mulValue_succ (α β : Ordinal V) :
    mulValue α β.succ = IsOrdinal.ordinalAddValue (mulValue α β) α.val := by
  simp [mulValue, succ_val]

end Ordinal

end LO.FirstOrder.SetTheory
