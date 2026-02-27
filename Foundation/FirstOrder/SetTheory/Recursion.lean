module

public import Foundation.FirstOrder.SetTheory.Ordinal

namespace LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V ⊧ₘ* 𝗭]

namespace IsOrdinal

variable {α β γ : V}
/--
`f` is a recursion function on `α` for the relation `φ`.
-/
def IsTransfiniteRecursionFunction (φ : V → V → Prop) (α f : V) : Prop :=
  IsOrdinal α ∧ IsFunction f ∧ domain f = α ∧
    ∀ β ∈ α, ∀ y, ⟨β, y⟩ₖ ∈ f ↔ φ (f ↾ β) y

/--
Under function-likeness of `φ`, the existential stage clause implies the bidirectional clause.
-/
lemma transfinite_recursion_iff_of_exists
    (φ : V → V → Prop) (hφ : ∀ r : V, IsFunction r → ∃! y : V, φ r y)
    {α f : V} [IsOrdinal α] [IsFunction f]
    (hrec : ∀ β ∈ α, ∃ z, ⟨β, z⟩ₖ ∈ f ∧ φ (f ↾ β) z) :
    ∀ β ∈ α, ∀ y, ⟨β, y⟩ₖ ∈ f ↔ φ (f ↾ β) y := by
  intro β hβα y
  constructor
  · intro hβy
    rcases hrec β hβα with ⟨z, hβz, hzφ⟩
    have : y = z := IsFunction.unique hβy hβz
    simpa [this] using hzφ
  · intro hyφ
    rcases hrec β hβα with ⟨z, hβz, hzφ⟩
    have huniq := hφ (f ↾ β) (IsFunction.restrict f β)
    have : y = z := huniq.unique hyφ hzφ
    simpa [this] using hβz

/--
If two functions with the same ordinal domain satisfy the same recursive clause at each stage,
then they are equal.
-/
lemma transfinite_recursion_function_unique
    (φ : V → V → Prop) {α f g : V} [hα : IsOrdinal α]
    [hf : IsFunction f] [hg : IsFunction g]
    (hdf : domain f = α) (hdg : domain g = α)
    (hrecf : ∀ β ∈ α, ∀ y, ⟨β, y⟩ₖ ∈ f ↔ φ (f ↾ β) y)
    (hrecg : ∀ β ∈ α, ∀ y, ⟨β, y⟩ₖ ∈ g ↔ φ (g ↾ β) y) :
    f = g := by
  have hrestr :
      ∀ β : Ordinal V, β.val ⊆ α → f ↾ β.val = g ↾ β.val := by
    refine transfinite_induction (P := fun x ↦ x ⊆ α → f ↾ x = g ↾ x) (by definability) ?_
    intro β ihβ hβα
    apply subset_antisymm
    · intro p hp
      rcases mem_restrict_iff.mp hp with ⟨hpf, x, hxβ, y, rfl⟩
      have hxα : x ∈ α := hβα x hxβ
      have hfxgx : f ↾ x = g ↾ x := by
        have : IsOrdinal x := IsOrdinal.of_mem hxβ
        let ξ : Ordinal V := IsOrdinal.toOrdinal x
        have hξβ : ξ < β := Ordinal.lt_def.mpr <| by simpa [ξ] using hxβ
        have hξα : ξ.val ⊆ α := by
          exact subset_trans (β.ordinal.toIsTransitive.transitive x hxβ) hβα
        simpa [ξ] using ihβ ξ hξβ hξα
      have hφ : φ (g ↾ x) y := by
        have : φ (f ↾ x) y := (hrecf x hxα y).1 hpf
        simpa [hfxgx] using this
      have hpg : ⟨x, y⟩ₖ ∈ g := (hrecg x hxα y).2 hφ
      exact mem_restrict_iff.mpr ⟨hpg, x, hxβ, y, rfl⟩
    · intro p hp
      rcases mem_restrict_iff.mp hp with ⟨hpg, x, hxβ, y, rfl⟩
      have hxα : x ∈ α := hβα x hxβ
      have hfxgx : f ↾ x = g ↾ x := by
        have : IsOrdinal x := IsOrdinal.of_mem hxβ
        let ξ : Ordinal V := IsOrdinal.toOrdinal x
        have hξβ : ξ < β := Ordinal.lt_def.mpr <| by simpa [ξ] using hxβ
        have hξα : ξ.val ⊆ α := by
          exact subset_trans (β.ordinal.toIsTransitive.transitive x hxβ) hβα
        simpa [ξ] using ihβ ξ hξβ hξα
      have hφ : φ (f ↾ x) y := by
        have : φ (g ↾ x) y := (hrecg x hxα y).1 hpg
        simpa [hfxgx] using this
      have hpf : ⟨x, y⟩ₖ ∈ f := (hrecf x hxα y).2 hφ
      exact mem_restrict_iff.mpr ⟨hpf, x, hxβ, y, rfl⟩
  have hαfg : f ↾ α = g ↾ α := by
    simpa using hrestr (IsOrdinal.toOrdinal α) (subset_refl α)
  have hfα : f ↾ α = f := by
    apply subset_antisymm
    · intro p hp
      exact (mem_restrict_iff.mp hp).1
    · intro p hp
      rcases show ∃ x ∈ domain f, ∃ y ∈ range f, p = ⟨x, y⟩ₖ from by
          simpa [mem_prod_iff] using subset_prod_of_mem_function (IsFunction.mem_function f) p hp with
        ⟨x, hxd, y, -, rfl⟩
      have hxα : x ∈ α := by simpa [hdf] using hxd
      exact mem_restrict_iff.mpr ⟨hp, x, hxα, y, rfl⟩
  have hgα : g ↾ α = g := by
    apply subset_antisymm
    · intro p hp
      exact (mem_restrict_iff.mp hp).1
    · intro p hp
      rcases show ∃ x ∈ domain g, ∃ y ∈ range g, p = ⟨x, y⟩ₖ from by
          simpa [mem_prod_iff] using subset_prod_of_mem_function (IsFunction.mem_function g) p hp with
        ⟨x, hxd, y, -, rfl⟩
      have hxα : x ∈ α := by simpa [hdg] using hxd
      exact mem_restrict_iff.mpr ⟨hp, x, hxα, y, rfl⟩
  calc
    f = f ↾ α := hfα.symm
    _ = g ↾ α := hαfg
    _ = g := hgα

/--
Uniqueness of recursion functions from the existential stage clause, under function-likeness of `φ`.
-/
lemma transfinite_recursion_function_unique_of_exists
    (φ : V → V → Prop) (hφ : ∀ r : V, IsFunction r → ∃! y : V, φ r y)
    {α f g : V} [hα : IsOrdinal α] [hf : IsFunction f] [hg : IsFunction g]
    (hdf : domain f = α) (hdg : domain g = α)
    (hrecf : ∀ β ∈ α, ∃ z, ⟨β, z⟩ₖ ∈ f ∧ φ (f ↾ β) z)
    (hrecg : ∀ β ∈ α, ∃ z, ⟨β, z⟩ₖ ∈ g ∧ φ (g ↾ β) z) :
    f = g := by
  apply transfinite_recursion_function_unique
    (φ := φ) (hdf := hdf) (hdg := hdg)
  · exact transfinite_recursion_iff_of_exists (φ := φ) hφ hrecf
  · exact transfinite_recursion_iff_of_exists (φ := φ) hφ hrecg

/--
If recursion functions exist on ordinal domains, then recursion values are unique.
-/
lemma transfinite_recursion_value_existsUnique_of_function_exists
    (φ : V → V → Prop) (hφ : ∀ r : V, IsFunction r → ∃! y : V, φ r y)
    (hex :
      ∀ α : V, IsOrdinal α →
        ∃ f : V, IsFunction f ∧ domain f = α ∧
          (∀ β ∈ α, ∃ z, ⟨β, z⟩ₖ ∈ f ∧ φ (f ↾ β) z)) :
    ∀ α : V, IsOrdinal α →
      ∃! y : V, ∃ f : V, IsFunction f ∧ domain f = α ∧
        (∀ β ∈ α, ∃ z, ⟨β, z⟩ₖ ∈ f ∧ φ (f ↾ β) z) ∧ φ f y := by
  intro α hα
  rcases hex α hα with ⟨f, hff, hdf, hrecf⟩
  rcases hφ f hff with ⟨y, hy, hyu⟩
  refine ⟨y, ⟨f, hff, hdf, hrecf, hy⟩, ?_⟩
  intro y' hy'
  rcases hy' with ⟨g, hgg, hdg, hrecg, hyg⟩
  letI : IsOrdinal α := hα
  letI : IsFunction f := hff
  letI : IsFunction g := hgg
  have hfg : f = g := transfinite_recursion_function_unique_of_exists
    (φ := φ) hφ (hdf := hdf) (hdg := hdg) (hrecf := hrecf) (hrecg := hrecg)
  have : y' = y := by
    have hφuniq := hφ g hgg
    exact hφuniq.unique hyg (by simpa [hfg] using hy)
  simpa using this

/--
Restricting an inserted relation to a set that does not contain the inserted first coordinate
recovers the original restriction.
-/
lemma restrict_insert_kpair_eq_restrict_of_not_mem
    {f x y A : V} (hxA : x ∉ A) :
    (insert ⟨x, y⟩ₖ f) ↾ A = f ↾ A := by
  ext p
  constructor
  · intro hp
    rcases mem_restrict_iff.mp hp with ⟨hp', a, haA, b, rfl⟩
    rcases show ⟨a, b⟩ₖ = ⟨x, y⟩ₖ ∨ ⟨a, b⟩ₖ ∈ f by simpa using hp' with (hxy | hf)
    · rcases kpair_inj hxy with ⟨rfl, rfl⟩
      exact (hxA haA).elim
    · exact mem_restrict_iff.mpr ⟨hf, a, haA, b, rfl⟩
  · intro hp
    rcases mem_restrict_iff.mp hp with ⟨hf, a, haA, b, rfl⟩
    exact mem_restrict_iff.mpr ⟨by simp [hf], a, haA, b, rfl⟩

/--
Successor step for transfinite-recursion functions in existential-stage form.
-/
lemma transfinite_recursion_function_exists_succ
    (φ : V → V → Prop) (hφ : ∀ r : V, IsFunction r → ∃! y : V, φ r y)
    {α f : V} [hα : IsOrdinal α] [hf : IsFunction f]
    (hdf : domain f = α)
    (hrec : ∀ β ∈ α, ∃ z, ⟨β, z⟩ₖ ∈ f ∧ φ (f ↾ β) z) :
    ∃ g : V, IsFunction g ∧ domain g = succ α ∧
      (∀ β ∈ succ α, ∃ z, ⟨β, z⟩ₖ ∈ g ∧ φ (g ↾ β) z) := by
  rcases hφ f hf with ⟨y, hy, -⟩
  let g : V := insert ⟨α, y⟩ₖ f
  have hαnd : α ∉ domain f := by simp [hdf]
  have hg : IsFunction g := by
    simpa [g] using (IsFunction.insert f α y hαnd)
  refine ⟨g, hg, ?_, ?_⟩
  · simp [g, hdf, succ]
  · intro β hβsucc
    rcases show β = α ∨ β ∈ α by simpa [mem_succ_iff] using hβsucc with (rfl | hβα)
    · refine ⟨y, ?_, ?_⟩
      · simp [g]
      · have hga : g ↾ β = f := by
          calc
            g ↾ β = f ↾ β := by
              simpa [g] using restrict_insert_kpair_eq_restrict_of_not_mem (f := f) (x := β) (y := y) (A := β) (by simp)
            _ = f := by
              exact IsFunction.restrict_eq_self f β (by simp [hdf])
        rw [hga]; exact hy
    · rcases hrec β hβα with ⟨z, hβz, hzφ⟩
      refine ⟨z, by simp [g, hβz], ?_⟩
      have hαβ : α ∉ β := mem_asymm hβα
      have hgb : g ↾ β = f ↾ β := by
        simpa [g] using restrict_insert_kpair_eq_restrict_of_not_mem (f := f) (x := α) (y := y) (A := β) hαβ
      simpa [hgb] using hzφ

/--
Coherence: if `β ∈ α`, a recursion function on `α` restricts to the recursion function on `β`.
-/
lemma transfinite_recursion_function_restrict_eq_of_mem
    (φ : V → V → Prop) (hφ : ∀ r : V, IsFunction r → ∃! y : V, φ r y)
    {α β f g : V} [hα : IsOrdinal α] [hβ : IsOrdinal β] [hf : IsFunction f] [hg : IsFunction g]
    (hβα : β ∈ α)
    (hdf : domain f = α) (hdg : domain g = β)
    (hrecf : ∀ γ ∈ α, ∃ z, ⟨γ, z⟩ₖ ∈ f ∧ φ (f ↾ γ) z)
    (hrecg : ∀ γ ∈ β, ∃ z, ⟨γ, z⟩ₖ ∈ g ∧ φ (g ↾ γ) z) :
    f ↾ β = g := by
  have hβsubα : β ⊆ α := hα.toIsTransitive.transitive _ hβα
  have hdfβ : domain (f ↾ β) = β := by
    calc
      domain (f ↾ β) = domain f ∩ β := domain_restrict_eq f β
      _ = α ∩ β := by simp [hdf]
      _ = β := inter_eq_right_of_subset hβsubα
  have hrecfβ : ∀ γ ∈ β, ∃ z, ⟨γ, z⟩ₖ ∈ (f ↾ β) ∧ φ ((f ↾ β) ↾ γ) z := by
    intro γ hγβ
    have hγα : γ ∈ α := hβsubα _ hγβ
    rcases hrecf γ hγα with ⟨z, hγz, hzφ⟩
    have hγsubβ : γ ⊆ β := hβ.toIsTransitive.transitive _ hγβ
    refine ⟨z, ?_, ?_⟩
    · exact kpair_mem_restrict_iff.mpr ⟨hγz, hγβ⟩
    · simpa [restrict_restrict_of_subset hγsubβ] using hzφ
  haveI : IsFunction (f ↾ β) := IsFunction.restrict f β
  have hfg : f ↾ β = g := transfinite_recursion_function_unique_of_exists
    (φ := φ) hφ (hdf := hdfβ) (hdg := hdg) (hrecf := hrecfβ) (hrecg := hrecg)
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

/--
Any two transfinite-recursion functions for a function-like `φ` agree on overlapping inputs.
-/
lemma transfinite_recursion_function_coherent
    (φ : V → V → Prop) (hφ : ∀ r : V, IsFunction r → ∃! y : V, φ r y)
    {β γ f g x y₁ y₂ : V}
    [hβ : IsOrdinal β] [hγ : IsOrdinal γ] [hf : IsFunction f] [hg : IsFunction g]
    (hdf : domain f = β) (hdg : domain g = γ)
    (hrecf : ∀ ξ ∈ β, ∃ z, ⟨ξ, z⟩ₖ ∈ f ∧ φ (f ↾ ξ) z)
    (hrecg : ∀ ξ ∈ γ, ∃ z, ⟨ξ, z⟩ₖ ∈ g ∧ φ (g ↾ ξ) z)
    (hxy₁ : ⟨x, y₁⟩ₖ ∈ f) (hxy₂ : ⟨x, y₂⟩ₖ ∈ g) :
    y₁ = y₂ := by
  have hxβ : x ∈ β := by simpa [hdf] using mem_domain_of_kpair_mem hxy₁
  have hxγ : x ∈ γ := by simpa [hdg] using mem_domain_of_kpair_mem hxy₂
  rcases IsOrdinal.mem_trichotomy (α := β) (β := γ) with (hβγ | rfl | hγβ)
  · have hgb : g ↾ β = f := transfinite_recursion_function_restrict_eq_of_mem
      (φ := φ) hφ (hβα := hβγ) (hdf := hdg) (hdg := hdf) (hrecf := hrecg) (hrecg := hrecf)
    have hxy₂' : ⟨x, y₂⟩ₖ ∈ g ↾ β := kpair_mem_restrict_iff.mpr ⟨hxy₂, hxβ⟩
    have hxy₂f : ⟨x, y₂⟩ₖ ∈ f := by simpa [hgb] using hxy₂'
    exact IsFunction.unique hxy₁ hxy₂f
  · have hfg : f = g := transfinite_recursion_function_unique_of_exists
      (φ := φ) hφ (hdf := hdf) (hdg := hdg) (hrecf := hrecf) (hrecg := hrecg)
    simpa [hfg] using IsFunction.unique hxy₁ (by simpa [hfg] using hxy₂)
  · have hfb : f ↾ γ = g := transfinite_recursion_function_restrict_eq_of_mem
      (φ := φ) hφ (hβα := hγβ) (hdf := hdf) (hdg := hdg) (hrecf := hrecf) (hrecg := hrecg)
    have hxy₁' : ⟨x, y₁⟩ₖ ∈ f ↾ γ := kpair_mem_restrict_iff.mpr ⟨hxy₁, hxγ⟩
    have hxy₁g : ⟨x, y₁⟩ₖ ∈ g := by simpa [hfb] using hxy₁'
    exact (IsFunction.unique hxy₂ hxy₁g).symm

/--
Using replacement, collect all predecessor recursion functions on an ordinal domain.
-/
lemma replacement_collect_predecessor_recursion_functions
    [V ⊧ₘ* 𝗭𝗙]
    (φ : V → V → Prop) (hφ : ∀ r : V, IsFunction r → ∃! y : V, φ r y)
    {α : V} [hα : IsOrdinal α]
    (hR : ℒₛₑₜ-relation[V] (fun β f ↦
      IsFunction f ∧ domain f = β ∧
      ∀ γ ∈ β, ∃ z, ⟨γ, z⟩ₖ ∈ f ∧ φ (f ↾ γ) z))
    (hprev : ∀ β ∈ α, ∃ f : V, IsFunction f ∧ domain f = β ∧
      ∀ γ ∈ β, ∃ z, ⟨γ, z⟩ₖ ∈ f ∧ φ (f ↾ γ) z) :
    ∃ C : V, ∀ f : V, f ∈ C ↔ ∃ β ∈ α, IsFunction f ∧ domain f = β ∧
      ∀ γ ∈ β, ∃ z, ⟨γ, z⟩ₖ ∈ f ∧ φ (f ↾ γ) z := by
  let R : V → V → Prop := fun β f ↦
    IsFunction f ∧ domain f = β ∧
    ∀ γ ∈ β, ∃ z, ⟨γ, z⟩ₖ ∈ f ∧ φ (f ↾ γ) z
  have hfunon : ∀ β : V, β ∈ α → ∃! f : V, R β f := by
    intro β hβα
    rcases hprev β hβα with ⟨f, hf⟩
    refine ⟨f, hf, ?_⟩
    intro g hg
    letI : IsOrdinal β := IsOrdinal.of_mem hβα
    letI : IsFunction f := hf.1
    letI : IsFunction g := hg.1
    have : f = g := transfinite_recursion_function_unique_of_exists
      (φ := φ) hφ (hdf := hf.2.1) (hdg := hg.2.1) (hrecf := hf.2.2) (hrecg := hg.2.2)
    simpa [R] using this.symm
  rcases replacement_exists_on (X := α) R hR hfunon with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro f
  constructor
  · intro hfC
    rcases (hC f).1 hfC with ⟨β, hβα, hfR⟩
    exact ⟨β, hβα, hfR⟩
  · rintro ⟨β, hβα, hfR⟩
    exact (hC f).2 ⟨β, hβα, hfR⟩

/--
Limit-style union construction: from a collected predecessor family `C`,
build a recursion function on `α` by union, assuming every `x ∈ α` lies in some `β ∈ α`
and predecessor recursion functions exist for all ordinals in `α`.
-/
lemma transfinite_recursion_function_exists_sUnion_of_collected
    (φ : V → V → Prop) (hφ : ∀ r : V, IsFunction r → ∃! y : V, φ r y)
    {α C : V} [hα : IsOrdinal α]
    (hC : ∀ f : V, f ∈ C ↔ ∃ β ∈ α, IsFunction f ∧ domain f = β ∧
      ∀ γ ∈ β, ∃ z, ⟨γ, z⟩ₖ ∈ f ∧ φ (f ↾ γ) z)
    (hprev : ∀ β ∈ α, ∃ g : V, IsFunction g ∧ domain g = β ∧
      ∀ γ ∈ β, ∃ z, ⟨γ, z⟩ₖ ∈ g ∧ φ (g ↾ γ) z)
    (hcover : ∀ x ∈ α, ∃ β ∈ α, x ∈ β) :
    ∃ f : V, IsFunction f ∧ domain f = α ∧
      ∀ γ ∈ α, ∃ z, ⟨γ, z⟩ₖ ∈ f ∧ φ (f ↾ γ) z := by
  let f : V := ⋃ˢ C
  have hf_isFunction : IsFunction f := by
    refine IsFunction.sUnion_of_coherent
      (hfunc := ?_)
      (hcoh := ?_)
    · intro u huC
      rcases (hC u).1 huC with ⟨β, hβα, hu, -, -⟩
      exact hu
    · intro u huC v hvC x y₁ y₂ hxyu hxyv
      rcases (hC u).1 huC with ⟨β, hβα, hu, hdu, hrecu⟩
      rcases (hC v).1 hvC with ⟨γ, hγα, hv, hdv, hrecv⟩
      letI : IsOrdinal β := IsOrdinal.of_mem hβα
      letI : IsOrdinal γ := IsOrdinal.of_mem hγα
      letI : IsFunction u := hu
      letI : IsFunction v := hv
      exact transfinite_recursion_function_coherent
        (φ := φ) hφ (hdf := hdu) (hdg := hdv) (hrecf := hrecu) (hrecg := hrecv) hxyu hxyv
  -- Helper: get a member of C with a given domain β ∈ α
  have hC_mem : ∀ β ∈ α, ∃ g ∈ C, domain g = β ∧ IsFunction g ∧
      ∀ γ ∈ β, ∃ z, ⟨γ, z⟩ₖ ∈ g ∧ φ (g ↾ γ) z := by
    intro β hβα
    rcases hprev β hβα with ⟨g, hgf, hgd, hgrec⟩
    exact ⟨g, (hC g).2 ⟨β, hβα, hgf, hgd, hgrec⟩, hgd, hgf, hgrec⟩
  have hf_domain : domain f = α := by
    apply domain_sUnion_eq_of_domain_subset_and_cover
    · intro u huC
      rcases (hC u).1 huC with ⟨β, hβα, hu, hdu, -⟩
      have hβsubα : β ⊆ α := hα.toIsTransitive.transitive _ hβα
      exact ⟨hu, by simpa [hdu] using hβsubα⟩
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
  -- φ (f ↾ γ) z: we know φ (u ↾ γ) z, and f ↾ γ = u ↾ γ by coherence
  · have hγsubβ : γ ⊆ β := (IsOrdinal.of_mem hβα).toIsTransitive.transitive _ hγβ
    have hγsubα : γ ⊆ α := subset_trans hγsubβ (hα.toIsTransitive.transitive _ hβα)
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

/--
Existence of transfinite-recursion functions on arbitrary ordinal domains,
in existential-stage form.
-/
def ExistsTransfiniteRecursionFunction (φ : V → V → Prop) (α : V) : Prop :=
  ∃ f : V, IsFunction f ∧ domain f = α ∧
    ∀ β ∈ α, ∃ z, ⟨β, z⟩ₖ ∈ f ∧ φ (f ↾ β) z

lemma existsTransfiniteRecursionFunction_definable
    (φ : V → V → Prop)
    (hR : ℒₛₑₜ-relation[V] (fun β f ↦
      IsFunction f ∧ domain f = β ∧
      ∀ γ ∈ β, ∃ z, ⟨γ, z⟩ₖ ∈ f ∧ φ (f ↾ γ) z)) :
    ℒₛₑₜ-predicate[V] (ExistsTransfiniteRecursionFunction φ) :=
  Language.Definable.exs (Language.Definable.retraction hR ![1, 0])

lemma transfinite_recursion_function_exists
    [V ⊧ₘ* 𝗭𝗙]
    (φ : V → V → Prop) (hφ : ∀ r : V, IsFunction r → ∃! y : V, φ r y)
    (hR : ℒₛₑₜ-relation[V] (fun β f ↦
      IsFunction f ∧ domain f = β ∧
      ∀ γ ∈ β, ∃ z, ⟨γ, z⟩ₖ ∈ f ∧ φ (f ↾ γ) z)) :
    ∀ α : V, IsOrdinal α →
      ExistsTransfiniteRecursionFunction φ α := by
  let R : V → V → Prop := fun β f ↦
    IsFunction f ∧ domain f = β ∧
    ∀ γ ∈ β, ∃ z, ⟨γ, z⟩ₖ ∈ f ∧ φ (f ↾ γ) z
  have hP : ℒₛₑₜ-predicate[V] (ExistsTransfiniteRecursionFunction φ) :=
    existsTransfiniteRecursionFunction_definable (φ := φ) hR
  have hrec : ∀ α : Ordinal V, ExistsTransfiniteRecursionFunction φ α.val := by
    refine transfinite_induction
      (P := ExistsTransfiniteRecursionFunction φ)
      hP
      ?_
    intro α ih
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
        rcases ih βo hβlt with ⟨f, hff, hdf, hstage⟩
        letI : IsOrdinal β := hβord
        letI : IsFunction f := hff
        rcases transfinite_recursion_function_exists_succ
            (φ := φ) hφ (α := β) (f := f) hdf hstage with ⟨g, hg⟩
        refine ⟨g, ?_⟩
        rwa [hαβ]
      · have hprev : ∀ β ∈ α.val, ∃ g : V, IsFunction g ∧ domain g = β ∧
            ∀ γ ∈ β, ∃ z, ⟨γ, z⟩ₖ ∈ g ∧ φ (g ↾ γ) z := by
          intro β hβα
          letI : IsOrdinal β := IsOrdinal.of_mem hβα
          let βo : Ordinal V := IsOrdinal.toOrdinal β
          have hβlt : βo < α := Ordinal.lt_def.mpr (by simpa [βo] using hβα)
          rcases ih βo hβlt with ⟨g, hg⟩
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
        rcases replacement_collect_predecessor_recursion_functions
            (φ := φ) hφ (α := α.val) hR hprev with ⟨C, hC⟩
        rcases transfinite_recursion_function_exists_sUnion_of_collected
            (φ := φ) hφ (α := α.val) (C := C) hC hprev hcover with ⟨f, hf⟩
        exact ⟨f, hf⟩
  intro α hα
  letI : IsOrdinal α := hα
  let αo : Ordinal V := IsOrdinal.toOrdinal α
  rcases hrec αo with ⟨f, hf⟩
  exact ⟨f, by simpa [R, αo] using hf⟩

/--
Relation form of transfinite recursion value:
`IsTransfiniteRecursionValue φ α y` means `y` is obtained by applying `φ`
to a recursion function on domain `α`.
-/
def IsTransfiniteRecursionValue (φ : V → V → Prop) (α y : V) : Prop :=
  ∃ f : V, IsFunction f ∧ domain f = α ∧
    (∀ β ∈ α, ∃ z, ⟨β, z⟩ₖ ∈ f ∧ φ (f ↾ β) z) ∧ φ f y

/--
Specialized transfinite-recursion rule:
- initial stage (`domain r = ∅`): value is `a₀`,
- successor stage (`domain r = succ β`): value is given by `S` from the predecessor value,
- limit stage (neither empty nor successor): value is `⋃ˢ range r`.
-/
def SuccLimitRecursionRule (a₀ : V) (S : V → V → Prop) (r y : V) : Prop :=
  (domain r = ∅ ∧ y = a₀) ∨
  (∃ β x, domain r = succ β ∧ ⟨β, x⟩ₖ ∈ r ∧ S x y) ∨
  (domain r ≠ ∅ ∧ (∀ β, domain r ≠ succ β) ∧ y = ⋃ˢ range r)

lemma succLimitRecursionRule_definable
    (a₀ : V) (S : V → V → Prop) (hS : ℒₛₑₜ-relation[V] S) :
    ℒₛₑₜ-relation[V] (SuccLimitRecursionRule a₀ S) := by
  letI : ℒₛₑₜ-relation[V] S := hS
  unfold SuccLimitRecursionRule
  definability

lemma succLimitRecursionRule_definable_varInit
    (S : V → V → Prop) (hS : ℒₛₑₜ-relation[V] S) :
    ℒₛₑₜ-relation₃[V] (fun a₀ r y ↦ SuccLimitRecursionRule a₀ S r y) := by
  letI : ℒₛₑₜ-relation[V] S := hS
  unfold SuccLimitRecursionRule
  definability

lemma succLimitRecursionRule_definable_varStep
    (a₀ : V) (S : V → V → V → Prop) (hS : ℒₛₑₜ-relation₃[V] S) :
    ℒₛₑₜ-relation₃[V] (fun a r y ↦ SuccLimitRecursionRule a₀ (S a) r y) := by
  letI : ℒₛₑₜ-relation₃[V] S := hS
  unfold SuccLimitRecursionRule
  definability

lemma succLimitRecursionRule_functionLike
    (a₀ : V) (S : V → V → Prop)
    (hSfun : ∀ x : V, ∃! y : V, S x y) :
    ∀ r : V, IsFunction r → ∃! y : V, SuccLimitRecursionRule a₀ S r y := by
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
      rcases hSfun x with ⟨y, hyS, hySu⟩
      refine ⟨y, Or.inr (Or.inl ⟨β, x, hdb, hβx, hyS⟩), ?_⟩
      intro y' hy'
      rcases hy' with (hy0 | hyS' | hyL)
      · exact (h0 hy0.1).elim
      · rcases hyS' with ⟨β', x', hdb', hβ'x', hx'y'⟩
        have hdbEq : succ β' = succ β := by simpa [hdb] using hdb'.symm
        have hβeq : β' = β := succ_inj hdbEq
        subst hβeq
        have hxEq : x' = x := IsFunction.unique hβ'x' hβx
        subst hxEq
        exact hySu y' hx'y'
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
Bridge between the relation-level recursion-value predicate and a witness by
`IsTransfiniteRecursionFunction`.
-/
lemma isTransfiniteRecursionValue_iff_exists_isTransfiniteRecursionFunction
    (φ : V → V → Prop)
    (hφ : ∀ r : V, IsFunction r → ∃! y : V, φ r y)
    {α y : V} (hα : IsOrdinal α) :
    IsTransfiniteRecursionValue φ α y ↔
      ∃ f : V, IsTransfiniteRecursionFunction φ α f ∧ φ f y := by
  letI : IsOrdinal α := hα
  constructor
  · rintro ⟨f, hf, hdf, hrec, hfy⟩
    letI : IsFunction f := hf
    have hrec' : ∀ β ∈ α, ∀ z, ⟨β, z⟩ₖ ∈ f ↔ φ (f ↾ β) z :=
      transfinite_recursion_iff_of_exists (φ := φ) hφ (α := α) (f := f) hrec
    refine ⟨f, ?_, hfy⟩
    exact ⟨hα, hf, hdf, hrec'⟩
  · rintro ⟨f, ⟨_, hf_func, hf_dom, hf_rec⟩, hfy⟩
    refine ⟨f, hf_func, hf_dom, ?_, hfy⟩
    intro β hβα
    letI : IsFunction f := hf_func
    rcases hφ (f ↾ β) (IsFunction.restrict f β) with ⟨z, hz, -⟩
    exact ⟨z, (hf_rec β hβα z).2 hz, hz⟩

lemma isTransfiniteRecursionValue_definable
    (φ : V → V → Prop)
    (hφ : ℒₛₑₜ-relation[V] φ) :
    ℒₛₑₜ-relation[V] (IsTransfiniteRecursionValue φ) := by
  letI : ℒₛₑₜ-relation[V] φ := hφ
  unfold IsTransfiniteRecursionValue
  definability

lemma isTransfiniteRecursionValue_definable_var
    (φ : V → V → V → Prop)
    (hφ : ℒₛₑₜ-relation₃[V] φ) :
    ℒₛₑₜ-relation₃[V] (fun a α y ↦ IsTransfiniteRecursionValue (φ a) α y) := by
  letI : ℒₛₑₜ-relation₃[V] φ := hφ
  unfold IsTransfiniteRecursionValue
  definability

/--
Existence and uniqueness of transfinite-recursion values in relation form.
-/
lemma transfinite_recursion_value_existsUnique
    [V ⊧ₘ* 𝗭𝗙]
    (φ : V → V → Prop)
    (hφ : ∀ r : V, IsFunction r → ∃! y : V, φ r y)
    (hR : ℒₛₑₜ-relation[V] (fun β f ↦
      IsFunction f ∧ domain f = β ∧
      ∀ γ ∈ β, ∃ z, ⟨γ, z⟩ₖ ∈ f ∧ φ (f ↾ γ) z)) :
    ∀ α : V, IsOrdinal α → ∃! y : V, IsTransfiniteRecursionValue φ α y := by
  intro α hα
  exact transfinite_recursion_value_existsUnique_of_function_exists
    (φ := φ) hφ (hex := transfinite_recursion_function_exists (φ := φ) hφ hR) α hα

/--
Existence/uniqueness of specialized recursion values (initial/successor/limit rule).
-/
lemma succLimitRecursion_value_existsUnique
    [V ⊧ₘ* 𝗭𝗙]
    (a₀ : V) (S : V → V → Prop)
    (hSdef : ℒₛₑₜ-relation[V] S)
    (hSfun : ∀ x : V, ∃! y : V, S x y) :
    ∀ α : V, IsOrdinal α →
      ∃! y : V, IsTransfiniteRecursionValue (SuccLimitRecursionRule a₀ S) α y := by
  let φ : V → V → Prop := SuccLimitRecursionRule a₀ S
  have hφfun : ∀ r : V, IsFunction r → ∃! y : V, φ r y :=
    succLimitRecursionRule_functionLike a₀ S hSfun
  have hφdef : ℒₛₑₜ-relation[V] φ :=
    succLimitRecursionRule_definable a₀ S hSdef
  have hR : ℒₛₑₜ-relation[V] (fun β f ↦
      IsFunction f ∧ domain f = β ∧
      ∀ γ ∈ β, ∃ z, ⟨γ, z⟩ₖ ∈ f ∧ φ (f ↾ γ) z) := by
    letI : ℒₛₑₜ-relation[V] φ := hφdef
    definability
  exact transfinite_recursion_value_existsUnique (φ := φ) hφfun hR

/--
Convenience successor equation for specialized recursion:
if `x` is the value at `α` and `y` is the value at `succ α`, then `S x y`.
-/
lemma succLimitRecursion_successor
    (a₀ : V) (S : V → V → Prop)
    (hSfun : ∀ x : V, ∃! y : V, S x y)
    {α x y : V} (hα : IsOrdinal α)
    (hx : IsTransfiniteRecursionValue (SuccLimitRecursionRule a₀ S) α x)
    (hy : IsTransfiniteRecursionValue (SuccLimitRecursionRule a₀ S) (succ α) y) :
    S x y := by
  let φ : V → V → Prop := SuccLimitRecursionRule a₀ S
  have hφfun : ∀ r : V, IsFunction r → ∃! z : V, φ r z :=
    succLimitRecursionRule_functionLike a₀ S hSfun
  rcases (isTransfiniteRecursionValue_iff_exists_isTransfiniteRecursionFunction
      (φ := φ) hφfun (hα := hα)).1 hx with ⟨g, ⟨_, hg_func, hg_dom, hg_rec⟩, hgx⟩
  have hsuccα : IsOrdinal (succ α) := IsOrdinal.succ
  rcases (isTransfiniteRecursionValue_iff_exists_isTransfiniteRecursionFunction
      (φ := φ) hφfun (hα := hsuccα)).1 hy with ⟨f, ⟨_, hf_func, hf_dom, hf_rec⟩, hfy⟩
  letI : IsFunction f := hf_func
  letI : IsFunction g := hg_func
  -- Build the restriction as a recursion function on α
  have hα_sub_succα : α ⊆ succ α := mem_subset_refl α
  have hfrestrict : IsTransfiniteRecursionFunction φ α (f ↾ α) := by
    refine ⟨hα, IsFunction.restrict _ _, ?_, ?_⟩
    · simp [hf_dom, domain_restrict_eq, hα_sub_succα]
    · intro γ hγα y'
      have hγ_sub_α : γ ⊆ α := hα.toIsTransitive.transitive _ hγα
      have hγ_succα : γ ∈ succ α := hα_sub_succα _ hγα
      rw [kpair_mem_restrict_iff, restrict_restrict_of_subset hγ_sub_α, hf_rec γ hγ_succα y']
      simp [hγα]
  -- Show g = f ↾ α by uniqueness
  letI : IsFunction (f ↾ α) := IsFunction.restrict f α
  have hgEq : g = f ↾ α := transfinite_recursion_function_unique
    (φ := φ) (hdf := hg_dom) (hdg := (by simp [hf_dom, domain_restrict_eq, hα_sub_succα]))
    (hrecf := hg_rec) (hrecg := hfrestrict.2.2.2)
  have hφfa : φ (f ↾ α) x := by simpa [hgEq] using hgx
  have hαxf : ⟨α, x⟩ₖ ∈ f := (hf_rec α (by simp) x).2 hφfa
  rcases hfy with (h0 | hs | hL)
  · have : domain f = (∅ : V) := h0.1
    have : succ α = (∅ : V) := by rwa [hf_dom] at this
    have : α ∈ (∅ : V) := by simpa [this] using (show α ∈ succ α by simp)
    exact (not_mem_empty this).elim
  · rcases hs with ⟨β, u, hdb, hβuf, hSuy⟩
    have hdbEq : succ β = succ α := by simpa [hf_dom] using hdb.symm
    have hβα : β = α := succ_inj hdbEq
    subst hβα
    have hux : u = x := IsFunction.unique hβuf hαxf
    subst hux
    exact hSuy
  · exact (hL.2.1 α (by rw [hf_dom])).elim

/--
Graph-level strict increase on ordinal indices:
if `β ∈ γ` and `f(β)=x`, `f(γ)=y`, then `x ∈ y`.
-/
def IsStrictIncreasingOrdinalGraph (f : V) : Prop :=
  IsFunction f ∧ ∀ β γ x y, β ∈ γ → ⟨β, x⟩ₖ ∈ f → ⟨γ, y⟩ₖ ∈ f → x ∈ y

/--
If each successor step is strict (`x ∈ y`) and extends membership (`u ∈ x → u ∈ y`),
then every recursion function for `SuccLimitRecursionRule a₀ S` is strictly increasing.
-/
lemma succLimitRecursion_strictIncreasing
    (a₀ : V) (S : V → V → Prop)
    (hSstrict : ∀ x y, S x y → x ∈ y)
    (hSextend : ∀ u x y, u ∈ x → S x y → u ∈ y)
    {α f : V}
    (hrec : IsTransfiniteRecursionFunction (SuccLimitRecursionRule a₀ S) α f) :
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
    have hyRule : SuccLimitRecursionRule a₀ S (f ↾ γo.val) y :=
      (hf_rec γo.val hγα y).1 hγy
    rcases hyRule with (h0 | hs | hL)
    · have hdom : domain (f ↾ γo.val) = γo.val := by
        simp [domain_restrict_eq, hf_dom, inter_eq_right_of_subset hγsubα]
      have : γo.val = (∅ : V) := by simpa [hdom] using h0.1
      have : β ∈ (∅ : V) := by simp [this] at hβγ
      exact (not_mem_empty this).elim
    · rcases hs with ⟨δ, u, hdb, hδu, hSuy⟩
      have hdom : domain (f ↾ γo.val) = γo.val := by
        simp [domain_restrict_eq, hf_dom, inter_eq_right_of_subset hγsubα]
      have hγsucc : γo.val = succ δ := by simpa [hdom] using hdb
      have hδu_f : ⟨δ, u⟩ₖ ∈ f := (kpair_mem_restrict_iff.mp hδu).1
      rcases show β = δ ∨ β ∈ δ by simpa [hγsucc, mem_succ_iff] using hβγ with (rfl | hβδ)
      · have hxu : x = u := IsFunction.unique hβx hδu_f
        rw [hxu]
        exact hSstrict u y hSuy
      · have hδord : IsOrdinal δ := by
          have hδγ : δ ∈ γo.val := by simp [hγsucc]
          exact IsOrdinal.of_mem hδγ
        have hδγ : IsOrdinal.toOrdinal δ < γo := Ordinal.lt_def.mpr (by simp [hγsucc])
        have hxu : x ∈ u := (ih (IsOrdinal.toOrdinal δ) hδγ) β hβδ x u hβx hδu_f
        exact hSextend x u y hxu hSuy
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
      have hzRule : SuccLimitRecursionRule a₀ S (f ↾ (succ β)) z :=
        (hf_rec (succ β) hsuccβα z).1 hsuccβz
      have hxz : x ∈ z := by
        have hdom_succβ : domain (f ↾ (succ β)) = succ β := by
          simp [domain_restrict_eq, hf_dom,
            inter_eq_right_of_subset (subset_trans hsuccβsubγ hγsubα)]
        rcases hzRule with (h0' | hs' | hL')
        · have : succ β = (∅ : V) := by simpa [hdom_succβ] using h0'.1
          have : β ∈ (∅ : V) := by simpa [this] using (show β ∈ succ β by simp)
          exact (not_mem_empty this).elim
        · rcases hs' with ⟨δ, u, hdb', hδu, hSuz⟩
          have hdbEq : succ δ = succ β := by simpa [hdom_succβ] using hdb'.symm
          have hδβ : δ = β := succ_inj hdbEq
          rw [hδβ] at hδu
          have hβu_f : ⟨β, u⟩ₖ ∈ f := (kpair_mem_restrict_iff.mp hδu).1
          have hxu : x = u := IsFunction.unique hβx hβu_f
          rw [hxu]
          exact hSstrict u z hSuz
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
    (a₀ : V) (S : V → V → Prop)
    {α f : V}
    (hrec : IsTransfiniteRecursionFunction (SuccLimitRecursionRule a₀ S) α f)
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
  have hy₀Rule : SuccLimitRecursionRule a₀ S (f ↾ β₀) y₀ := (hfRec β₀ hβ₀α y₀).1 hβ₀y₀
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
    (a₀ : V) (S : V → V → Prop)
    (ha₀ : IsOrdinal a₀)
    (hSord : ∀ x y : V, IsOrdinal x → S x y → IsOrdinal y)
    {α f : V}
    (hrec : IsTransfiniteRecursionFunction (SuccLimitRecursionRule a₀ S) α f) :
    ∀ β y, β ∈ α → ⟨β, y⟩ₖ ∈ f → IsOrdinal y := by
  obtain ⟨hαord, hfFunc, hfDom, hfRec⟩ := hrec
  letI : IsFunction f := hfFunc
  let P : V → Prop := fun β ↦ β ⊆ α → ∀ y, ⟨β, y⟩ₖ ∈ f → IsOrdinal y
  have hPall : ∀ βo : Ordinal V, P βo.val := by
    refine transfinite_induction (P := P) (by definability) ?_
    intro βo ih hβα y hβy
    have hβα' : βo.val ∈ α := by simpa [hfDom] using mem_domain_of_kpair_mem hβy
    have hyRule : SuccLimitRecursionRule a₀ S (f ↾ βo.val) y := (hfRec βo.val hβα' y).1 hβy
    rcases hyRule with (h0 | hs | hL)
    · simpa [h0.2] using ha₀
    · rcases hs with ⟨δ, x, hdb, hδx_restr, hSxy⟩
      have hδβ : δ ∈ βo.val := (kpair_mem_restrict_iff.mp hδx_restr).2
      have hδx : ⟨δ, x⟩ₖ ∈ f := (kpair_mem_restrict_iff.mp hδx_restr).1
      have hδord : IsOrdinal δ := IsOrdinal.of_mem hδβ
      let δo : Ordinal V := IsOrdinal.toOrdinal δ
      have hδlt : δo < βo := Ordinal.lt_def.mpr (by simpa [δo] using hδβ)
      have hδsubβ : δ ⊆ βo.val := βo.ordinal.toIsTransitive.transitive _ hδβ
      have hδsubα : δ ⊆ α := subset_trans hδsubβ hβα
      have hxord : IsOrdinal x := (ih δo hδlt) hδsubα x hδx
      exact hSord x y hxord hSxy
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

/-! ### Ordinal addition (initial/successor stage) -/

section ordinalAddition


/-- Successor-step relation used for ordinal addition recursion. -/
def OrdinalAddSuccStep (x y : V) : Prop := y = succ x

lemma ordinalAddSuccStep_definable :
    ℒₛₑₜ-relation[V] OrdinalAddSuccStep := by
  unfold OrdinalAddSuccStep
  definability

lemma ordinalAddSuccStep_functionLike :
    ∀ x : V, ∃! y : V, OrdinalAddSuccStep x y := by
  intro x
  refine ⟨succ x, rfl, ?_⟩
  intro y hy
  simpa [OrdinalAddSuccStep] using hy

lemma ordinalAddSuccStep_strict :
    ∀ x y : V, OrdinalAddSuccStep x y → x ∈ y := by
  intro x y hxy
  rcases hxy with rfl
  simp

lemma ordinalAddSuccStep_extend :
    ∀ u x y : V, u ∈ x → OrdinalAddSuccStep x y → u ∈ y := by
  intro u x y hux hxy
  rcases hxy with rfl
  simp [mem_succ_iff, hux]

variable [V ⊧ₘ* 𝗭𝗙]

/--
Set-level ordinal-addition value obtained by specialized transfinite recursion:
base value `a`, successor step `succ`, and limit step `⋃ˢ range`.
-/
noncomputable def ordinalAddValue (a b : V) (hb : IsOrdinal b) : V :=
  Classical.choose! (succLimitRecursion_value_existsUnique
    (a₀ := a) (S := OrdinalAddSuccStep)
    ordinalAddSuccStep_definable ordinalAddSuccStep_functionLike b hb)

/--
Totalized version of `ordinalAddValue` without an ordinality hypothesis.
If `b` is not ordinal, return an arbitrary fallback value (`a`).
-/
noncomputable def ordinalAddValueTotal (a b : V) : V := by
  classical
  by_cases hb : IsOrdinal b
  · exact ordinalAddValue a b hb
  · exact a

@[simp] lemma ordinalAddValueTotal_of_isOrdinal (a b : V) (hb : IsOrdinal b) :
    ordinalAddValueTotal a b = ordinalAddValue a b hb := by
  simp [ordinalAddValueTotal, hb]

@[simp] lemma ordinalAddValueTotal_of_not_isOrdinal (a b : V) (hb : ¬IsOrdinal b) :
    ordinalAddValueTotal a b = a := by
  simp [ordinalAddValueTotal, hb]

lemma ordinalAddValue_isRecursionValue (a b : V) (hb : IsOrdinal b) :
    IsTransfiniteRecursionValue (SuccLimitRecursionRule a OrdinalAddSuccStep) b
      (ordinalAddValue a b hb) :=
  Classical.choose!_spec (succLimitRecursion_value_existsUnique
    (a₀ := a) (S := OrdinalAddSuccStep)
    ordinalAddSuccStep_definable ordinalAddSuccStep_functionLike b hb)

lemma ordinalAddValue_eq_iff_isRecursionValue
    (a b y : V) (hb : IsOrdinal b) :
    y = ordinalAddValue a b hb ↔
      IsTransfiniteRecursionValue (SuccLimitRecursionRule a OrdinalAddSuccStep) b y := by
  constructor
  · intro hy
    simpa [hy] using ordinalAddValue_isRecursionValue a b hb
  · intro hy
    have huniq := succLimitRecursion_value_existsUnique
      (a₀ := a) (S := OrdinalAddSuccStep)
      ordinalAddSuccStep_definable ordinalAddSuccStep_functionLike b hb
    exact huniq.unique hy (ordinalAddValue_isRecursionValue a b hb)

lemma ordinalAddValueTotal_eq_iff_recursion_or_fallback
    (a b y : V) :
    y = ordinalAddValueTotal a b ↔
      (IsOrdinal b ∧
        IsTransfiniteRecursionValue (SuccLimitRecursionRule a OrdinalAddSuccStep) b y) ∨
      (¬IsOrdinal b ∧ y = a) := by
  classical
  by_cases hb : IsOrdinal b
  · constructor
    · intro hy
      left
      refine ⟨hb, ?_⟩
      have : y = ordinalAddValue a b hb := by
        simpa [ordinalAddValueTotal, hb] using hy
      exact (ordinalAddValue_eq_iff_isRecursionValue a b y hb).1 this
    · rintro (⟨-, hy⟩ | hfalse)
      · have : y = ordinalAddValue a b hb :=
          (ordinalAddValue_eq_iff_isRecursionValue a b y hb).2 hy
        simpa [ordinalAddValueTotal, hb] using this
      · exact (hfalse.1 hb).elim
  · constructor
    · intro hy
      right
      exact ⟨hb, by simpa [ordinalAddValueTotal, hb] using hy⟩
    · rintro (hfalse | ⟨-, hy⟩)
      · exact (hb hfalse.1).elim
      · simpa [ordinalAddValueTotal, hb] using hy

lemma ordinalAddValueTotal_eq_definable (a : V) :
    ℒₛₑₜ-relation[V] (fun b y ↦ y = ordinalAddValueTotal a b) := by
  let R : V → V → Prop := fun b y ↦
    (IsOrdinal b ∧
      IsTransfiniteRecursionValue (SuccLimitRecursionRule a OrdinalAddSuccStep) b y) ∨
    (¬IsOrdinal b ∧ y = a)
  have hTRVdef : ℒₛₑₜ-relation[V]
      (IsTransfiniteRecursionValue (SuccLimitRecursionRule a OrdinalAddSuccStep)) := by
    exact isTransfiniteRecursionValue_definable
      (φ := SuccLimitRecursionRule a OrdinalAddSuccStep)
      (succLimitRecursionRule_definable
        (a₀ := a) (S := OrdinalAddSuccStep) ordinalAddSuccStep_definable)
  have hR : ℒₛₑₜ-relation[V] R := by
    letI : ℒₛₑₜ-relation[V]
      (IsTransfiniteRecursionValue (SuccLimitRecursionRule a OrdinalAddSuccStep)) := hTRVdef
    change ℒₛₑₜ-relation[V] (fun b y ↦
      (IsOrdinal b ∧
        IsTransfiniteRecursionValue (SuccLimitRecursionRule a OrdinalAddSuccStep) b y) ∨
      (¬IsOrdinal b ∧ y = a))
    definability
  have hEq :
      (fun b y ↦ y = ordinalAddValueTotal a b) = R := by
    funext b y
    exact propext (ordinalAddValueTotal_eq_iff_recursion_or_fallback a b y)
  simpa [R, hEq] using hR

lemma ordinalAddValueTotal_eq_definable_varInit :
    ℒₛₑₜ-relation₃[V] (fun a b y ↦ y = ordinalAddValueTotal a b) := by
  let R : V → V → V → Prop := fun a b y ↦
    (IsOrdinal b ∧
      IsTransfiniteRecursionValue (SuccLimitRecursionRule a OrdinalAddSuccStep) b y) ∨
    (¬IsOrdinal b ∧ y = a)
  have hφdef : ℒₛₑₜ-relation₃[V]
      (fun a r y ↦ SuccLimitRecursionRule a OrdinalAddSuccStep r y) := by
    exact succLimitRecursionRule_definable_varInit
      (S := OrdinalAddSuccStep) ordinalAddSuccStep_definable
  have hTRVdef : ℒₛₑₜ-relation₃[V]
      (fun a b y ↦ IsTransfiniteRecursionValue
        (SuccLimitRecursionRule a OrdinalAddSuccStep) b y) := by
    exact isTransfiniteRecursionValue_definable_var
      (φ := fun a r y ↦ SuccLimitRecursionRule a OrdinalAddSuccStep r y) hφdef
  have hR : ℒₛₑₜ-relation₃[V] R := by
    letI : ℒₛₑₜ-relation₃[V]
      (fun a b y ↦ IsTransfiniteRecursionValue
        (SuccLimitRecursionRule a OrdinalAddSuccStep) b y) := hTRVdef
    change ℒₛₑₜ-relation₃[V] (fun a b y ↦
      (IsOrdinal b ∧
        IsTransfiniteRecursionValue (SuccLimitRecursionRule a OrdinalAddSuccStep) b y) ∨
      (¬IsOrdinal b ∧ y = a))
    definability
  have hEq :
      (fun a b y ↦ y = ordinalAddValueTotal a b) = R := by
    funext a b y
    exact propext (ordinalAddValueTotal_eq_iff_recursion_or_fallback a b y)
  simpa [R, hEq] using hR

lemma ordinalAddValueTotal_eq_definable_left (b : V) :
    ℒₛₑₜ-relation[V] (fun a y ↦ y = ordinalAddValueTotal a b) := by
  let R : V → V → Prop := fun a y ↦
    (IsOrdinal b ∧
      IsTransfiniteRecursionValue (SuccLimitRecursionRule a OrdinalAddSuccStep) b y) ∨
    (¬IsOrdinal b ∧ y = a)
  have hR : ℒₛₑₜ-relation[V] R := by
    show ℒₛₑₜ-relation[V] (fun a y ↦
      (IsOrdinal b ∧
        IsTransfiniteRecursionValue (SuccLimitRecursionRule a OrdinalAddSuccStep) b y) ∨
      (¬IsOrdinal b ∧ y = a))
    unfold IsTransfiniteRecursionValue SuccLimitRecursionRule OrdinalAddSuccStep
    definability
  have hEq :
      (fun a y ↦ y = ordinalAddValueTotal a b) = R := by
    funext a y
    exact propext (ordinalAddValueTotal_eq_iff_recursion_or_fallback a b y)
  rw [hEq]; exact hR

omit [V ⊧ₘ* 𝗭𝗙] in
lemma ordinalAddValue_zero_isRecursionValue (a : V) :
    IsTransfiniteRecursionValue (SuccLimitRecursionRule a OrdinalAddSuccStep) 0 a := by
  refine ⟨∅, inferInstance, ?_, ?_, ?_⟩
  · simp [zero_def]
  · intro γ hγ
    simp [zero_def] at hγ
  · exact Or.inl ⟨by simp, rfl⟩

@[simp] lemma ordinalAddValue_zero (a : V) :
    ordinalAddValue a 0 (inferInstance : IsOrdinal (0 : V)) = a := by
  have huniq := succLimitRecursion_value_existsUnique
    (a₀ := a) (S := OrdinalAddSuccStep)
    ordinalAddSuccStep_definable ordinalAddSuccStep_functionLike 0 (inferInstance : IsOrdinal (0 : V))
  exact huniq.unique
    (ordinalAddValue_isRecursionValue a 0 (inferInstance : IsOrdinal (0 : V)))
    (ordinalAddValue_zero_isRecursionValue a)

@[simp] lemma ordinalAddValue_succ (a β : V) (hβ : IsOrdinal β) :
    ordinalAddValue a (succ β) (IsOrdinal.succ (α := β)) =
      succ (ordinalAddValue a β hβ) := by
  let φ : V → V → Prop := SuccLimitRecursionRule a OrdinalAddSuccStep
  have hx : IsTransfiniteRecursionValue φ β (ordinalAddValue a β hβ) :=
    ordinalAddValue_isRecursionValue a β hβ
  have hy : IsTransfiniteRecursionValue φ (succ β)
      (ordinalAddValue a (succ β) (IsOrdinal.succ (α := β))) :=
    ordinalAddValue_isRecursionValue a (succ β) (IsOrdinal.succ (α := β))
  have hstep : OrdinalAddSuccStep (ordinalAddValue a β hβ)
      (ordinalAddValue a (succ β) (IsOrdinal.succ (α := β))) :=
    succLimitRecursion_successor
      (a₀ := a) (S := OrdinalAddSuccStep) ordinalAddSuccStep_functionLike hβ hx hy
  simpa [OrdinalAddSuccStep] using hstep

lemma ordinalAddValue_isOrdinal
    (a β : V) (ha : IsOrdinal a) (hβ : IsOrdinal β) :
    IsOrdinal (ordinalAddValue a β hβ) := by
  let φ : V → V → Prop := SuccLimitRecursionRule a OrdinalAddSuccStep
  have hφfun : ∀ r : V, IsFunction r → ∃! y : V, φ r y :=
    succLimitRecursionRule_functionLike a OrdinalAddSuccStep ordinalAddSuccStep_functionLike
  have hφdef : ℒₛₑₜ-relation[V] φ :=
    succLimitRecursionRule_definable a OrdinalAddSuccStep ordinalAddSuccStep_definable
  have hR : ℒₛₑₜ-relation[V] (fun ξ f ↦
      IsFunction f ∧ domain f = ξ ∧
      ∀ ζ ∈ ξ, ∃ z, ⟨ζ, z⟩ₖ ∈ f ∧ φ (f ↾ ζ) z) := by
    letI : ℒₛₑₜ-relation[V] φ := hφdef
    definability
  let α := succ β
  have hα : IsOrdinal α := IsOrdinal.succ
  rcases transfinite_recursion_function_exists (φ := φ) hφfun hR α hα with
    ⟨f, hfFunc, hfDom, hfEx⟩
  letI : IsOrdinal α := hα
  letI : IsFunction f := hfFunc
  have hfRec : ∀ ξ ∈ α, ∀ y, ⟨ξ, y⟩ₖ ∈ f ↔ φ (f ↾ ξ) y :=
    transfinite_recursion_iff_of_exists (φ := φ) hφfun hfEx
  let hrec : IsTransfiniteRecursionFunction φ α f := ⟨hα, hfFunc, hfDom, hfRec⟩
  have hValOrd : ∀ ξ y, ξ ∈ α → ⟨ξ, y⟩ₖ ∈ f → IsOrdinal y :=
    succLimitRecursion_stageValue_isOrdinal
      (a₀ := a) (S := OrdinalAddSuccStep) ha
      (by
        intro x y hx hxy
        rcases hxy with rfl
        exact IsOrdinal.succ)
      hrec
  have hβα : β ∈ α := by simp [α]
  rcases mem_domain_iff.mp (by rw [hfDom]; exact hβα) with ⟨y, hβy⟩
  have hyTRV : IsTransfiniteRecursionValue φ β y :=
    (isTransfiniteRecursionValue_iff_exists_isTransfiniteRecursionFunction
      (φ := φ) hφfun (hα := hβ)).2 ⟨f ↾ β, by
        have hβsubα : β ⊆ α := hα.toIsTransitive.transitive _ hβα
        refine ⟨hβ, IsFunction.restrict _ _, ?_, ?_⟩
        · simp [hfDom, domain_restrict_eq, hβsubα]
        · intro ξ hξβ y'
          have hξα : ξ ∈ α := hβsubα _ hξβ
          have hξsubβ : ξ ⊆ β := hβ.toIsTransitive.transitive _ hξβ
          rw [kpair_mem_restrict_iff, restrict_restrict_of_subset hξsubβ, hfRec ξ hξα y']
          simp [hξβ], (hfRec β hβα y).1 hβy⟩
  have hyeq : y = ordinalAddValue a β hβ := by
    have huniq := succLimitRecursion_value_existsUnique
      (a₀ := a) (S := OrdinalAddSuccStep)
      ordinalAddSuccStep_definable ordinalAddSuccStep_functionLike β hβ
    exact huniq.unique hyTRV (ordinalAddValue_isRecursionValue a β hβ)
  simpa [hyeq] using hValOrd β y hβα hβy

lemma ordinalAddValue_strictIncreasing_right
    (a : V) {β γ : V} (hγ : IsOrdinal γ) (hβγ : β ∈ γ) :
    ordinalAddValue a β (IsOrdinal.of_mem hβγ) ∈ ordinalAddValue a γ hγ := by
  let φ : V → V → Prop := SuccLimitRecursionRule a OrdinalAddSuccStep
  have hφfun : ∀ r : V, IsFunction r → ∃! y : V, φ r y :=
    succLimitRecursionRule_functionLike a OrdinalAddSuccStep ordinalAddSuccStep_functionLike
  have hφdef : ℒₛₑₜ-relation[V] φ :=
    succLimitRecursionRule_definable a OrdinalAddSuccStep ordinalAddSuccStep_definable
  have hR : ℒₛₑₜ-relation[V] (fun δ f ↦
      IsFunction f ∧ domain f = δ ∧
      ∀ ξ ∈ δ, ∃ z, ⟨ξ, z⟩ₖ ∈ f ∧ φ (f ↾ ξ) z) := by
    letI : ℒₛₑₜ-relation[V] φ := hφdef
    definability
  let α := succ γ
  have hα : IsOrdinal α := IsOrdinal.succ (α := γ)
  -- Get a recursion function F on α = succ γ
  rcases transfinite_recursion_function_exists (φ := φ) hφfun hR α hα with
    ⟨F, hFfunc, hFdom, hFex⟩
  letI : IsOrdinal α := hα
  letI : IsFunction F := hFfunc
  have hFrec : ∀ ξ ∈ α, ∀ y, ⟨ξ, y⟩ₖ ∈ F ↔ φ (F ↾ ξ) y :=
    transfinite_recursion_iff_of_exists (φ := φ) hφfun hFex
  let hFtr : IsTransfiniteRecursionFunction φ α F := ⟨hα, hFfunc, hFdom, hFrec⟩
  have hβα : β ∈ α := hα.toIsTransitive.transitive γ (show γ ∈ α by simp [α]) β hβγ
  have hγα : γ ∈ α := by simp [α]
  -- Show F(β) = ordinalAddValue a β and F(γ) = ordinalAddValue a γ
  -- by converting through IsTransfiniteRecursionValue
  have hβord : IsOrdinal β := IsOrdinal.of_mem hβγ
  rcases mem_domain_iff.mp (by rw [hFdom]; exact hβα) with ⟨x, hβxF⟩
  rcases mem_domain_iff.mp (by rw [hFdom]; exact hγα) with ⟨y, hγyF⟩
  -- x is the recursion value at β via F
  have hxφ : φ (F ↾ β) x := (hFrec β hβα x).1 hβxF
  have hxTRV : IsTransfiniteRecursionValue φ β x :=
    (isTransfiniteRecursionValue_iff_exists_isTransfiniteRecursionFunction
      (φ := φ) hφfun (hα := hβord)).2 ⟨F ↾ β, by
        have hβ_sub_α : β ⊆ α := hα.toIsTransitive.transitive _ hβα
        refine ⟨hβord, IsFunction.restrict _ _, ?_, ?_⟩
        · simp [hFdom, domain_restrict_eq, hβ_sub_α]
        · intro ξ hξβ y'
          have hξα : ξ ∈ α := hβ_sub_α _ hξβ
          have hξ_sub_β : ξ ⊆ β := hβord.toIsTransitive.transitive _ hξβ
          rw [kpair_mem_restrict_iff, restrict_restrict_of_subset hξ_sub_β, hFrec ξ hξα y']
          simp [hξβ], hxφ⟩
  -- y is the recursion value at γ via F
  have hyφ : φ (F ↾ γ) y := (hFrec γ hγα y).1 hγyF
  have hyTRV : IsTransfiniteRecursionValue φ γ y :=
    (isTransfiniteRecursionValue_iff_exists_isTransfiniteRecursionFunction
      (φ := φ) hφfun (hα := hγ)).2 ⟨F ↾ γ, by
        have hγ_sub_α : γ ⊆ α := hα.toIsTransitive.transitive _ hγα
        refine ⟨hγ, IsFunction.restrict _ _, ?_, ?_⟩
        · simp [hFdom, domain_restrict_eq, hγ_sub_α]
        · intro ξ hξγ y'
          have hξα : ξ ∈ α := hγ_sub_α _ hξγ
          have hξ_sub_γ : ξ ⊆ γ := hγ.toIsTransitive.transitive _ hξγ
          rw [kpair_mem_restrict_iff, restrict_restrict_of_subset hξ_sub_γ, hFrec ξ hξα y']
          simp [hξγ], hyφ⟩
  -- By uniqueness, x = ordinalAddValue a β and y = ordinalAddValue a γ
  have hxeq : x = ordinalAddValue a β hβord := by
    have huniq := succLimitRecursion_value_existsUnique
      (a₀ := a) (S := OrdinalAddSuccStep)
      ordinalAddSuccStep_definable ordinalAddSuccStep_functionLike β hβord
    exact huniq.unique hxTRV (ordinalAddValue_isRecursionValue a β hβord)
  have hyeq : y = ordinalAddValue a γ hγ := by
    have huniq := succLimitRecursion_value_existsUnique
      (a₀ := a) (S := OrdinalAddSuccStep)
      ordinalAddSuccStep_definable ordinalAddSuccStep_functionLike γ hγ
    exact huniq.unique hyTRV (ordinalAddValue_isRecursionValue a γ hγ)
  -- F is strictly increasing, so x ∈ y
  have hInc : IsStrictIncreasingOrdinalGraph F :=
    succLimitRecursion_strictIncreasing
      (a₀ := a) (S := OrdinalAddSuccStep)
      ordinalAddSuccStep_strict ordinalAddSuccStep_extend hFtr
  have hxy : x ∈ y := hInc.2 β γ x y hβγ hβxF hγyF
  rwa [hxeq, hyeq] at hxy

lemma ordinalAddValue_subset_right_of_initOrdinal
    (a β γ : V) (ha : IsOrdinal a) (hβ : IsOrdinal β) (hγ : IsOrdinal γ)
    (hβγ : β ⊆ γ) :
    ordinalAddValue a β hβ ⊆ ordinalAddValue a γ hγ := by
  by_cases hEq : β = γ
  · subst hEq
    simp
  · have hβmemγ : β ∈ γ := (IsOrdinal.ssubset_iff (α := β) (β := γ)).1 ⟨hβγ, hEq⟩
    have hlt : ordinalAddValue a β hβ ∈ ordinalAddValue a γ hγ :=
      ordinalAddValue_strictIncreasing_right (a := a) (hγ := hγ) (hβγ := hβmemγ)
    have hγord' : IsOrdinal (ordinalAddValue a γ hγ) :=
      ordinalAddValue_isOrdinal a γ ha hγ
    exact hγord'.toIsTransitive.transitive _ hlt

omit [V ⊧ₘ* 𝗭𝗙] in
lemma ordinalAddRecursion_exists_max_right_le
    (a : V) {α f : V}
    (hrec : IsTransfiniteRecursionFunction (SuccLimitRecursionRule a OrdinalAddSuccStep) α f)
    (hstrict : IsStrictIncreasingOrdinalGraph f)
    (hValOrd : ∀ β y, β ∈ α → ⟨β, y⟩ₖ ∈ f → IsOrdinal y)
    (hself : ∀ β y, β ∈ α → ⟨β, y⟩ₖ ∈ f → β ⊆ y)
    {γ : V} (hγ : IsOrdinal γ) (hale : a ⊆ γ) (hsuccγα : succ γ ∈ α) :
    ∃ δ yδ, δ ∈ α ∧ ⟨δ, yδ⟩ₖ ∈ f ∧ yδ ⊆ γ ∧
      ∀ η yη, η ∈ α → ⟨η, yη⟩ₖ ∈ f → yη ⊆ γ → η ⊆ δ :=
  succLimitRecursion_exists_max_stage_le
    (a₀ := a) (S := OrdinalAddSuccStep)
    hrec hstrict hValOrd hself hγ hale hsuccγα

omit [V ⊧ₘ* 𝗭𝗙] in
lemma ordinalAddRecursion_exists_max_right_eq
    (a : V) {γ α f : V}
    (hαeq : α = succ (succ γ))
    (hrec : IsTransfiniteRecursionFunction (SuccLimitRecursionRule a OrdinalAddSuccStep) α f)
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
        simpa [OrdinalAddSuccStep] using hxyS
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
    ∃ δ : Ordinal V, ordinalAddValue a δ.val δ.ordinal = γ := by
  let φ : V → V → Prop := SuccLimitRecursionRule a OrdinalAddSuccStep
  have hφfun : ∀ r : V, IsFunction r → ∃! y : V, φ r y :=
    succLimitRecursionRule_functionLike a OrdinalAddSuccStep ordinalAddSuccStep_functionLike
  have hφdef : ℒₛₑₜ-relation[V] φ :=
    succLimitRecursionRule_definable a OrdinalAddSuccStep ordinalAddSuccStep_definable
  have hR : ℒₛₑₜ-relation[V] (fun β f ↦
      IsFunction f ∧ domain f = β ∧
      ∀ ξ ∈ β, ∃ z, ⟨ξ, z⟩ₖ ∈ f ∧ φ (f ↾ ξ) z) := by
    letI : ℒₛₑₜ-relation[V] φ := hφdef
    definability
  let α := succ (succ γ)
  have hα : IsOrdinal α := IsOrdinal.succ
  rcases transfinite_recursion_function_exists (φ := φ) hφfun hR α hα with
    ⟨f, hfFunc, hfDom, hfEx⟩
  letI : IsOrdinal α := hα
  letI : IsFunction f := hfFunc
  have hfRec : ∀ ξ ∈ α, ∀ y, ⟨ξ, y⟩ₖ ∈ f ↔ φ (f ↾ ξ) y :=
    transfinite_recursion_iff_of_exists (φ := φ) hφfun hfEx
  let hrec : IsTransfiniteRecursionFunction φ α f := ⟨hα, hfFunc, hfDom, hfRec⟩
  have hstrict : IsStrictIncreasingOrdinalGraph f :=
    succLimitRecursion_strictIncreasing
      (a₀ := a) (S := OrdinalAddSuccStep)
      ordinalAddSuccStep_strict ordinalAddSuccStep_extend hrec
  have hValOrd : ∀ β y, β ∈ α → ⟨β, y⟩ₖ ∈ f → IsOrdinal y :=
    succLimitRecursion_stageValue_isOrdinal
      (a₀ := a) (S := OrdinalAddSuccStep) ha
      (by
        intro x y hx hxy
        rcases hxy with rfl
        exact IsOrdinal.succ)
      hrec
  have hstrictRelTotal :
      ∀ β γ yβ yγ : V, IsOrdinal β → IsOrdinal γ → β ∈ γ →
        (yβ = ordinalAddValueTotal a β) → (yγ = ordinalAddValueTotal a γ) → yβ ∈ yγ := by
    intro β' γ' yβ yγ hβ hγ' hβγ hyβ hyγ
    rcases hyβ with rfl
    rcases hyγ with rfl
    have hlt : ordinalAddValue a β' hβ ∈ ordinalAddValue a γ' hγ' :=
      ordinalAddValue_strictIncreasing_right (a := a) (hγ := hγ') (hβγ := hβγ)
    simpa [ordinalAddValueTotal, hβ, hγ'] using hlt
  have hself : ∀ β y, β ∈ α → ⟨β, y⟩ₖ ∈ f → β ⊆ y := by
    intro β y hβα hβy
    have hβord : IsOrdinal β := IsOrdinal.of_mem hβα
    have hyord : IsOrdinal y := hValOrd β y hβα hβy
    have hyφ : φ (f ↾ β) y := (hfRec β hβα y).1 hβy
    have hyTRV : IsTransfiniteRecursionValue φ β y :=
      (isTransfiniteRecursionValue_iff_exists_isTransfiniteRecursionFunction
        (φ := φ) hφfun (hα := hβord)).2 ⟨f ↾ β, by
          have hβ_sub_α : β ⊆ α := hα.toIsTransitive.transitive _ hβα
          refine ⟨hβord, IsFunction.restrict _ _, ?_, ?_⟩
          · simp [hfDom, domain_restrict_eq, hβ_sub_α]
          · intro ξ hξβ y'
            have hξα : ξ ∈ α := hβ_sub_α _ hξβ
            have hξ_sub_β : ξ ⊆ β := hβord.toIsTransitive.transitive _ hξβ
            rw [kpair_mem_restrict_iff, restrict_restrict_of_subset hξ_sub_β, hfRec ξ hξα y']
            simp [hξβ], hyφ⟩
    have hyeqAdd : y = ordinalAddValue a β hβord := by
      have huniq := succLimitRecursion_value_existsUnique
        (a₀ := a) (S := OrdinalAddSuccStep)
        ordinalAddSuccStep_definable ordinalAddSuccStep_functionLike β hβord
      exact huniq.unique hyTRV (ordinalAddValue_isRecursionValue a β hβord)
    have hyeqTot : y = ordinalAddValueTotal a β := by
      simpa [ordinalAddValueTotal, hβord] using hyeqAdd
    have hnot : ¬ y ∈ β := by
      intro hyβ
      have hnotTot := strictIncreasing_relation_no_value_lt_self
        (R := fun x y ↦ y = ordinalAddValueTotal a x)
        (hRdef := ordinalAddValueTotal_eq_definable a)
        (hRfun := by intro x; exact ⟨ordinalAddValueTotal a x, rfl, by intro y hy; simpa using hy⟩)
        (hRstrict := hstrictRelTotal)
        β (ordinalAddValueTotal a β) hβord rfl
      exact hnotTot (by simpa [hyeqTot] using hyβ)
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
  have hyδφ : φ (f ↾ δ) yδ := (hfRec δ hδα yδ).1 hδyδ
  have hyδTRV : IsTransfiniteRecursionValue φ δ yδ :=
    (isTransfiniteRecursionValue_iff_exists_isTransfiniteRecursionFunction
      (φ := φ) hφfun (hα := hδord)).2 ⟨f ↾ δ, by
        have hδ_sub_α : δ ⊆ α := hα.toIsTransitive.transitive _ hδα
        refine ⟨hδord, IsFunction.restrict _ _, ?_, ?_⟩
        · simp [hfDom, domain_restrict_eq, hδ_sub_α]
        · intro ξ hξδ y'
          have hξα : ξ ∈ α := hδ_sub_α _ hξδ
          have hξ_sub_δ : ξ ⊆ δ := hδord.toIsTransitive.transitive _ hξδ
          rw [kpair_mem_restrict_iff, restrict_restrict_of_subset hξ_sub_δ, hfRec ξ hξα y']
          simp [hξδ], hyδφ⟩
  have hyδeqAdd : yδ = ordinalAddValue a δ hδord := by
    have huniq := succLimitRecursion_value_existsUnique
      (a₀ := a) (S := OrdinalAddSuccStep)
      ordinalAddSuccStep_definable ordinalAddSuccStep_functionLike δ hδord
    exact huniq.unique hyδTRV (ordinalAddValue_isRecursionValue a δ hδord)
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
  IsOrdinal.ordinalAddValue α.val β.val β.ordinal

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

/-- Successor-step relation for right-multiplication by `a`: `y = x + a`. -/
def OrdinalMulSuccStep (a x y : V) : Prop := y = ordinalAddValueTotal x a

lemma ordinalMulSuccStep_definable (a : V) :
    ℒₛₑₜ-relation[V] (OrdinalMulSuccStep a) := by
  simpa [OrdinalMulSuccStep] using ordinalAddValueTotal_eq_definable_left (b := a)

lemma ordinalMulSuccStep_definable_varLeft :
    ℒₛₑₜ-relation₃[V] (fun a x y ↦ OrdinalMulSuccStep a x y) := by
  letI : ℒₛₑₜ-relation₃[V] (fun a b y ↦ y = ordinalAddValueTotal a b) :=
    ordinalAddValueTotal_eq_definable_varInit
  simpa [OrdinalMulSuccStep] using
    (Language.DefinableRel₃.comp
      (P := fun a b y ↦ y = ordinalAddValueTotal a b)
      (f₁ := fun v : Fin 3 → V ↦ v 1)
      (f₂ := fun v : Fin 3 → V ↦ v 0)
      (f₃ := fun v : Fin 3 → V ↦ v 2)
      (by infer_instance) (by infer_instance) (by infer_instance))

lemma ordinalMulSuccStep_functionLike (a : V) :
    ∀ x : V, ∃! y : V, OrdinalMulSuccStep a x y := by
  intro x
  refine ⟨ordinalAddValueTotal x a, rfl, ?_⟩
  intro y hy
  simpa [OrdinalMulSuccStep] using hy

lemma ordinalMulSuccStep_strict_of_pos
    (a : V) (ha : IsOrdinal a) (ha0 : (0 : V) ∈ a) :
    ∀ x y : V, OrdinalMulSuccStep a x y → x ∈ y := by
  intro x y hxy
  rcases hxy with rfl
  have hx0 : ordinalAddValue x 0 (inferInstance : IsOrdinal (0 : V)) = x := ordinalAddValue_zero x
  have hxlt : ordinalAddValue x 0 (inferInstance : IsOrdinal (0 : V)) ∈ ordinalAddValue x a ha :=
    ordinalAddValue_strictIncreasing_right (a := x) (hγ := ha) (hβγ := ha0)
  simpa [ordinalAddValueTotal, ha, hx0] using hxlt

/--
Set-level ordinal multiplication value (as recursion in the right argument):
base value `0`, successor step `x ↦ x + a` (with `a` on the right), and limit step `⋃ˢ range`.
-/
noncomputable def ordinalMulValue (a b : V) (hb : IsOrdinal b) : V :=
  Classical.choose! (succLimitRecursion_value_existsUnique
    (a₀ := (0 : V)) (S := OrdinalMulSuccStep a)
    (ordinalMulSuccStep_definable a) (ordinalMulSuccStep_functionLike a) b hb)

/--
Totalized version of `ordinalMulValue` without an ordinality hypothesis.
If `b` is not ordinal, return an arbitrary fallback value (`a`).
-/
noncomputable def ordinalMulValueTotal (a b : V) : V := by
  classical
  by_cases hb : IsOrdinal b
  · exact ordinalMulValue a b hb
  · exact a

@[simp] lemma ordinalMulValueTotal_of_isOrdinal (a b : V) (hb : IsOrdinal b) :
    ordinalMulValueTotal a b = ordinalMulValue a b hb := by
  simp [ordinalMulValueTotal, hb]

@[simp] lemma ordinalMulValueTotal_of_not_isOrdinal (a b : V) (hb : ¬IsOrdinal b) :
    ordinalMulValueTotal a b = a := by
  simp [ordinalMulValueTotal, hb]

lemma ordinalMulValue_isRecursionValue (a b : V) (hb : IsOrdinal b) :
    IsTransfiniteRecursionValue (SuccLimitRecursionRule (0 : V) (OrdinalMulSuccStep a)) b
      (ordinalMulValue a b hb) :=
  Classical.choose!_spec (succLimitRecursion_value_existsUnique
    (a₀ := (0 : V)) (S := OrdinalMulSuccStep a)
    (ordinalMulSuccStep_definable a) (ordinalMulSuccStep_functionLike a) b hb)

lemma ordinalMulValue_eq_iff_isRecursionValue
    (a b y : V) (hb : IsOrdinal b) :
    y = ordinalMulValue a b hb ↔
      IsTransfiniteRecursionValue (SuccLimitRecursionRule (0 : V) (OrdinalMulSuccStep a)) b y := by
  constructor
  · intro hy
    simpa [hy] using ordinalMulValue_isRecursionValue a b hb
  · intro hy
    have huniq := succLimitRecursion_value_existsUnique
      (a₀ := (0 : V)) (S := OrdinalMulSuccStep a)
      (ordinalMulSuccStep_definable a) (ordinalMulSuccStep_functionLike a) b hb
    exact huniq.unique hy (ordinalMulValue_isRecursionValue a b hb)

lemma ordinalMulValueTotal_eq_iff_recursion_or_fallback
    (a b y : V) :
    y = ordinalMulValueTotal a b ↔
      (IsOrdinal b ∧
        IsTransfiniteRecursionValue (SuccLimitRecursionRule (0 : V) (OrdinalMulSuccStep a)) b y) ∨
      (¬IsOrdinal b ∧ y = a) := by
  classical
  by_cases hb : IsOrdinal b
  · constructor
    · intro hy
      left
      refine ⟨hb, ?_⟩
      have : y = ordinalMulValue a b hb := by
        simpa [ordinalMulValueTotal, hb] using hy
      exact (ordinalMulValue_eq_iff_isRecursionValue a b y hb).1 this
    · rintro (⟨-, hy⟩ | hfalse)
      · have : y = ordinalMulValue a b hb :=
          (ordinalMulValue_eq_iff_isRecursionValue a b y hb).2 hy
        simpa [ordinalMulValueTotal, hb] using this
      · exact (hfalse.1 hb).elim
  · constructor
    · intro hy
      right
      exact ⟨hb, by simpa [ordinalMulValueTotal, hb] using hy⟩
    · rintro (hfalse | ⟨-, hy⟩)
      · exact (hb hfalse.1).elim
      · simpa [ordinalMulValueTotal, hb] using hy

lemma ordinalMulValueTotal_eq_definable (a : V) :
    ℒₛₑₜ-relation[V] (fun b y ↦ y = ordinalMulValueTotal a b) := by
  let R : V → V → Prop := fun b y ↦
    (IsOrdinal b ∧
      IsTransfiniteRecursionValue (SuccLimitRecursionRule (0 : V) (OrdinalMulSuccStep a)) b y) ∨
    (¬IsOrdinal b ∧ y = a)
  have hTRVdef : ℒₛₑₜ-relation[V]
      (IsTransfiniteRecursionValue (SuccLimitRecursionRule (0 : V) (OrdinalMulSuccStep a))) := by
    exact isTransfiniteRecursionValue_definable
      (φ := SuccLimitRecursionRule (0 : V) (OrdinalMulSuccStep a))
      (succLimitRecursionRule_definable
        (a₀ := (0 : V)) (S := OrdinalMulSuccStep a) (ordinalMulSuccStep_definable a))
  have hR : ℒₛₑₜ-relation[V] R := by
    letI : ℒₛₑₜ-relation[V]
      (IsTransfiniteRecursionValue (SuccLimitRecursionRule (0 : V) (OrdinalMulSuccStep a))) := hTRVdef
    change ℒₛₑₜ-relation[V] (fun b y ↦
      (IsOrdinal b ∧
        IsTransfiniteRecursionValue (SuccLimitRecursionRule (0 : V) (OrdinalMulSuccStep a)) b y) ∨
      (¬IsOrdinal b ∧ y = a))
    definability
  have hEq :
      (fun b y ↦ y = ordinalMulValueTotal a b) = R := by
    funext b y
    exact propext (ordinalMulValueTotal_eq_iff_recursion_or_fallback a b y)
  rw [hEq]; exact hR

lemma ordinalMulValueTotal_eq_definable_varLeft :
    ℒₛₑₜ-relation₃[V] (fun a b y ↦ y = ordinalMulValueTotal a b) := by
  let R : V → V → V → Prop := fun a b y ↦
    (IsOrdinal b ∧
      IsTransfiniteRecursionValue (SuccLimitRecursionRule (0 : V) (OrdinalMulSuccStep a)) b y) ∨
    (¬IsOrdinal b ∧ y = a)
  have hφdef : ℒₛₑₜ-relation₃[V]
      (fun a r y ↦ SuccLimitRecursionRule (0 : V) (OrdinalMulSuccStep a) r y) := by
    exact succLimitRecursionRule_definable_varStep
      (a₀ := (0 : V)) (S := OrdinalMulSuccStep) ordinalMulSuccStep_definable_varLeft
  have hTRVdef : ℒₛₑₜ-relation₃[V]
      (fun a b y ↦ IsTransfiniteRecursionValue
        (SuccLimitRecursionRule (0 : V) (OrdinalMulSuccStep a)) b y) := by
    exact isTransfiniteRecursionValue_definable_var
      (φ := fun a r y ↦ SuccLimitRecursionRule (0 : V) (OrdinalMulSuccStep a) r y) hφdef
  have hR : ℒₛₑₜ-relation₃[V] R := by
    letI : ℒₛₑₜ-relation₃[V]
      (fun a b y ↦ IsTransfiniteRecursionValue
        (SuccLimitRecursionRule (0 : V) (OrdinalMulSuccStep a)) b y) := hTRVdef
    change ℒₛₑₜ-relation₃[V] (fun a b y ↦
      (IsOrdinal b ∧
        IsTransfiniteRecursionValue
          (SuccLimitRecursionRule (0 : V) (OrdinalMulSuccStep a)) b y) ∨
      (¬IsOrdinal b ∧ y = a))
    definability
  have hEq :
      (fun a b y ↦ y = ordinalMulValueTotal a b) = R := by
    funext a b y
    exact propext (ordinalMulValueTotal_eq_iff_recursion_or_fallback a b y)
  simpa [R, hEq] using hR

lemma ordinalMulValueTotal_eq_definable_left (b : V) :
    ℒₛₑₜ-relation[V] (fun a y ↦ y = ordinalMulValueTotal a b) := by
  letI : ℒₛₑₜ-relation₃[V] (fun a b y ↦ y = ordinalMulValueTotal a b) :=
    ordinalMulValueTotal_eq_definable_varLeft
  simpa using
    (Language.DefinableRel₃.comp
      (P := fun a b y ↦ y = ordinalMulValueTotal a b)
      (f₁ := fun v : Fin 2 → V ↦ v 0)
      (f₂ := fun _ : Fin 2 → V ↦ b)
      (f₃ := fun v : Fin 2 → V ↦ v 1)
      (by infer_instance) (by infer_instance) (by infer_instance))

lemma ordinalMulValue_zero_isRecursionValue :
    IsTransfiniteRecursionValue (SuccLimitRecursionRule (0 : V) (OrdinalMulSuccStep a)) 0 (0 : V) := by
  refine ⟨∅, inferInstance, ?_, ?_, ?_⟩
  · simp [zero_def]
  · intro γ hγ
    simp [zero_def] at hγ
  · exact Or.inl ⟨by simp, rfl⟩

@[simp] lemma ordinalMulValue_zero (a : V) :
    ordinalMulValue a 0 (inferInstance : IsOrdinal (0 : V)) = (0 : V) := by
  have huniq := succLimitRecursion_value_existsUnique
    (a₀ := (0 : V)) (S := OrdinalMulSuccStep a)
    (ordinalMulSuccStep_definable a) (ordinalMulSuccStep_functionLike a)
    0 (inferInstance : IsOrdinal (0 : V))
  exact huniq.unique
    (ordinalMulValue_isRecursionValue a 0 (inferInstance : IsOrdinal (0 : V)))
    (ordinalMulValue_zero_isRecursionValue (a := a))

@[simp] lemma ordinalMulValue_succ (a β : V) (hβ : IsOrdinal β) :
    ordinalMulValue a (succ β) (IsOrdinal.succ (α := β)) =
      ordinalAddValueTotal (ordinalMulValue a β hβ) a := by
  let φ : V → V → Prop := SuccLimitRecursionRule (0 : V) (OrdinalMulSuccStep a)
  have hx : IsTransfiniteRecursionValue φ β (ordinalMulValue a β hβ) :=
    ordinalMulValue_isRecursionValue a β hβ
  have hy : IsTransfiniteRecursionValue φ (succ β)
      (ordinalMulValue a (succ β) (IsOrdinal.succ (α := β))) :=
    ordinalMulValue_isRecursionValue a (succ β) (IsOrdinal.succ (α := β))
  have hstep : OrdinalMulSuccStep a (ordinalMulValue a β hβ)
      (ordinalMulValue a (succ β) (IsOrdinal.succ (α := β))) :=
    succLimitRecursion_successor
      (a₀ := (0 : V)) (S := OrdinalMulSuccStep a) (ordinalMulSuccStep_functionLike a) hβ hx hy
  simpa [OrdinalMulSuccStep] using hstep

lemma ordinalMulValue_strictIncreasing_right_of_left_pos
    (a : V) (ha : IsOrdinal a) (ha0 : (0 : V) ∈ a)
    (hStepExtend : ∀ u x y : V, u ∈ x → OrdinalMulSuccStep a x y → u ∈ y)
    {β γ : V} (hγ : IsOrdinal γ) (hβγ : β ∈ γ) :
    ordinalMulValue a β (IsOrdinal.of_mem hβγ) ∈ ordinalMulValue a γ hγ := by
  let φ : V → V → Prop := SuccLimitRecursionRule (0 : V) (OrdinalMulSuccStep a)
  have hφfun : ∀ r : V, IsFunction r → ∃! y : V, φ r y :=
    succLimitRecursionRule_functionLike (0 : V) (OrdinalMulSuccStep a) (ordinalMulSuccStep_functionLike a)
  have hφdef : ℒₛₑₜ-relation[V] φ :=
    succLimitRecursionRule_definable (0 : V) (OrdinalMulSuccStep a) (ordinalMulSuccStep_definable a)
  have hR : ℒₛₑₜ-relation[V] (fun δ f ↦
      IsFunction f ∧ domain f = δ ∧
      ∀ ξ ∈ δ, ∃ z, ⟨ξ, z⟩ₖ ∈ f ∧ φ (f ↾ ξ) z) := by
    letI : ℒₛₑₜ-relation[V] φ := hφdef
    definability
  let α := succ γ
  have hα : IsOrdinal α := IsOrdinal.succ (α := γ)
  rcases transfinite_recursion_function_exists (φ := φ) hφfun hR α hα with
    ⟨F, hFfunc, hFdom, hFex⟩
  letI : IsOrdinal α := hα
  letI : IsFunction F := hFfunc
  have hFrec : ∀ ξ ∈ α, ∀ y, ⟨ξ, y⟩ₖ ∈ F ↔ φ (F ↾ ξ) y :=
    transfinite_recursion_iff_of_exists (φ := φ) hφfun hFex
  let hFtr : IsTransfiniteRecursionFunction φ α F := ⟨hα, hFfunc, hFdom, hFrec⟩
  have hβα : β ∈ α := hα.toIsTransitive.transitive γ (by simp [α]) β hβγ
  have hγα : γ ∈ α := by simp [α]
  rcases mem_domain_iff.mp (by rw [hFdom]; exact hβα) with ⟨x, hβxF⟩
  rcases mem_domain_iff.mp (by rw [hFdom]; exact hγα) with ⟨y, hγyF⟩
  have hβord : IsOrdinal β := IsOrdinal.of_mem hβγ
  have hxφ : φ (F ↾ β) x := (hFrec β hβα x).1 hβxF
  have hxTRV : IsTransfiniteRecursionValue φ β x :=
    (isTransfiniteRecursionValue_iff_exists_isTransfiniteRecursionFunction
      (φ := φ) hφfun (hα := hβord)).2 ⟨F ↾ β, by
        have hβ_sub_α : β ⊆ α := hα.toIsTransitive.transitive _ hβα
        refine ⟨hβord, IsFunction.restrict _ _, ?_, ?_⟩
        · simp [hFdom, domain_restrict_eq, hβ_sub_α]
        · intro ξ hξβ y'
          have hξα : ξ ∈ α := hβ_sub_α _ hξβ
          have hξ_sub_β : ξ ⊆ β := hβord.toIsTransitive.transitive _ hξβ
          rw [kpair_mem_restrict_iff, restrict_restrict_of_subset hξ_sub_β, hFrec ξ hξα y']
          simp [hξβ], hxφ⟩
  have hyφ : φ (F ↾ γ) y := (hFrec γ hγα y).1 hγyF
  have hyTRV : IsTransfiniteRecursionValue φ γ y :=
    (isTransfiniteRecursionValue_iff_exists_isTransfiniteRecursionFunction
      (φ := φ) hφfun (hα := hγ)).2 ⟨F ↾ γ, by
        have hγ_sub_α : γ ⊆ α := hα.toIsTransitive.transitive _ hγα
        refine ⟨hγ, IsFunction.restrict _ _, ?_, ?_⟩
        · simp [hFdom, domain_restrict_eq, hγ_sub_α]
        · intro ξ hξγ y'
          have hξα : ξ ∈ α := hγ_sub_α _ hξγ
          have hξ_sub_γ : ξ ⊆ γ := hγ.toIsTransitive.transitive _ hξγ
          rw [kpair_mem_restrict_iff, restrict_restrict_of_subset hξ_sub_γ, hFrec ξ hξα y']
          simp [hξγ], hyφ⟩
  have hxeq : x = ordinalMulValue a β hβord := by
    have huniq := succLimitRecursion_value_existsUnique
      (a₀ := (0 : V)) (S := OrdinalMulSuccStep a)
      (ordinalMulSuccStep_definable a) (ordinalMulSuccStep_functionLike a) β hβord
    exact huniq.unique hxTRV (ordinalMulValue_isRecursionValue a β hβord)
  have hyeq : y = ordinalMulValue a γ hγ := by
    have huniq := succLimitRecursion_value_existsUnique
      (a₀ := (0 : V)) (S := OrdinalMulSuccStep a)
      (ordinalMulSuccStep_definable a) (ordinalMulSuccStep_functionLike a) γ hγ
    exact huniq.unique hyTRV (ordinalMulValue_isRecursionValue a γ hγ)
  have hInc : IsStrictIncreasingOrdinalGraph F :=
    succLimitRecursion_strictIncreasing
      (a₀ := (0 : V)) (S := OrdinalMulSuccStep a)
      (ordinalMulSuccStep_strict_of_pos a ha ha0) hStepExtend hFtr
  have hxy : x ∈ y := hInc.2 β γ x y hβγ hβxF hγyF
  rwa [hxeq, hyeq] at hxy

lemma ordinalMulValue_exists_right_mul_add_eq_of_pos
    (a γ : V) (ha : IsOrdinal a) (ha0 : (0 : V) ∈ a) (hγ : IsOrdinal γ)
    (hStepExtend : ∀ u x y : V, u ∈ x → OrdinalMulSuccStep a x y → u ∈ y) :
    ∃ δ ρ : Ordinal V,
      ordinalAddValue (ordinalMulValue a δ.val δ.ordinal) ρ.val ρ.ordinal = γ ∧
      ρ.val ∈ a := by
  let φ : V → V → Prop := SuccLimitRecursionRule (0 : V) (OrdinalMulSuccStep a)
  have hφfun : ∀ r : V, IsFunction r → ∃! y : V, φ r y :=
    succLimitRecursionRule_functionLike (0 : V) (OrdinalMulSuccStep a) (ordinalMulSuccStep_functionLike a)
  have hφdef : ℒₛₑₜ-relation[V] φ :=
    succLimitRecursionRule_definable (0 : V) (OrdinalMulSuccStep a) (ordinalMulSuccStep_definable a)
  have hR : ℒₛₑₜ-relation[V] (fun β f ↦
      IsFunction f ∧ domain f = β ∧
      ∀ ξ ∈ β, ∃ z, ⟨ξ, z⟩ₖ ∈ f ∧ φ (f ↾ ξ) z) := by
    letI : ℒₛₑₜ-relation[V] φ := hφdef
    definability
  let α := succ (succ γ)
  have hα : IsOrdinal α := IsOrdinal.succ
  rcases transfinite_recursion_function_exists (φ := φ) hφfun hR α hα with
    ⟨f, hfFunc, hfDom, hfEx⟩
  letI : IsOrdinal α := hα
  letI : IsFunction f := hfFunc
  have hfRec : ∀ ξ ∈ α, ∀ y, ⟨ξ, y⟩ₖ ∈ f ↔ φ (f ↾ ξ) y :=
    transfinite_recursion_iff_of_exists (φ := φ) hφfun hfEx
  let hrec : IsTransfiniteRecursionFunction φ α f := ⟨hα, hfFunc, hfDom, hfRec⟩
  have hstrict : IsStrictIncreasingOrdinalGraph f :=
    succLimitRecursion_strictIncreasing
      (a₀ := (0 : V)) (S := OrdinalMulSuccStep a)
      (ordinalMulSuccStep_strict_of_pos a ha ha0) hStepExtend hrec
  have hValOrd : ∀ β y, β ∈ α → ⟨β, y⟩ₖ ∈ f → IsOrdinal y :=
    succLimitRecursion_stageValue_isOrdinal
      (a₀ := (0 : V)) (S := OrdinalMulSuccStep a) (by infer_instance)
      (by
        intro x y hxord hxy
        rcases hxy with rfl
        simpa [ordinalAddValueTotal, ha] using ordinalAddValue_isOrdinal x a hxord ha)
      hrec
  have hstrictRelTotal :
      ∀ β γ yβ yγ : V, IsOrdinal β → IsOrdinal γ → β ∈ γ →
        (yβ = ordinalMulValueTotal a β) → (yγ = ordinalMulValueTotal a γ) → yβ ∈ yγ := by
    intro β' γ' yβ yγ hβ hγ' hβγ hyβ hyγ
    rcases hyβ with rfl
    rcases hyγ with rfl
    have hlt : ordinalMulValue a β' hβ ∈ ordinalMulValue a γ' hγ' :=
      ordinalMulValue_strictIncreasing_right_of_left_pos
        (a := a) (ha := ha) (ha0 := ha0) (hStepExtend := hStepExtend)
        (hγ := hγ') (hβγ := hβγ)
    simpa [ordinalMulValueTotal, hβ, hγ'] using hlt
  have hself : ∀ β y, β ∈ α → ⟨β, y⟩ₖ ∈ f → β ⊆ y := by
    intro β y hβα hβy
    have hβord : IsOrdinal β := IsOrdinal.of_mem hβα
    have hyord : IsOrdinal y := hValOrd β y hβα hβy
    have hyφ : φ (f ↾ β) y := (hfRec β hβα y).1 hβy
    have hyTRV : IsTransfiniteRecursionValue φ β y :=
      (isTransfiniteRecursionValue_iff_exists_isTransfiniteRecursionFunction
        (φ := φ) hφfun (hα := hβord)).2 ⟨f ↾ β, by
          have hβsubα : β ⊆ α := hα.toIsTransitive.transitive _ hβα
          refine ⟨hβord, IsFunction.restrict _ _, ?_, ?_⟩
          · simp [hfDom, domain_restrict_eq, hβsubα]
          · intro ξ hξβ y'
            have hξα : ξ ∈ α := hβsubα _ hξβ
            have hξsubβ : ξ ⊆ β := hβord.toIsTransitive.transitive _ hξβ
            rw [kpair_mem_restrict_iff, restrict_restrict_of_subset hξsubβ, hfRec ξ hξα y']
            simp [hξβ], hyφ⟩
    have hyeqMul : y = ordinalMulValue a β hβord := by
      have huniq := succLimitRecursion_value_existsUnique
        (a₀ := (0 : V)) (S := OrdinalMulSuccStep a)
        (ordinalMulSuccStep_definable a) (ordinalMulSuccStep_functionLike a) β hβord
      exact huniq.unique hyTRV (ordinalMulValue_isRecursionValue a β hβord)
    have hyeqTot : y = ordinalMulValueTotal a β := by
      simpa [ordinalMulValueTotal, hβord] using hyeqMul
    have hnot : ¬ y ∈ β := by
      intro hyβ
      have hnotTot := strictIncreasing_relation_no_value_lt_self
        (R := fun x y ↦ y = ordinalMulValueTotal a x)
        (hRdef := ordinalMulValueTotal_eq_definable a)
        (hRfun := by intro x; exact ⟨ordinalMulValueTotal a x, rfl, by intro y hy; simpa using hy⟩)
        (hRstrict := hstrictRelTotal)
        β (ordinalMulValueTotal a β) hβord rfl
      exact hnotTot (by simpa [hyeqTot] using hyβ)
    letI : IsOrdinal β := hβord
    letI : IsOrdinal y := hyord
    rcases IsOrdinal.mem_trichotomy (α := y) (β := β) with (hyβ | hEq | hβy)
    · exact (hnot hyβ).elim
    · simp [hEq]
    · exact (IsOrdinal.subset_iff (α := β) (β := y)).2 (Or.inr hβy)
  have hsuccγα : succ γ ∈ α := by simp [α]
  rcases succLimitRecursion_exists_max_stage_le
      (a₀ := (0 : V)) (S := OrdinalMulSuccStep a)
      (hrec := hrec) (hstrict := hstrict) (hValOrd := hValOrd) (hself := hself)
      (hξord := hγ) (ha₀le := empty_subset γ) (hsuccξα := hsuccγα) with
    ⟨δ, yδ, hδα, hδyδ, hyδleγ, hmax⟩
  have hδord : IsOrdinal δ := IsOrdinal.of_mem hδα
  have hyδord : IsOrdinal yδ := hValOrd δ yδ hδα hδyδ
  rcases ordinalAddValue_exists_right_eq_of_subset yδ γ hyδord hγ hyδleγ with
    ⟨ρ, hρeq⟩
  have hρord : IsOrdinal ρ.val := ρ.ordinal
  by_cases hρlt : ρ.val ∈ a
  · have hyδφ : φ (f ↾ δ) yδ := (hfRec δ hδα yδ).1 hδyδ
    have hyδTRV : IsTransfiniteRecursionValue φ δ yδ :=
      (isTransfiniteRecursionValue_iff_exists_isTransfiniteRecursionFunction
        (φ := φ) hφfun (hα := hδord)).2 ⟨f ↾ δ, by
          have hδsubα : δ ⊆ α := hα.toIsTransitive.transitive _ hδα
          refine ⟨hδord, IsFunction.restrict _ _, ?_, ?_⟩
          · simp [hfDom, domain_restrict_eq, hδsubα]
          · intro ξ hξδ y'
            have hξα : ξ ∈ α := hδsubα _ hξδ
            have hξsubδ : ξ ⊆ δ := hδord.toIsTransitive.transitive _ hξδ
            rw [kpair_mem_restrict_iff, restrict_restrict_of_subset hξsubδ, hfRec ξ hξα y']
            simp [hξδ], hyδφ⟩
    have hyδeqMul : yδ = ordinalMulValue a δ hδord := by
      have huniq := succLimitRecursion_value_existsUnique
        (a₀ := (0 : V)) (S := OrdinalMulSuccStep a)
        (ordinalMulSuccStep_definable a) (ordinalMulSuccStep_functionLike a) δ hδord
      exact huniq.unique hyδTRV (ordinalMulValue_isRecursionValue a δ hδord)
    refine ⟨⟨δ, hδord⟩, ρ, ?_, hρlt⟩
    simpa [hyδeqMul] using hρeq
  · have ha_sub_ρ : a ⊆ ρ.val := by
      letI : IsOrdinal a := ha
      letI : IsOrdinal ρ.val := hρord
      rcases IsOrdinal.mem_trichotomy (α := ρ.val) (β := a) with (hρa | hEq | haρ)
      · exact (hρlt hρa).elim
      · simp [hEq]
      · exact hρord.toIsTransitive.transitive _ haρ
    have hsuccδ_in_α : succ δ ∈ α := by
      have hδ_sub_γ : δ ⊆ γ := subset_trans (hself δ yδ hδα hδyδ) hyδleγ
      letI : IsOrdinal δ := hδord
      letI : IsOrdinal γ := hγ
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
    rcases mem_domain_iff.mp (by rw [hfDom]; exact hsuccδ_in_α) with ⟨yS, hsuccδyS⟩
    have hySrule : φ (f ↾ (succ δ)) yS := (hfRec (succ δ) hsuccδ_in_α yS).1 hsuccδyS
    have hdom_succδ : domain (f ↾ (succ δ)) = succ δ := by
      simp [domain_restrict_eq, hfDom, inter_eq_right_of_subset hsucc_sub_α]
    have hyS_eq_add : yS = ordinalAddValueTotal yδ a := by
      rcases hySrule with (h0 | hs | hL)
      · have : succ δ = (∅ : V) := by simpa [hdom_succδ] using h0.1
        have hδsucc : δ ∈ succ δ := by simp
        rw [this] at hδsucc
        exact (not_mem_empty hδsucc).elim
      · rcases hs with ⟨δ', x, hdom', hδ'x, hxyS⟩
        have hdom_eq : succ δ' = succ δ := by simpa [hdom_succδ] using hdom'.symm
        have hδ' : δ' = δ := succ_inj hdom_eq
        rw [hδ'] at hδ'x
        have hδx : ⟨δ, x⟩ₖ ∈ f := (kpair_mem_restrict_iff.mp hδ'x).1
        have hx_eq : x = yδ := IsFunction.unique hδx hδyδ
        subst hx_eq
        simpa [OrdinalMulSuccStep] using hxyS
      · exact (hL.2.1 δ (by simp [hdom_succδ])).elim
    have hyS_sub_γ : yS ⊆ γ := by
      have hyδ_add_a_sub :
          ordinalAddValue yδ a ha ⊆ ordinalAddValue yδ ρ.val hρord := by
        exact ordinalAddValue_subset_right_of_initOrdinal yδ a ρ.val hyδord ha hρord ha_sub_ρ
      have : ordinalAddValueTotal yδ a ⊆ γ := by
        simpa [ordinalAddValueTotal, ha, hρeq] using hyδ_add_a_sub
      simpa [hyS_eq_add] using this
    have hsuccδ_sub_δ : succ δ ⊆ δ := hmax (succ δ) yS hsuccδ_in_α hsuccδyS hyS_sub_γ
    have : δ ∈ δ := hsuccδ_sub_δ _ (by simp)
    exact (mem_irrefl δ this).elim

end ordinalMultiplication

end IsOrdinal

namespace Ordinal

variable [V ⊧ₘ* 𝗭𝗙]

/-- Current set-level value of ordinal multiplication. -/
noncomputable def mulValue (α β : Ordinal V) : V :=
  IsOrdinal.ordinalMulValue α.val β.val β.ordinal

@[simp] lemma mulValue_bot (α : Ordinal V) : mulValue α ⊥ = (0 : V) := by
  simp only [mulValue, bot_val_eq]
  exact IsOrdinal.ordinalMulValue_zero (a := α.val)

@[simp] lemma mulValue_succ (α β : Ordinal V) :
    mulValue α β.succ = IsOrdinal.ordinalAddValueTotal (mulValue α β) α.val := by
  simp [mulValue, succ_val]

variable [V ⊧ₘ* 𝗭𝗙]

end Ordinal

end LO.FirstOrder.SetTheory
