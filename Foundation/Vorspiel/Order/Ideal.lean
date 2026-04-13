
module

public import Mathlib.Order.Ideal
public import Mathlib.Order.PFilter
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Order.PrimeIdeal

@[expose] public section

namespace Order

namespace Ideal

variable {P : Type*}

section semilatticeSup

variable [SemilatticeSup P] [OrderBot P]

lemma sSup_def (s : Set (Ideal P)) : sSup s = sInf (upperBounds s) := rfl

lemma iSup_def (I : ι → Ideal P) : ⨆ i, I i = sInf (upperBounds (Set.range I)) := rfl

@[simp] lemma mem_bot {x : P} : x ∈ (⊥ : Ideal P) ↔ x = ⊥ := le_bot_iff

theorem mem_finsup_principal [DecidableEq ι] {s : Finset ι} {f : ι → P} :
    x ∈ s.sup (principal ∘ f) ↔ x ≤ s.sup f := by
  induction s using Finset.induction generalizing x
  · simp
  case insert i s hi ih =>
    suffices (∃ y ≤ f i, ∃ z ≤ s.sup f, x ≤ y ⊔ z) ↔ x ≤ f i ⊔ s.sup f by
      simpa [ih]
    constructor
    · rintro ⟨y, hy, z, hz, h⟩
      refine le_trans h (sup_le_sup hy hz)
    · intro h
      exact ⟨f i, le_refl _, s.sup f, le_refl _, h⟩

lemma mem_iSup_iff [DecidableEq ι] {I : ι → Ideal P} {x : P} :
    x ∈ ⨆ i, I i ↔ ∃ u : Finset ι, x ∈ u.sup I := by
  revert x
  let K : Ideal P := {
    carrier := { x | ∃ u : Finset ι, x ∈ u.sup I }
    lower' x y hyx := by
      rintro ⟨u, hx⟩
      exact ⟨u, (u.sup I).lower hyx hx⟩
    nonempty' := ⟨⊥, ∅, by simp⟩
    directed' := by
      rintro x ⟨u, hu⟩ y ⟨v, hv⟩
      refine ⟨x ⊔ y, ⟨u ∪ v, ?_⟩, ?_⟩
      · simpa [Finset.sup_union]
        using ⟨⟨x, hu, y, hv, by simp⟩, ⟨x, hu, y, hv, by simp⟩⟩
      · simp }
  have mem_K_iff x : x ∈ K ↔ ∃ u : Finset ι, x ∈ u.sup I := by rfl
  suffices K = ⨆ i, I i by simp [←this, mem_K_iff]
  apply le_antisymm
  · intro x hx
    rcases hx with ⟨u, hxu⟩
    suffices ∀ J, (∀ i, I i ≤ J) → x ∈ J by simpa [iSup_def, upperBounds]
    intro J hJ
    have : u.sup I ≤ J := by simp [hJ]
    exact this hxu
  · suffices ∀ i, I i ≤ K by simpa [upperBounds]
    intro i x hx
    refine ⟨{i}, by simpa using hx⟩

end semilatticeSup

section completeSemilatticeSup

variable [CompleteSemilatticeSup P]

theorem sSup_mem {s : Set P} {I : Ideal P} :
    sSup s ∈ I → ∀ x ∈ s, x ∈ I := fun h _ hx ↦
  I.lower (le_sSup_iff.mpr fun _ a ↦ a hx) h

end completeSemilatticeSup

end Ideal

namespace Ideal.IsProper

variable {P : Type*} [SemilatticeSup P]

lemma iff_top_not_mem [OrderTop P] {I : Ideal P} : I.IsProper ↔ ⊤ ∉ I := by
  constructor
  · intro h ht
    have : (I : Set P) = Set.univ := by
      ext x
      suffices x ∈ I by simpa
      exact I.lower (show x ≤ ⊤ by simp) ht
    exact h.ne_univ this
  · intro hn
    refine ⟨?_⟩
    intro e
    have : ⊤ ∈ I :=
      SetLike.mem_coe.mp <| by rw [e]; simp
    contradiction

@[simp] lemma top_not_mem [OrderTop P] (I : Ideal P) [I.IsProper] : ⊤ ∉ I :=
  iff_top_not_mem.mp inferInstance

end Ideal.IsProper

namespace Ideal.PrimePair

variable {P : Type*}

open IsPrime

section booleanAlgebra

section basic

variable [Preorder P] (IF : PrimePair P)

lemma not_mem_F_iff_mem_I {x : P} :
    x ∉ IF.F ↔ x ∈ IF.I := by
  have : x ∈ IF.I ∨ x ∈ IF.F := by simpa using Set.ext_iff.mp IF.I_union_F x
  have : x ∈ IF.I → x ∉ IF.F := @Set.disjoint_left.mp IF.disjoint x
  tauto

lemma not_mem_I_iff_mem_F {x : P} :
    x ∉ IF.I ↔ x ∈ IF.F := by
  have : x ∈ IF.I ∨ x ∈ IF.F := by simpa using Set.ext_iff.mp IF.I_union_F x
  have : x ∈ IF.F → x ∉ IF.I := @Set.disjoint_right.mp IF.disjoint x
  tauto

abbrev IsProper : Prop := IF.I.IsProper

instance i_isProper (IF : PrimePair P) [IF.IsProper] : IF.I.IsProper := inferInstance

instance : IF.I.IsPrime := I_isPrime IF

end basic

variable [BooleanAlgebra P] {IF : PrimePair P}

lemma mem_or_compl_mem_I (x : P) : x ∈ IF.I ∨ xᶜ ∈ IF.I :=
  IF.I_isPrime.mem_or_compl_mem

lemma mem_or_compl_mem_F (x : P) : x ∈ IF.F ∨ xᶜ ∈ IF.F := by
  by_contra!
  have hx : x ∈ IF.I := by simpa [not_mem_F_iff_mem_I] using this.1
  have hxc : xᶜ ∈ IF.I := by simpa [not_mem_F_iff_mem_I] using this.2
  have : ⊤ ∈ IF.I := by simpa using Order.Ideal.sup_mem hx hxc
  have : ⊤ ∉ IF.I := Ideal.IsProper.top_not_mem IF.I
  contradiction

lemma compl_mem_I_iff_mem_F :
    xᶜ ∈ IF.I ↔ x ∈ IF.F := by
  constructor
  · have : x ∈ IF.F ∨ xᶜ ∉ IF.I := by simpa [not_mem_I_iff_mem_F] using mem_or_compl_mem_F x
    tauto
  · have : x ∉ IF.F ∨ xᶜ ∈ IF.I := by simpa [not_mem_F_iff_mem_I] using mem_or_compl_mem_I x
    tauto

lemma compl_mem_F_iff_mem_I :
    xᶜ ∈ IF.F ↔ x ∈ IF.I := by
  simpa using (compl_mem_I_iff_mem_F (x := xᶜ)).symm

@[simp] lemma inf_mem_I_iff {x y : P} :
    x ⊓ y ∈ IF.I ↔ x ∈ IF.I ∨ y ∈ IF.I := by
  constructor
  · exact mem_or_mem (I_isPrime IF)
  · rintro (h | h)
    · exact IF.I.lower (by simp) h
    · exact IF.I.lower (by simp) h

@[simp] lemma sup_mem_F_iff {x y : P} :
    x ⊔ y ∈ IF.F ↔ x ∈ IF.F ∨ y ∈ IF.F := by
  simp [←compl_mem_I_iff_mem_F]

@[simp] lemma himp_mem_F_iff {x y : P} :
    x ⇨ y ∈ IF.F ↔ (x ∈ IF.F → y ∈ IF.F) := by
  simp [himp_eq, compl_mem_F_iff_mem_I, ←not_mem_F_iff_mem_I]
  tauto

end booleanAlgebra

section completeBooleanAlgebra

variable [CompleteBooleanAlgebra P] {IF : PrimePair P}

lemma iSup_mem_iff {f : ι → P} :
    ⨆ i, f i ∈ IF.I ↔ ∀ i, f i ∈ IF.I := by
  constructor
  · intro h i
    exact IF.I.lower (le_iSup f i) h
  · intro h
    by_contra! hf
    

lemma iInf_mem_iff {f : ι → P} :
    ⨅ i, f i ∈ IF.I ↔ ∃ i, f i ∈ IF.I := by
  constructor
  · intro h
    by_contra! hf


end completeBooleanAlgebra

end Ideal.IsPrime




end Order
