module

public import Foundation.FirstOrder.SetTheory.Z

@[expose] public section
/-!
# Ordinals and transitive sets

reference: Ralf Schindler, "Set Theory, Exploring Independence and Truth" [Sch14]
-/

namespace LO.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V ⊧ₘ* 𝗭]

/-! ### Transitive set -/

class IsTransitive (x : V) : Prop where
  transitive : ∀ y ∈ x, y ⊆ x

omit [Nonempty V] [V ⊧ₘ* 𝗭] in
lemma isTransitive_def {x : V} : IsTransitive x ↔ ∀ y ∈ x, y ⊆ x :=
  ⟨fun h ↦ h.transitive, fun h ↦ ⟨h⟩⟩

def IsTransitive.dfn : SetTheorySemisentence 1 := “x. ∀ y ∈ x, y ⊆ x”

instance IsTransitive.defined : ℒₛₑₜ-predicate[V] IsTransitive via IsTransitive.dfn :=
  ⟨fun v ↦ by simp [IsTransitive.dfn, isTransitive_def]⟩

instance IsTransitive.definable : ℒₛₑₜ-predicate[V] IsTransitive := IsTransitive.defined.to_definable

namespace IsTransitive

omit [Nonempty V] [V ⊧ₘ* 𝗭] in
lemma mem_trans {x y z : V} (H : IsTransitive z) (hxy : x ∈ y) (hyz : y ∈ z) : x ∈ z := H.transitive y hyz x hxy

@[simp] protected instance empty : IsTransitive (∅ : V) := ⟨fun x ↦ by simp⟩

lemma succ {x : V} (h : IsTransitive x) : IsTransitive (succ x) := ⟨by
  intro y hy
  rcases show y = x ∨ y ∈ x by simpa [mem_succ_iff] using hy with (rfl | hy)
  · simp
  · exact subset_trans (h.transitive y hy) (by simp)⟩

@[simp] lemma nat : x ∈ (ω : V) → IsTransitive x := by
  apply naturalNumber_induction
  · definability
  case zero =>
    simp [zero_def]
  case succ =>
    intro x hx ih
    exact ih.succ

lemma union {x y : V} [hx : IsTransitive x] [hy : IsTransitive y] : IsTransitive (x ∪ y) := ⟨by
  simp only [mem_union_iff]
  rintro z (hzx | hzy)
  · exact subset_trans (hx.transitive z hzx) (by simp)
  · exact subset_trans (hy.transitive z hzy) (by simp)⟩

lemma sUnion {X : V} (h : ∀ x ∈ X, IsTransitive x) : IsTransitive (⋃ˢ X) := ⟨by
  intro x hx
  have : ∃ y ∈ X, x ∈ y := by simpa [mem_sUnion_iff] using hx
  rcases this with ⟨y, hyX, hxy⟩
  exact subset_trans ((h y hyX).transitive x hxy) (subset_sUnion_of_mem hyX)⟩

lemma sInter {X : V} (h : ∀ x ∈ X, IsTransitive x) : IsTransitive (⋂ˢ X) := by
  rcases eq_empty_or_isNonempty X with (rfl | hX)
  · simp
  refine ⟨?_⟩
  intro y hy
  apply subset_sInter_iff_of_nonempty.mpr
  intro z hzX
  have : y ∈ z := mem_sInter_iff_of_nonempty.mp hy z hzX
  exact (h z hzX).transitive y this

/-
@[simp] lemma IsTransitive.ω : IsTransitive (ω : V) := by
  intro x hx
  induction x using naturalNumber_induction
  · definability
  case zero =>
    simp [zero_def]
  case succ x hx' ih =>
    intro z hz
    rcases show z = x ∨ z ∈ x by simpa using hz with (rfl | hz)
    · exact hx'
    · exact ih hx' z hz
-/

@[simp] protected instance ω : IsTransitive (ω : V) := ⟨by
  apply naturalNumber_induction
  · definability
  case zero =>
    simp [zero_def]
  case succ =>
    intro x hx ih z hz
    rcases show z = x ∨ z ∈ x by simpa [mem_succ_iff] using hz with (rfl | hz)
    · exact hx
    · exact ih z hz⟩

end IsTransitive

/-! ### Ordinals -/

/-- Neumann ordinal -/
class IsOrdinal (x : V) : Prop extends IsTransitive x where
  trichotomy : ∀ y ∈ x, ∀ z ∈ x, y ∈ z ∨ y = z ∨ z ∈ y

omit [Nonempty V] [V ⊧ₘ* 𝗭] in
lemma isOrdinal_iff {x : V} :
    IsOrdinal x ↔ IsTransitive x ∧ ∀ y ∈ x, ∀ z ∈ x, y ∈ z ∨ y = z ∨ z ∈ y :=
  ⟨fun h ↦ ⟨⟨h.transitive⟩, h.trichotomy⟩, fun h ↦ { transitive := h.1.transitive, trichotomy := h.2 }⟩

def IsOrdinal.dfn : SetTheorySemisentence 1 := “x. !IsTransitive.dfn x ∧ ∀ y ∈ x, ∀ z ∈ x, y ∈ z ∨ y = z ∨ z ∈ y”

instance IsOrdinal.defined : ℒₛₑₜ-predicate[V] IsOrdinal via IsOrdinal.dfn := ⟨fun δ ↦ by simp [isOrdinal_iff, dfn]⟩

instance IsOrdinal.definable : ℒₛₑₜ-predicate[V] IsOrdinal := IsOrdinal.defined.to_definable

namespace IsOrdinal

variable {α β γ : V}

lemma of_mem [h : IsOrdinal α] (lt : β ∈ α) : IsOrdinal β where
  transitive γ hzy δ hvz := by
    have hzx : γ ∈ α := h.transitive _ lt _ hzy
    have hvx : δ ∈ α := h.transitive _ hzx _ hvz
    rcases show β ∈ δ ∨ β = δ ∨ δ ∈ β from h.trichotomy _ lt _ hvx with (hzv | rfl | hvz)
    · have : β ∉ δ := mem_asymm₃ hvz hzy
      contradiction
    · have : γ ∉ β := mem_asymm hvz
      contradiction
    · assumption
  trichotomy γ hzy δ hvy := by
    have hzx : γ ∈ α := h.transitive _ lt _ hzy
    have hvx : δ ∈ α := h.transitive _ lt _ hvy
    exact h.trichotomy γ hzx δ hvx

@[simp] protected instance empty : IsOrdinal (∅ : V) where
  trichotomy := by simp

@[simp] protected instance zero : IsOrdinal (0 : V) := .empty

protected instance succ [h : IsOrdinal α] : IsOrdinal (succ α) where
  transitive := h.toIsTransitive.succ.transitive
  trichotomy β₁ h₁ β₂ h₂ := by
    rcases show β₁ = α ∨ β₁ ∈ α by simpa [mem_succ_iff] using h₁ with (rfl | h₁)
    · rcases show β₂ = β₁ ∨ β₂ ∈ β₁ by simpa [mem_succ_iff] using h₂ with (rfl | h₂) <;> simp_all
    · rcases show β₂ = α ∨ β₂ ∈ α by simpa [mem_succ_iff] using h₂ with (rfl | h₂)
      · simp_all
      · exact h.trichotomy β₁ h₁ β₂ h₂

protected instance nat : α ∈ (ω : V) → IsOrdinal (α : V) := by
  apply naturalNumber_induction
  · definability
  case zero => simp [zero_def]
  case succ => intro α hα H; exact H.succ

lemma mem_of_ssubset [hα : IsOrdinal α] [hβ : IsOrdinal β] : α ⊊ β → α ∈ β := by
  intro ss
  have : ∃ γ, (γ ∈ β ∧ γ ∉ α) ∧ ∀ δ ∈ β, δ ∉ α → δ ∉ γ := by
    have : IsNonempty (β \ α) := (isNonempty_sdiff_of_ssubset ss)
    simpa using foundation (β \ α)
  rcases this with ⟨γ, ⟨hγβ, hγα⟩, Hγ⟩
  have Hγα : γ ⊆ α := by
    intro ξ hξγ
    have hξβ : ξ ∈ β := hβ.transitive γ hγβ _ hξγ
    by_contra! hξα
    have : ξ ∉ γ := Hγ ξ hξβ hξα
    contradiction
  have Hαγ : α ⊆ γ := by
    intro ξ hξα
    have : ξ ∈ β := ss.subset _ hξα
    have : ξ ∈ γ ∨ (ξ = γ ∨ γ ∈ ξ) := hβ.trichotomy ξ this γ hγβ
    rcases this with (hξγ | C)
    · exact hξγ
    · have : γ ∈ α := by
        rcases C with (rfl | h)
        · assumption
        · exact hα.transitive _ hξα _ h
      contradiction
  have : α = γ := subset_antisymm Hαγ Hγα
  rcases this
  assumption

@[grind =] lemma ssubset_iff [hα : IsOrdinal α] [hβ : IsOrdinal β] : α ⊊ β ↔ α ∈ β :=
  ⟨mem_of_ssubset, fun hαβ ↦ ⟨hβ.transitive _ hαβ, ne_of_mem hαβ⟩⟩

@[grind =] lemma subset_iff [hα : IsOrdinal α] [hβ : IsOrdinal β] : α ⊆ β ↔ α = β ∨ α ∈ β := by
  constructor
  · intro ss
    by_cases eq : α = β
    · simp_all
    · right; exact mem_of_ssubset ⟨ss, eq⟩
  · rintro (rfl | h)
    · simp
    · exact hβ.transitive α h

open Classical in
@[grind =_] lemma mem_iff_subset_and_not_subset [hα : IsOrdinal α] [hβ : IsOrdinal β] :
    α ∈ β ↔ α ⊆ β ∧ ¬β ⊆ α := calc
  α ∈ β ↔ α ⊊ β          := ssubset_iff.symm
  _     ↔ α ⊆ β ∧ α ≠ β  := by rfl
  _     ↔ α ⊆ β ∧ ¬β ⊆ α := by grind

variable (α β)

lemma subset_or_supset [hα : IsOrdinal α] [hβ : IsOrdinal β] : α ⊆ β ∨ β ⊆ α := by
  by_contra! Aαβ
  let C : V := {α' ∈ succ α ; ∃ β, IsOrdinal β ∧ ¬α' ⊆ β ∧ ¬β ⊆ α'}
  have hαC : α ∈ C := by
    simp only [mem_sep_iff, mem_succ_iff, mem_irrefl, or_false, true_and, C]
    exact ⟨β, hβ, Aαβ⟩
  have : ∃ α₀, (α₀ ∈ succ α ∧ ∃ β, IsOrdinal β ∧ ¬α₀ ⊆ β ∧ ¬β ⊆ α₀) ∧ ∀ γ ∈ C, γ ∉ α₀ := by
    have : IsNonempty C := ⟨α, hαC⟩
    simpa [C] using foundation C
  rcases this with ⟨α₀, ⟨hα₀sα, β₀, ordβ₀, Hα₀β₀⟩, Hα₀⟩
  have ordα₀ : IsOrdinal α₀ := by
    rcases mem_succ_iff.mp hα₀sα with (rfl | hα₀α)
    · assumption
    · exact hα.of_mem hα₀α
  let γ₀ := α₀ ∪ β₀
  have : IsOrdinal γ₀ := isOrdinal_iff.mpr ⟨IsTransitive.union, by
    intro ξ hξγ₀ ζ hζγ₀
    rcases show ξ ∈ α₀ ∨ ξ ∈ β₀ by simpa [γ₀] using hξγ₀ with (hξα₀ | hξβ₀)
    · have : IsOrdinal ξ := of_mem hξα₀
      rcases show ζ ∈ α₀ ∨ ζ ∈ β₀ by simpa [γ₀] using hζγ₀ with (hζα₀ | hζβ₀)
      · exact ordα₀.trichotomy ξ hξα₀ ζ hζα₀
      · have : IsOrdinal ζ := of_mem hζβ₀
        have : ξ ⊆ ζ ∨ ζ ⊆ ξ := by
          by_contra! A
          have : ξ ∈ C := mem_sep_iff.mpr ⟨hα.succ.transitive α₀ hα₀sα ξ hξα₀, ζ, of_mem hζβ₀, A⟩
          exact Hα₀ ξ this hξα₀
        grind
    · have : IsOrdinal ξ := of_mem hξβ₀
      rcases show ζ ∈ α₀ ∨ ζ ∈ β₀ by simpa [γ₀] using hζγ₀ with (hζα₀ | hζβ₀)
      · have : IsOrdinal ζ := of_mem hζα₀
        have : ξ ⊆ ζ ∨ ζ ⊆ ξ := by
          by_contra! A
          have : ζ ∈ C := mem_sep_iff.mpr ⟨hα.succ.transitive α₀ hα₀sα ζ hζα₀, ξ, inferInstance, by grind⟩
          exact Hα₀ _ this hζα₀
        grind
      · have : ζ ∈ ξ ∨ ζ = ξ ∨ ξ ∈ ζ := ordβ₀.trichotomy ζ hζβ₀ ξ hξβ₀
        grind⟩
  have : γ₀ = α₀ ∨ γ₀ = β₀ := by
    by_contra! A
    have : α₀ ∈ γ₀ := ssubset_iff.mp ⟨by simp [γ₀], by grind⟩
    have hα₀β₀ : α₀ ∈ β₀ := by simpa [γ₀] using this
    have : β₀ ∈ γ₀ := ssubset_iff.mp ⟨by simp [γ₀], by grind⟩
    have hβ₀α₀ : β₀ ∈ α₀ := by simpa [γ₀] using this
    exact mem_asymm hα₀β₀ hβ₀α₀
  rcases this with (e | e)
  · have : β₀ ⊆ α₀ := by simpa [γ₀] using e
    grind
  · have : α₀ ⊆ β₀ := by simpa [γ₀] using e
    grind

lemma mem_trichotomy [hα : IsOrdinal α] [hβ : IsOrdinal β] : α ∈ β ∨ α = β ∨ β ∈ α := by
  have : α ⊆ β ∨ β ⊆ α := subset_or_supset α β
  grind

variable {α β}

lemma of_transitive_of_isOrdinal (tr : IsTransitive α) (H : ∀ β ∈ α, IsOrdinal β) : IsOrdinal α where
  trichotomy ξ hξα ζ hζα :=
    have : IsOrdinal ξ := H ξ hξα
    have : IsOrdinal ζ := H ζ hζα
    mem_trichotomy ξ ζ

@[simp] protected instance ω : IsOrdinal (ω : V) :=
  of_transitive_of_isOrdinal inferInstance fun _ hn ↦ IsOrdinal.nat hn

protected lemma sUnion {X : V} (h : ∀ α ∈ X, IsOrdinal α) : IsOrdinal (⋃ˢ X) :=
  of_transitive_of_isOrdinal (IsTransitive.sUnion fun α hαX ↦ (h α hαX).toIsTransitive)
    fun β hβ ↦ by
      have : ∃ γ ∈ X, β ∈ γ := by simpa [mem_sUnion_iff] using hβ
      rcases this with ⟨γ, hγX, hβγ⟩
      have : IsOrdinal γ := h γ hγX
      exact of_mem hβγ

protected lemma sInter {X : V} (h : ∀ α ∈ X, IsOrdinal α) : IsOrdinal (⋂ˢ X) := by
  rcases eq_empty_or_isNonempty X with (rfl | hX)
  · simp
  · apply of_transitive_of_isOrdinal (IsTransitive.sInter fun α hαX ↦ (h α hαX).toIsTransitive)
    rcases hX.nonempty with ⟨α₀, hα₀X⟩
    have : IsOrdinal α₀ := h α₀ hα₀X
    intro α hα
    have : ∀ y ∈ X, α ∈ y := by simpa using hα
    have : α ∈ α₀ := this α₀ hα₀X
    exact of_mem this

lemma sInter_mem {X : V} [IsNonempty X] (h : ∀ α ∈ X, IsOrdinal α) : ⋂ˢ X ∈ X := by
  by_contra! hXX
  have : IsOrdinal (⋂ˢ X) := IsOrdinal.sInter h
  have : ⋂ˢ X ∈ ⋂ˢ X := mem_sInter_iff_of_nonempty.mpr fun α hαX ↦ by
    have : IsOrdinal α := h α hαX
    have : ⋂ˢ X ⊆ α := sInter_subset_of_mem_of_nonempty hαX
    rcases subset_iff.mp this with (rfl | hXα)
    · contradiction
    · assumption
  simp_all

lemma empty_mem_iff_nonempty [IsOrdinal α] : ∅ ∈ α ↔ IsNonempty α := by
  have : ∅ = α ∨ ∅ ∈ α := subset_iff.mp (show ∅ ⊆ α by simp)
  rcases this with (rfl | h)
  · simp
  · simp only [h, true_iff]
    exact ⟨∅, h⟩

end IsOrdinal

variable (V)

@[ext]
structure Ordinal where
  val : V
  ordinal : IsOrdinal val

variable {V}

attribute [coe] Ordinal.val

attribute [instance] Ordinal.ordinal

instance : Coe (Ordinal V) V := ⟨Ordinal.val⟩

@[coe] def IsOrdinal.toOrdinal (α : V) [IsOrdinal α] : Ordinal V := ⟨α, inferInstance⟩

omit [Nonempty V] [V ⊧ₘ* 𝗭] in
@[simp] lemma IsOrdinal.toOrdinal_val (α : V) [IsOrdinal α] : (IsOrdinal.toOrdinal α).val = α := rfl

omit [Nonempty V] [V ⊧ₘ* 𝗭] in
@[simp] lemma Ordinal.val_toOrdinal (α : Ordinal V) : IsOrdinal.toOrdinal α.val = α := rfl

namespace Ordinal

variable {α β γ : Ordinal V}

instance : LT (Ordinal V) := ⟨fun α β ↦ α.val ∈ β.val⟩

instance : LE (Ordinal V) := ⟨fun α β ↦ α.val ⊆ β.val⟩

omit [Nonempty V] [V ⊧ₘ* 𝗭] in
lemma lt_def : α < β ↔ α.val ∈ β.val := by rfl

omit [Nonempty V] [V ⊧ₘ* 𝗭] in
lemma le_def : α ≤ β ↔ α.val ⊆ β.val := by rfl

instance : IsOrdinal α.val := α.ordinal

noncomputable instance : LinearOrder (Ordinal V) where
  le_refl α := subset_refl α.val
  le_trans α β γ := subset_trans
  lt_iff_le_not_ge α β := IsOrdinal.mem_iff_subset_and_not_subset
  le_antisymm α β := by simpa [le_def, Ordinal.ext_iff] using subset_antisymm (x := α.val) (y := β.val)
  le_total α β := IsOrdinal.subset_or_supset α.val β.val
  toDecidableLE := Classical.decRel LE.le

noncomputable instance : OrderBot (Ordinal V) where
  bot := IsOrdinal.toOrdinal ∅
  bot_le _ := empty_subset _

@[simp] lemma bot_val_eq : (⊥ : Ordinal V).val = ∅ := rfl

lemma pos_iff_nonempty : ⊥ < α ↔ IsNonempty α.val := IsOrdinal.empty_mem_iff_nonempty

lemma eq_bot_or_pos : α = ⊥ ∨ α > ⊥ := by exact eq_bot_or_bot_lt α

protected noncomputable def succ (α : Ordinal V) : Ordinal V where
  val := succ α
  ordinal := inferInstance

@[simp] lemma succ_val (α : Ordinal V) : α.succ.val = succ α.val := rfl

@[simp] lemma lt_succ (α : Ordinal V) : α < α.succ := lt_def.mpr <| by simp

protected noncomputable def ω : Ordinal V := IsOrdinal.toOrdinal ω

noncomputable def minimal (α : Ordinal V) (P : V → Prop) (hP : ℒₛₑₜ-predicate P := by definability) : Ordinal V where
  val := ⋂ˢ {x ∈ ↑α ; P x}
  ordinal := IsOrdinal.sInter fun ξ hξ ↦
    have : ξ ∈ (α : V) ∧ P ξ := by simpa using hξ
    IsOrdinal.of_mem this.1

section minimal

variable (P : V → Prop) (hP : ℒₛₑₜ-predicate P)

@[simp] lemma minimal_val (α : Ordinal V) : (minimal α P).val = ⋂ˢ {x ∈ ↑α ; P x} := rfl

@[simp] lemma minimal_bot_eq : minimal ⊥ P hP = ⊥ := by ext; simp [minimal_val]

variable {P hP}

private lemma minimal_prop_of_exists_aux (H : ∃ β < α, P β) :
    α.minimal P < α ∧ P (α.minimal P) ∧ ∀ ξ < α, P ξ → α.minimal P ≤ ξ := by
  let X := {x ∈ ↑α ; P x}
  have : IsNonempty X := by
    rcases H with ⟨β, hαβ, Pβ⟩
    exact ⟨β, by simp [X, lt_def.mp hαβ, Pβ]⟩
  have : ⋂ˢ X ∈ X := IsOrdinal.sInter_mem (X := X) fun β hβ ↦ by
    have : β ∈ α.val ∧ P β := by simpa [X] using hβ
    exact IsOrdinal.of_mem this.1
  have : ⋂ˢ X ∈ α.val ∧ P (⋂ˢ X) := by simpa [X] using this
  refine ⟨this.1, by simpa using this.2, ?_⟩
  intro ξ hξα Pξ
  suffices ⋂ˢ X ⊆ ξ from le_def.mpr (by simpa using this)
  apply sInter_subset_of_mem_of_nonempty
  simp [X, Pξ, lt_def.mp hξα]

lemma minimal_lt_of_exists (H : ∃ β < α, P β) : α.minimal P < α := (minimal_prop_of_exists_aux H).1

lemma minimal_prop_of_exists (H : ∃ β < α, P β) : P (α.minimal P) := (minimal_prop_of_exists_aux H).2.1

lemma minimal_le_of_exists_aux (H : ∃ β < α, P β) : ∀ ξ < α, P ξ → α.minimal P ≤ ξ := (minimal_prop_of_exists_aux H).2.2

lemma minimal_le_of_exists (H : ∃ β < α, P β) : ∀ ξ : Ordinal V, P ξ → α.minimal P ≤ ξ := by
  intro ξ Pξ
  rcases show ξ < α ∨ α ≤ ξ from lt_or_ge ξ α with (lt | le)
  · exact minimal_le_of_exists_aux H ξ lt Pξ
  · calc
      α.minimal P hP ≤ α := le_of_lt <| minimal_lt_of_exists H
      _              ≤ ξ := le

end minimal

end Ordinal

lemma exists_minimal (P : V → Prop) (hP : ℒₛₑₜ-predicate P) (h : ∃ α : Ordinal V, P α) :
    ∃ β : Ordinal V, P β ∧ ∀ ξ : Ordinal V, P ξ → β ≤ ξ := by
  rcases h with ⟨α, hα⟩
  have exs : ∃ β < α.succ, P β := ⟨α, by simp, hα⟩
  refine ⟨α.succ.minimal P, Ordinal.minimal_prop_of_exists exs, Ordinal.minimal_le_of_exists exs⟩

lemma transfinite_induction (P : V → Prop) (hP : ℒₛₑₜ-predicate P)
    (ih : ∀ α : Ordinal V, (∀ β < α, P β) → P α) : ∀ α : Ordinal V, P α := by
  by_contra! exs
  have : ∃ β : Ordinal V, ¬P ↑β ∧ ∀ (ξ : Ordinal V), ¬P ↑ξ → β ≤ ξ :=
    exists_minimal (fun x ↦ ¬P x) (by definability) exs
  rcases this with ⟨β, Pβ, H⟩
  have : P β := ih β fun ξ hξβ ↦ by
    by_contra! Pξ
    have : β ≤ ξ := H ξ Pξ
    exact not_lt_of_ge this hξβ
  contradiction

/-! ### Well-foundedness -/

class IsWellFoundedRel (D : outParam (V → Prop)) (R : V → V → Prop) : Prop where
  wf : ∀ S : V, (∀ x ∈ S, D x) → IsNonempty S → ∃ z ∈ S, ∀ x ∈ S, ¬R x z

instance IsWellFoundedRel.mem : IsWellFoundedRel (fun _ : V ↦ True) (· ∈ ·) where
  wf S _ _ := foundation S

class SetLike (R : V → V → Prop) where
  leftSet (x : V) : ∃ y : V, ∀ z, z ∈ y ↔ R z x

namespace SetLike

variable (R : V → V → Prop) [SetLike R]

lemma left_existsUnique (x : V) : ∃! s : V, ∀ z, z ∈ s ↔ R z x := by
  have : ∃ y, ∀ z, z ∈ y ↔ R z x := leftSet x
  rcases this with ⟨y, hy⟩
  apply ExistsUnique.intro y hy
  intro y' hy'
  ext; simp_all

noncomputable def left (x : V) : V := Classical.choose! <| left_existsUnique R x

@[simp] lemma mem_left (x y : V) : y ∈ left R x ↔ R y x := Classical.choose!_spec (left_existsUnique R x) y

end SetLike

end LO.FirstOrder.SetTheory
