import Foundation.Logic.LogicSymbol

open Function

namespace LO

@[notation_class]
class Box (F : Type*) where
  box : F → F
  box_injective : Function.Injective box := by simp [Function.Injective];

prefix:76 "□" => Box.box

namespace Box

attribute [match_pattern] Box.box
attribute [simp] Box.box_injective

variable [Box F]

@[match_pattern] abbrev boxdot [Wedge F] (φ : F) : F := φ ⋏ □φ
prefix:76 "⊡" => boxdot

abbrev multibox (n : ℕ) : F → F := (□ ·)^[n]
notation:76 "□^[" n:90 "]" φ:80 => multibox n φ

/-
class Subclosed (C : F → Prop) where
  box_closed : C (□φ) → C φ

attribute [aesop safe 5 forward] Subclosed.box_closed
-/

variable {φ ψ : F} {n : ℕ}

@[simp]
lemma box_injective' : □φ = □ψ ↔ φ = ψ := by
  constructor;
  . apply box_injective;
  . simp_all;

@[simp] lemma multibox_succ : □^[(n + 1)]φ = □(□^[n]φ) := by apply iterate_succ_apply'

@[simp] lemma multibox_injective : Function.Injective (□^[n] · : F → F) := by apply Function.Injective.iterate (by simp);

@[simp]
lemma multimop_injective' : □^[n]φ = □^[n]ψ ↔ φ = ψ := by
  constructor;
  . apply multibox_injective;
  . simp_all;

lemma add : □^[n](□^[m]φ) = □^[(n + m)]φ := by
  induction n with
  | zero => simp;
  | succ n ih => rw [(show n + 1 + m = n + m + 1 by omega)]; simpa;

end Box


@[notation_class]
class Dia (F : Type*) where
  dia : F → F
  dia_injective : Function.Injective dia := by simp [Function.Injective];

prefix:76 "◇" => Dia.dia

namespace Dia

attribute [match_pattern] Dia.dia
attribute [simp] Dia.dia_injective

variable [Dia F]

@[match_pattern] abbrev diadot [Vee F] (φ : F) : F := φ ⋎ ◇φ
prefix:76 "⟐" => diadot

abbrev multidia (n : ℕ) : F → F := (◇ ·)^[n]

notation:76 "◇^[" n:90 "]" φ:80 => multidia n φ

/-
class Subclosed [LogicalConnective F] (C : F → Prop)  where
  dia_closed : C (◇φ) → C φ

attribute [aesop safe 5 forward] Subclosed.dia_closed
-/

variable {φ ψ : F} {n : ℕ}

@[simp]
lemma dia_injective' : ◇φ = ◇ψ ↔ φ = ψ := by
  constructor;
  . apply dia_injective;
  . simp_all;

@[simp] lemma multidia_succ : ◇^[(n + 1)]φ = ◇(◇^[n]φ) := by apply iterate_succ_apply'

@[simp] lemma multidia_injective : Function.Injective (◇^[n] · : F → F) := by apply Function.Injective.iterate (by simp);

@[simp]
lemma multidia_injective' : ◇^[n]φ = ◇^[n]ψ ↔ φ = ψ := by
  constructor;
  . apply multidia_injective;
  . simp_all;

lemma add : ◇^[n](◇^[m]φ) = ◇^[(n + m)]φ := by
  induction n with
  | zero => simp;
  | succ n ih => rw [(show n + 1 + m = n + m + 1 by omega)]; simpa;

end Dia

class BasicModalLogicalConnective (F : Type*) extends LogicalConnective F, Box F, Dia F

/-
class BasicModalLogicConnective.Subclosed [BasicModalLogicalConnective F] (C : F → Prop) extends
  LogicalConnective.Subclosed C,
  Box.Subclosed C,
  Dia.Subclosed C
-/

class DiaAbbrev (F : Type*) [Box F] [Dia F] [Tilde F] where
  dia_abbrev {φ : F} : ◇φ =  ∼(□(∼φ))
-- attribute [aesop safe 5 forward] DiaAbbrev.dia_abbrev

class ModalDeMorgan (F : Type*) [LogicalConnective F] [Box F] [Dia F] extends DeMorgan F where
  dia (φ : F) : ∼◇φ = □(∼φ)
  box (φ : F) : ∼□φ = ◇(∼φ)

attribute [simp] ModalDeMorgan.dia ModalDeMorgan.box

end LO


section

variable {n m : ℕ}

open LO (Box Dia)
variable {F : Type*}

section Box

variable [Box F]

namespace Set

variable {s t : Set F} {φ : F}

protected abbrev multibox (n : ℕ) : Set F → Set F := Set.image (□·)^[n]
protected abbrev box : Set F → Set F := Set.multibox (n := 1)
protected abbrev premultibox (n : ℕ) : Set F → Set F := Set.preimage (□·)^[n]
protected abbrev prebox : Set F → Set F := Set.premultibox (n := 1)

@[simp] lemma eq_box_multibox_one : s.multibox 1 = s.box := by rfl
@[simp] lemma eq_prebox_premultibox_one : s.premultibox 1 = s.prebox:= by rfl

lemma multibox_subset_mono (h : s ⊆ t) : s.multibox n ⊆ t.multibox n := by simp_all [Set.subset_def];
lemma box_subset_mono (h : s ⊆ t) : s.box ⊆ t.box := by simpa using multibox_subset_mono (n := 1) h;

lemma premultibox_subset_mono (h : s ⊆ t) : s.premultibox n ⊆ t.premultibox n := by simp_all [Set.subset_def];
lemma prebox_subset_mono (h : s ⊆ t) : s.prebox ⊆ t.prebox := by simpa using premultibox_subset_mono (n := 1) h;

lemma iff_mem_premultibox : φ ∈ s.premultibox n ↔ □^[n]φ ∈ s := by simp;
@[simp] lemma iff_mem_multibox : □^[n]φ ∈ s.multibox n ↔ φ ∈ s := by simp;

end Set


namespace Finset

variable  {s t : Finset F} {φ : F}

protected abbrev multibox [DecidableEq F] (n : ℕ) : Finset F → Finset F := Finset.image (□·)^[n]
protected abbrev box [DecidableEq F] : Finset F → Finset F := Finset.multibox (n := 1)

protected noncomputable abbrev premultibox (n : ℕ) : Finset F → Finset F := λ s => Finset.preimage s (□·)^[n] (by simp [Set.InjOn])
protected noncomputable abbrev prebox := Finset.premultibox (F := F) (n := 1)

@[simp] lemma eq_box_multibox_one [DecidableEq F] : s.multibox 1 = s.box := by rfl
@[simp] lemma eq_prebox_premultibox_one : s.premultibox 1 = s.prebox := by rfl

/-
lemma multibox_coe [DecidableEq F] : s.multibox n = s.toSet.multibox n := by simp_all
lemma box_coe [DecidableEq F] : s.box = s.toSet.box := by simpa using multibox_coe (n := 1)

lemma multibox_mem_coe [DecidableEq F] : φ ∈ s.multibox n ↔ φ ∈ s.toSet.multibox n := by constructor <;> simp_all
lemma box_mem_coe [DecidableEq F] : φ ∈ s.box ↔ φ ∈ s.toSet.box := by simp;

lemma premultibox_coe : s.premultibox n = s.toSet.premultibox n := by simp_all
lemma prebox_coe : s.prebox = □''⁻¹(↑s : Set F) := by simpa using premultibox_coe (n := 1)
-/

/-
lemma premultibox_multibox_eq_of_subset_multibox
  [DecidableEq F]
  {s : Finset F} {t : Set F} (hs : ↑s ⊆ t.multibox n) : (s.premultibox n).multibox n = s := by
  have := Set.eq_premultibox_multibox_of_subset_premultibox hs;
  rw [←premultibox_coe, ←multibox_coe] at this;
  exact Finset.coe_inj.mp this;

lemma prebox_box_eq_of_subset_box [DecidableEq F] {s : Finset F} {t : Set F} (hs : ↑s ⊆ t.box) : s.prebox.box = s
  := by simpa using premultibox_multibox_eq_of_subset_multibox (n := 1) hs
-/

lemma exists_multibox_of_mem_multibox [DecidableEq F] (h : φ ∈ s.multibox n) : ∃ ψ ∈ s, φ = □^[n]ψ := by
  simp at h;
  tauto;
lemma exists_box_of_mem_box [DecidableEq F] (h : φ ∈ s.box) : ∃ ψ ∈ s, φ = □ψ := exists_multibox_of_mem_multibox h

end Finset



namespace List

variable {l s t : List F} {φ : F}

protected abbrev multibox (n : ℕ) : List F → List F
  | [] => []
  | φ :: l => □^[n]φ :: List.multibox n l
-- notation "□'^[" n:90 "]" l:80 => List.multibox n l

protected abbrev box : List F → List F := List.multibox (n := 1)
-- prefix:80 "□'" => List.box

protected noncomputable abbrev premultibox [DecidableEq F] (n : ℕ) : List F → List F := λ l => Finset.premultibox n l.toFinset |>.toList
-- notation "□'⁻¹^[" n:90 "]" l:80 => List.premultibox n l

protected noncomputable abbrev prebox [DecidableEq F] : List F → List F := List.premultibox (n := 1)
-- prefix:80 "□'⁻¹" => List.prebox

@[simp] lemma eq_multibox_zero : s.multibox 0 = s := by induction s <;> simp_all [List.multibox];
@[simp] lemma eq_box_multibox_one : l.multibox 1 = l.box := by rfl
@[simp] lemma eq_prebox_premultibox_one [DecidableEq F] : l.premultibox 1 = l.prebox := by rfl

@[simp] lemma multibox_nil : ([] : List F).multibox n = [] := by simp;
@[simp] lemma box_nil : ([] : List F).box = [] := multibox_nil (n := 1)
@[simp] lemma premultibox_nil [DecidableEq F] : ([] :List F).premultibox n = [] := by simp;
@[simp] lemma prebox_nil [DecidableEq F] : ([] : List F).prebox = [] := premultibox_nil (n := 1)

@[simp] lemma multibox_single : [φ].multibox n = [□^[n]φ] := by simp;
@[simp] lemma box_single : [φ].box = [□φ] := multibox_single (n := 1)

lemma multibox_mem_of (h : φ ∈ l) : □^[n]φ ∈ l.multibox n := by
  induction l with
  | nil => simp at h;
  | cons ψ l ih =>
    rcases (by simpa using h) with (rfl | h);
    . tauto;
    . tauto;
lemma box_mem_of (h : φ ∈ l) : □φ ∈ l.box := multibox_mem_of h

lemma multibox_nonempty (h : l ≠ []) : l.multibox n ≠ [] := by induction l <;> simp_all;
lemma box_nonempty (h : l ≠ []) : l.box ≠ [] := multibox_nonempty h

lemma exists_multibox_of_mem_multibox (h : φ ∈ l.multibox n) : ∃ ψ ∈ l, φ = □^[n]ψ := by
  induction l with
  | nil => simp at h;
  | cons ψ l ih =>
    simp only [mem_cons] at h;
    rcases h with (h | h);
    . use ψ; tauto;
    . obtain ⟨ξ, hξ₁, hξ₂⟩ := ih h;
      use ξ;
      constructor <;> tauto;
lemma exists_box_of_mem_box (h : φ ∈ l.box) : ∃ ψ ∈ l, φ = □ψ := exists_multibox_of_mem_multibox h

protected noncomputable abbrev multiboxFilter [DecidableEq F] (l : List F) (n : ℕ) := l.premultibox n |>.multibox n
protected noncomputable abbrev boxFilter [DecidableEq F] (l : List F) := l.multiboxFilter 1

lemma mem_of_mem_multiboxFilter [DecidableEq F] (h : φ ∈ l.multiboxFilter n) : φ ∈ l := by
  induction l with
  | nil => simp [List.multiboxFilter] at h;
  | cons ψ l ih =>
    obtain ⟨ξ, hξ, rfl⟩ := exists_multibox_of_mem_multibox h;
    clear h;
    simp only [Finset.mem_toList, toFinset_cons, Finset.mem_preimage, Finset.mem_insert, mem_toFinset] at hξ;
    rcases hξ with (hξ | hξ);
    . subst hξ; tauto;
    . tauto;
lemma mem_of_mem_boxFilter [DecidableEq F] (h : φ ∈ l.boxFilter) : φ ∈ l := mem_of_mem_multiboxFilter h

lemma mem_multiboxFilter_of_mem [DecidableEq F] (h : □^[n]φ ∈ l) : □^[n]φ ∈ l.multiboxFilter n := by
  apply multibox_mem_of;
  simpa;
lemma mem_boxFilter_of_mem [DecidableEq F] (h : □φ ∈ l) : □φ ∈ l.boxFilter := mem_multiboxFilter_of_mem h

@[simp]
lemma iff_mem_multibox_add : φ ∈ (l.multibox m |>.multibox n) ↔ φ ∈ l.multibox (n + m) := by
  induction l with
  | nil => simp_all;
  | cons ψ l ih =>
    simp only [mem_cons, LO.Box.add];
    constructor;
    . intro h;
      rcases h with (rfl | h);
      . tauto;
      . right;
        apply ih.mp;
        exact h;
    . intro h;
      rcases h with (rfl | h);
      . tauto;
      . right;
        apply ih.mpr;
        exact h;

end List


namespace Finset


end Finset

end Box



section Dia

variable [Dia F]

namespace Set

variable {s t : Set F} {φ : F}

protected abbrev multidia (n : ℕ) : Set F → Set F := Set.image (◇·)^[n]
protected abbrev dia : Set F → Set F := Set.multidia (n := 1)
protected abbrev premultidia (n : ℕ) : Set F → Set F := Set.preimage (◇·)^[n]
protected abbrev predia : Set F → Set F := Set.premultidia (n := 1)

@[simp] lemma eq_dia_multidia_one : s.multidia 1 = s.dia := by rfl
@[simp] lemma eq_predia_premultidia_one : s.premultidia 1 = s.predia:= by rfl

lemma multidia_subset_mono (h : s ⊆ t) : s.multidia n ⊆ t.multidia n := by simp_all [Set.subset_def];
lemma dia_subset_mono (h : s ⊆ t) : s.dia ⊆ t.dia := by simpa using multidia_subset_mono (n := 1) h;

lemma premultidia_subset_mono (h : s ⊆ t) : s.premultidia n ⊆ t.premultidia n := by simp_all [Set.subset_def];
lemma predia_subset_mono (h : s ⊆ t) : s.predia ⊆ t.predia := by simpa using premultidia_subset_mono (n := 1) h;

lemma iff_mem_premultidia : φ ∈ s.premultidia n ↔ ◇^[n]φ ∈ s := by simp;
@[simp] lemma iff_mem_multidia : ◇^[n]φ ∈ s.multidia n ↔ φ ∈ s := by simp;

end Set


namespace Finset

variable  {s t : Finset F} {φ : F}

protected abbrev multidia [DecidableEq F] (n : ℕ) : Finset F → Finset F := Finset.image (◇·)^[n]
protected abbrev dia [DecidableEq F] : Finset F → Finset F := Finset.multidia (n := 1)

protected noncomputable abbrev premultidia (n : ℕ) : Finset F → Finset F := λ s => Finset.preimage s (◇·)^[n] (by simp [Set.InjOn])
protected noncomputable abbrev predia := Finset.premultidia (F := F) (n := 1)

@[simp] lemma eq_dia_multidia_one [DecidableEq F] : s.multidia 1 = s.dia := by rfl
@[simp] lemma eq_predia_premultidia_one : s.premultidia 1 = s.predia := by rfl

/-
lemma multidia_coe [DecidableEq F] : s.multidia n = s.toSet.multidia n := by simp_all
lemma dia_coe [DecidableEq F] : s.dia = s.toSet.dia := by simpa using multidia_coe (n := 1)

lemma multidia_mem_coe [DecidableEq F] : φ ∈ s.multidia n ↔ φ ∈ s.toSet.multidia n := by constructor <;> simp_all
lemma dia_mem_coe [DecidableEq F] : φ ∈ s.dia ↔ φ ∈ s.toSet.dia := by simp;

lemma premultidia_coe : s.premultidia n = s.toSet.premultidia n := by simp_all
lemma predia_coe : s.predia = ◇''⁻¹(↑s : Set F) := by simpa using premultidia_coe (n := 1)
-/

/-
lemma premultidia_multidia_eq_of_subset_multidia
  [DecidableEq F]
  {s : Finset F} {t : Set F} (hs : ↑s ⊆ t.multidia n) : (s.premultidia n).multidia n = s := by
  have := Set.eq_premultidia_multidia_of_subset_premultidia hs;
  rw [←premultidia_coe, ←multidia_coe] at this;
  exact Finset.coe_inj.mp this;

lemma predia_dia_eq_of_subset_dia [DecidableEq F] {s : Finset F} {t : Set F} (hs : ↑s ⊆ t.dia) : s.predia.dia = s
  := by simpa using premultidia_multidia_eq_of_subset_multidia (n := 1) hs
-/

end Finset



namespace List

variable {l s t : List F} {φ : F}

protected abbrev multidia (n : ℕ) : List F → List F
  | [] => []
  | φ :: l => ◇^[n]φ :: List.multidia n l
-- notation "◇'^[" n:90 "]" l:80 => List.multidia n l

protected abbrev dia : List F → List F := List.multidia (n := 1)
-- prefix:80 "◇'" => List.dia

protected noncomputable abbrev premultidia [DecidableEq F] (n : ℕ) : List F → List F := λ l => Finset.premultidia n l.toFinset |>.toList
-- notation "◇'⁻¹^[" n:90 "]" l:80 => List.premultidia n l

protected noncomputable abbrev predia [DecidableEq F] : List F → List F := List.premultidia (n := 1)
-- prefix:80 "◇'⁻¹" => List.predia

@[simp] lemma eq_multidia_zero : s.multidia 0 = s := by induction s <;> simp_all [List.multidia];
@[simp] lemma eq_dia_multidia_one : l.multidia 1 = l.dia := by rfl
@[simp] lemma eq_predia_premultidia_one [DecidableEq F] : l.premultidia 1 = l.predia := by rfl

@[simp] lemma multidia_nil : ([] : List F).multidia n = [] := by simp;
@[simp] lemma dia_nil : ([] : List F).dia = [] := multidia_nil (n := 1)
@[simp] lemma premultidia_nil [DecidableEq F] : ([] :List F).premultidia n = [] := by simp;
@[simp] lemma predia_nil [DecidableEq F] : ([] : List F).predia = [] := premultidia_nil (n := 1)

@[simp] lemma multidia_single : [φ].multidia n = [◇^[n]φ] := by simp;
@[simp] lemma dia_single : [φ].dia = [◇φ] := multidia_single (n := 1)

lemma multidia_mem_of (h : φ ∈ l) : ◇^[n]φ ∈ l.multidia n := by
  induction l with
  | nil => simp at h;
  | cons ψ l ih =>
    rcases (by simpa using h) with (rfl | h);
    . tauto;
    . tauto;
lemma dia_mem_of (h : φ ∈ l) : ◇φ ∈ l.dia := multidia_mem_of h

lemma multidia_nonempty (h : l ≠ []) : l.multidia n ≠ [] := by induction l <;> simp_all;
lemma dia_nonempty (h : l ≠ []) : l.dia ≠ [] := multidia_nonempty h

lemma exists_multidia_of_mem_multidia (h : φ ∈ l.multidia n) : ∃ ψ ∈ l, φ = ◇^[n]ψ := by
  induction l with
  | nil => simp at h;
  | cons ψ l ih =>
    simp only [mem_cons] at h;
    rcases h with (h | h);
    . use ψ; tauto;
    . obtain ⟨ξ, hξ₁, hξ₂⟩ := ih h;
      use ξ;
      constructor <;> tauto;
lemma exists_dia_of_mem_dia (h : φ ∈ l.dia) : ∃ ψ ∈ l, φ = ◇ψ := exists_multidia_of_mem_multidia h

protected noncomputable abbrev multidiaFilter [DecidableEq F] (l : List F) (n : ℕ) := l.premultidia n |>.multidia n
protected noncomputable abbrev diaFilter [DecidableEq F] (l : List F) := l.multidiaFilter 1

lemma mem_of_mem_multidiaFilter [DecidableEq F] (h : φ ∈ l.multidiaFilter n) : φ ∈ l := by
  induction l with
  | nil => simp [List.multidiaFilter] at h;
  | cons ψ l ih =>
    obtain ⟨ξ, hξ, rfl⟩ := exists_multidia_of_mem_multidia h;
    clear h;
    simp only [Finset.mem_toList, toFinset_cons, Finset.mem_preimage, Finset.mem_insert, mem_toFinset] at hξ;
    rcases hξ with (hξ | hξ);
    . subst hξ; tauto;
    . tauto;
lemma mem_of_mem_diaFilter [DecidableEq F] (h : φ ∈ l.diaFilter) : φ ∈ l := mem_of_mem_multidiaFilter h

lemma mem_multidiaFilter_of_mem [DecidableEq F] (h : ◇^[n]φ ∈ l) : ◇^[n]φ ∈ l.multidiaFilter n := by
  apply multidia_mem_of;
  simpa;
lemma mem_diaFilter_of_mem [DecidableEq F] (h : ◇φ ∈ l) : ◇φ ∈ l.diaFilter := mem_multidiaFilter_of_mem h

@[simp]
lemma iff_mem_multidia_add : φ ∈ (l.multidia m |>.multidia n) ↔ φ ∈ l.multidia (n + m) := by
  induction l with
  | nil => simp_all;
  | cons ψ l ih =>
    simp only [mem_cons, LO.Dia.add];
    constructor;
    . intro h;
      rcases h with (rfl | h);
      . tauto;
      . right;
        apply ih.mp;
        exact h;
    . intro h;
      rcases h with (rfl | h);
      . tauto;
      . right;
        apply ih.mpr;
        exact h;

end List

end Dia


end
