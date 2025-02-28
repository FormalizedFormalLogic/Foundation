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

class Subclosed (C : F → Prop) where
  box_closed : C (□φ) → C φ

attribute [aesop safe 5 forward] Subclosed.box_closed


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

class Subclosed [LogicalConnective F] (C : F → Prop)  where
  dia_closed : C (◇φ) → C φ

attribute [aesop safe 5 forward] Subclosed.dia_closed

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

end Dia

class BasicModalLogicalConnective (F : Type*) extends LogicalConnective F, Box F, Dia F

class BasicModalLogicConnective.Subclosed [BasicModalLogicalConnective F] (C : F → Prop) extends
  LogicalConnective.Subclosed C,
  Box.Subclosed C,
  Dia.Subclosed C

class DiaAbbrev (F : Type*) [Box F] [Dia F] [Tilde F] where
  dia_abbrev {φ : F} : ◇φ =  ∼(□(∼φ))
-- attribute [aesop safe 5 forward] DiaAbbrev.dia_abbrev

class ModalDeMorgan (F : Type*) [LogicalConnective F] [Box F] [Dia F] extends DeMorgan F where
  dia (φ : F) : ∼◇φ = □(∼φ)
  box (φ : F) : ∼□φ = ◇(∼φ)

attribute [simp] ModalDeMorgan.dia ModalDeMorgan.box

end LO


section

open LO (Box Dia)
variable {F : Type*}

protected abbrev Set.multibox [Box F] (n : ℕ) : Set F → Set F := Set.image (□·)^[n]
notation:80 "□''^[" n:90 "]" s:80 => Set.multibox n s

protected abbrev Set.multidia [Dia F] (n : ℕ) : Set F → Set F := Set.image (◇·)^[n]
notation:80 "◇''^[" n:90 "]" s:80 => Set.multidia n s

protected abbrev Set.box [Box F] : Set F → Set F := Set.multibox (n := 1)
prefix:80 "□''" => Set.box

protected abbrev Set.dia [Dia F] : Set F → Set F := Set.multidia (n := 1)
prefix:80 "◇''" => Set.dia


protected abbrev Set.premultibox [Box F] (n : ℕ) : Set F → Set F := Set.preimage (□·)^[n]
notation:80 "□''⁻¹^[" n:90 "]" s:80 => Set.premultibox n s

protected abbrev Set.premultidia [Dia F] (n : ℕ) : Set F → Set F := Set.preimage (◇·)^[n]
notation:80 "◇''⁻¹^[" n:90 "]" s:80 => Set.premultidia n s

protected abbrev Set.prebox [Box F] : Set F → Set F := Set.premultibox (n := 1)
prefix:80 "□''⁻¹" => Set.prebox

protected abbrev Set.predia [Dia F] : Set F → Set F := Set.premultidia (n := 1)
prefix:80 "◇''⁻¹" => Set.predia


namespace Set

variable {s t : Set F}

section

variable [Box F]

@[simp] lemma eq_box_multibox_one : □''s = □''^[1]s := by rfl

@[simp] lemma eq_prebox_premultibox_one : □''⁻¹s = □''⁻¹^[1]s := by rfl


@[simp] lemma multibox_subset_mono (h : s ⊆ t) : □''^[n]s ⊆ □''^[n]t := by simp_all [Set.subset_def];

@[simp] lemma box_subset_mono (h : s ⊆ t) : □''s ⊆ □''t := by simpa using multibox_subset_mono (n := 1) h;


@[simp] lemma premultibox_subset_mono (h : s ⊆ t) : □''⁻¹^[n]s ⊆ □''⁻¹^[n]t := by simp_all [Set.subset_def];

@[simp] lemma prebox_subset_mono (h : s ⊆ t) : □''⁻¹s ⊆  □''⁻¹t := by simpa using premultibox_subset_mono (n := 1) h;


@[simp] lemma iff_mem_premultibox : φ ∈ □''⁻¹^[n]s ↔ □^[n]φ ∈ s := by simp;

@[simp] lemma iff_mem_multibox : □^[n]φ ∈ □''^[n]s ↔ φ ∈ s := by simp;


lemma subset_premulitibox_iff_multibox_subset (h : s ⊆ □''⁻¹^[n]t) :  □''^[n]s ⊆ t := by
  intro φ hp;
  obtain ⟨_, _, rfl⟩ := multibox_subset_mono h hp;
  assumption;

lemma subset_prebox_iff_box_subset (h : s ⊆ □''⁻¹t) : □''s ⊆ t := by simpa using subset_premulitibox_iff_multibox_subset (n := 1) h

lemma subset_multibox_iff_premulitibox_subset (h : s ⊆ □''^[n]t) : □''⁻¹^[n]s ⊆ t := by
  intro φ hp;
  have := premultibox_subset_mono h hp;
  simp_all;
lemma subset_box_iff_prebox_subset (h : s ⊆ □''t) : □''⁻¹s ⊆ t := by simpa using subset_multibox_iff_premulitibox_subset (n := 1) h

lemma forall_multibox_of_subset_multibox (h : s ⊆ □''^[n]t) : ∀ φ ∈ s, ∃ ψ ∈ t, φ = □^[n]ψ := by
  intro φ hp;
  obtain ⟨ψ, _, rfl⟩ := h hp;
  use ψ;
lemma forall_box_of_subset_box (h : s ⊆ □''t) : ∀ φ ∈ s, ∃ ψ ∈ t, φ = □ψ := by simpa using forall_multibox_of_subset_multibox (n := 1) h

lemma eq_premultibox_multibox_of_subset_premultibox (h : s ⊆ □''^[n]t) :  □''^[n]□''⁻¹^[n]s = s := by
  apply Set.eq_of_subset_of_subset;
  . intro φ hp;
    obtain ⟨_, _, rfl⟩ := hp;
    simp_all [Set.premultibox];
  . intro φ hp;
    obtain ⟨ψ, _, rfl⟩ := forall_multibox_of_subset_multibox h φ hp;
    simp_all [Set.premultibox];
lemma eq_prebox_box_of_subset_prebox (h : s ⊆ □''t) : □''□''⁻¹s = s := by simpa using eq_premultibox_multibox_of_subset_premultibox (n := 1) h

end


section

variable [Dia F]

@[simp] lemma eq_dia_multidia_one : ◇''s = ◇''^[1]s := by rfl

@[simp] lemma eq_predia_premultidia_one : ◇''⁻¹s = ◇''⁻¹^[1]s := by rfl


@[simp] lemma multidia_subset_mono (h : s ⊆ t) : ◇''^[n]s ⊆ ◇''^[n]t := by simp_all [Set.subset_def];

@[simp] lemma dia_subset_mono (h : s ⊆ t) : ◇''s ⊆ ◇''t := by simpa using multidia_subset_mono (n := 1) h;


@[simp] lemma premultidia_subset_mono (h : s ⊆ t) : ◇''⁻¹^[n]s ⊆ ◇''⁻¹^[n]t := by simp_all [Set.subset_def];

@[simp] lemma predia_subset_mono (h : s ⊆ t) : ◇''⁻¹s ⊆ ◇''⁻¹t := by simpa using premultidia_subset_mono (n := 1) h;


@[simp] lemma iff_mem_premultidia : φ ∈ ◇''⁻¹^[n]s ↔ ◇^[n]φ ∈ s := by simp;

@[simp] lemma iff_mem_multidia : ◇^[n]φ ∈ ◇''^[n]s ↔ φ ∈ s := by simp;

lemma subset_premultidia_iff_multidia_subset (h : s ⊆ ◇''⁻¹^[n]t) :  ◇''^[n]s ⊆ t := by
  intro φ hp;
  obtain ⟨_, _, rfl⟩ := multidia_subset_mono h hp;
  assumption;

lemma subset_predia_iff_dia_subset (h : s ⊆ ◇''⁻¹t) : ◇''s ⊆ t := by simpa using subset_premultidia_iff_multidia_subset (n := 1) h

lemma subset_multidia_iff_premultidia_subset (h : s ⊆ ◇''^[n]t) : ◇''⁻¹^[n]s ⊆ t := by
  intro φ hp;
  have := premultidia_subset_mono h hp;
  simp_all;

lemma subset_dia_iff_predia_subset (h : s ⊆ ◇''t) : ◇''⁻¹s ⊆ t := by simpa using subset_multidia_iff_premultidia_subset (n := 1) h

lemma forall_multidia_of_subset_multidia (h : s ⊆ ◇''^[n]t) : ∀ φ ∈ s, ∃ ψ ∈ t, φ = ◇^[n]ψ := by
  intro φ hp;
  obtain ⟨ψ, _, rfl⟩ := h hp;
  use ψ;
lemma forall_dia_of_subset_dia (h : s ⊆ ◇''t) : ∀ φ ∈ s, ∃ ψ ∈ t, φ = ◇ψ := by simpa using forall_multidia_of_subset_multidia (n := 1) h

lemma eq_premultidia_multidia_of_subset_premultidia (h : s ⊆ ◇''^[n]t) :  ◇''^[n]◇''⁻¹^[n]s = s := by
  apply Set.eq_of_subset_of_subset;
  . intro φ hp;
    obtain ⟨_, _, rfl⟩ := hp;
    simp_all [Set.premultidia];
  . intro φ hp;
    obtain ⟨ψ, _, rfl⟩ := forall_multidia_of_subset_multidia h φ hp;
    simp_all [Set.premultidia];
lemma eq_predia_dia_of_subset_predia (h : s ⊆ ◇''t) : ◇''◇''⁻¹s = s := by simpa using eq_premultidia_multidia_of_subset_premultidia (n := 1) h

end

end Set


section

variable [DecidableEq F]

protected abbrev Finset.multibox [Box F] (n : ℕ) : Finset F → Finset F := Finset.image (□·)^[n]

protected abbrev Finset.multidia [Dia F] (n : ℕ) : Finset F → Finset F := Finset.image (◇·)^[n]

protected abbrev Finset.box [Box F] : Finset F → Finset F := Finset.multibox (n := 1)

protected abbrev Finset.dia [Dia F] : Finset F → Finset F := Finset.multidia (n := 1)


protected noncomputable abbrev Finset.premultibox [Box F] (n : ℕ) : Finset F → Finset F := λ s => Finset.preimage s (□·)^[n] (by simp [Set.InjOn])

protected noncomputable abbrev Finset.premultidia [Dia F] (n : ℕ) : Finset F → Finset F := λ s => Finset.preimage s (◇·)^[n] (by simp [Set.InjOn])

protected noncomputable abbrev Finset.prebox [Box F] : Finset F → Finset F := Finset.premultibox (n := 1)

protected noncomputable abbrev Finset.predia [Dia F] : Finset F → Finset F := Finset.premultidia (n := 1)

end

namespace Finset

variable {s t : Finset F} {n : ℕ}

section

variable [Box F]

@[simp] lemma eq_box_multibox_one [DecidableEq F] : s.box = s.multibox 1 := by rfl

@[simp] lemma eq_prebox_premultibox_one : s.prebox = s.premultibox 1 := by rfl

lemma multibox_coe [DecidableEq F] : (s.multibox n) = □''^[n](s : Set F) := by simp_all

lemma box_coe [DecidableEq F] : s.box = □''(s : Set F) := by simpa using multibox_coe (n := 1)

lemma multibox_mem_coe [DecidableEq F] : φ ∈ s.multibox n ↔ φ ∈ □''^[n](↑s : Set F) := by constructor <;> simp_all

lemma box_mem_coe [DecidableEq F] : φ ∈ s.box ↔ φ ∈ □''(↑s : Set F) := by simp;

lemma premultibox_coe : (s.premultibox n) = □''⁻¹^[n](s : Set F) := by simp_all

lemma prebox_coe : s.prebox = □''⁻¹(↑s : Set F) := by simpa using premultibox_coe (n := 1)

lemma premultibox_multibox_eq_of_subset_multibox
  [DecidableEq F]
  {s : Finset F} {t : Set F} (hs : ↑s ⊆ □''^[n]t) : (s.premultibox n).multibox n = s := by
  have := Set.eq_premultibox_multibox_of_subset_premultibox hs;
  rw [←premultibox_coe, ←multibox_coe] at this;
  exact Finset.coe_inj.mp this;

lemma prebox_box_eq_of_subset_box [DecidableEq F] {s : Finset F} {t : Set F} (hs : ↑s ⊆ □''t) : s.prebox.box = s
  := by simpa using premultibox_multibox_eq_of_subset_multibox (n := 1) hs

end


section

variable [Dia F]

@[simp] lemma eq_dia_multidia_one [DecidableEq F] : s.dia = s.multidia 1 := by rfl

@[simp] lemma eq_predia_premultidia_one : s.predia = s.premultidia 1 := by rfl

lemma multidia_coe [DecidableEq F] : (s.multidia n) = ◇''^[n](s : Set F) := by simp_all

lemma dia_coe [DecidableEq F] : s.dia = ◇''(s : Set F) := by simpa using multidia_coe (n := 1)

lemma multidia_mem_coe [DecidableEq F] : φ ∈ s.multidia n ↔ φ ∈ ◇''^[n](↑s : Set F) := by constructor <;> simp_all

lemma dia_mem_coe [DecidableEq F] : φ ∈ s.dia ↔ φ ∈ ◇''(↑s : Set F) := by simp;

lemma premultidia_coe : (s.premultidia n) = ◇''⁻¹^[n](s : Set F) := by simp_all

lemma predia_coe : s.predia = ◇''⁻¹(↑s : Set F) := by simpa using premultidia_coe (n := 1)

lemma premultidia_multidia_eq_of_subset_multidia
  [DecidableEq F]
  {s : Finset F} {t : Set F} (hs : ↑s ⊆ ◇''^[n]t) : (s.premultidia n).multidia n = s := by
  have := Set.eq_premultidia_multidia_of_subset_premultidia hs;
  rw [←premultidia_coe, ←multidia_coe] at this;
  exact Finset.coe_inj.mp this;

lemma predia_dia_eq_of_subset_dia [DecidableEq F] {s : Finset F} {t : Set F} (hs : ↑s ⊆ ◇''t) : s.predia.dia = s
  := by simpa using premultidia_multidia_eq_of_subset_multidia (n := 1) hs

end

end Finset



section

variable [DecidableEq F]

protected noncomputable abbrev List.multibox [Box F] (n : ℕ) : List F → List F
  | [] => []
  | φ :: l => □^[n]φ :: List.multibox n l
notation "□'^[" n:90 "]" l:80 => List.multibox n l

protected noncomputable abbrev List.multidia [Dia F] (n : ℕ) : List F → List F
  | [] => []
  | φ :: l => ◇^[n]φ :: List.multidia n l
notation "◇'^[" n:90 "]" l:80 => List.multidia n l

protected noncomputable abbrev List.box [Box F] : List F → List F := List.multibox (n := 1)
prefix:80 "□'" => List.box

protected noncomputable abbrev List.dia [Dia F] : List F → List F := List.multidia (n := 1)
prefix:80 "◇'" => List.dia


protected noncomputable abbrev List.premultibox [Box F] (n : ℕ) : List F → List F := λ l => Finset.premultibox n l.toFinset |>.toList
notation "□'⁻¹^[" n:90 "]" l:80 => List.premultibox n l

protected noncomputable abbrev List.premultidia [Dia F] (n : ℕ) : List F → List F := λ l => Finset.premultidia n l.toFinset |>.toList
notation "◇'⁻¹^[" n:90 "]" l:80 => List.premultidia n l

protected noncomputable abbrev List.prebox [Box F] : List F → List F := List.premultibox (n := 1)
prefix:80 "□'⁻¹" => List.prebox

protected noncomputable abbrev List.predia [Dia F] : List F → List F := List.premultidia (n := 1)
prefix:80 "◇'⁻¹" => List.predia

end

namespace List

variable {l : List F} {s : Set F} {φ : F}


lemma forall_multibox_of_subset_multibox [Box F] (h : ∀ φ ∈ l, φ ∈ □''^[n]s) : ∀ φ ∈ l, ∃ ψ ∈ s, φ = □^[n]ψ := by
  intro φ hp;
  obtain ⟨ψ, _, rfl⟩ := h φ hp;
  use ψ;

lemma forall_box_of_subset_box [Box F] (h : ∀ φ ∈ l, φ ∈ □''s) : ∀ φ ∈ l, ∃ ψ ∈ s, φ = □ψ := by
  simpa using forall_multibox_of_subset_multibox (n := 1) h


lemma forall_multidia_of_subset_multidia [Dia F] (h : ∀ φ ∈ l, φ ∈ ◇''^[n]s) : ∀ φ ∈ l, ∃ ψ ∈ s, φ = ◇^[n]ψ := by
  intro φ hp;
  obtain ⟨ψ, _, rfl⟩ := h φ hp;
  use ψ;

lemma forall_dia_of_subset_dia [Dia F] (h : ∀ φ ∈ l, φ ∈ ◇''s) : ∀ φ ∈ l, ∃ ψ ∈ s, φ = ◇ψ := by
  simpa using forall_multidia_of_subset_multidia (n := 1) h


variable [DecidableEq F]

section

variable [Box F]

@[simp] lemma eq_box_multibox_one : □'l = □'^[1]l := by rfl

@[simp] lemma eq_prebox_premultibox_one : □'⁻¹l = □'⁻¹^[1]l := by rfl


@[simp] lemma multibox_nil : (□'^[n]([] :List F)) = [] := by simp;

@[simp] lemma box_nil : (□'([] : List F)) = [] := by simp;


@[simp] lemma premultibox_nil : (□'⁻¹^[n]([] :List F)) = [] := by simp;

@[simp] lemma prebox_nil : (□'⁻¹([] : List F)) = [] := by simp;


@[simp] lemma multibox_single : (□'^[n][φ]) = [□^[n]φ] := by simp;

@[simp] lemma box_single : (□'[φ]) = [□φ] := by simp;

lemma multibox_mem_of (h : φ ∈ l) : □^[n]φ ∈ □'^[n]l := by
  induction l with
  | nil => simp at h;
  | cons ψ l ih =>
    rcases (by simpa using h) with (rfl | h);
    . tauto;
    . tauto;

lemma box_mem_of (h : φ ∈ l) : □φ ∈ □'l := by simpa using multibox_mem_of h

lemma multibox_nonempty (h : l ≠ []) : □'^[n]l ≠ [] := by
  induction l <;> simp_all;

lemma box_nonempty (h : l ≠ []) : □'l ≠ [] := by simpa using multibox_nonempty h

lemma exists_of_multibox (h : φ ∈ □'^[n]l) : ∃ ψ ∈ l, φ = □^[n]ψ := by
  induction l with
  | nil => simp at h;
  | cons ψ l ih =>
    simp only [mem_cons] at h;
    rcases h with (h | h);
    . use ψ; tauto;
    . obtain ⟨ξ, hξ₁, hξ₂⟩ := ih h;
      use ξ;
      constructor <;> tauto;

lemma exists_of_box (h : φ ∈ □'l) : ∃ ψ ∈ l, φ = □ψ := by simpa using exists_of_multibox h

lemma mem_cancel_multibox_premultibox (h : φ ∈ □'^[n]□'⁻¹^[n]l) : φ ∈ l := by
  induction l with
  | nil => simp at h;
  | cons ψ l ih =>
    obtain ⟨ξ, hξ, rfl⟩ := exists_of_multibox h;
    clear h;
    simp only [Finset.mem_toList, toFinset_cons, Finset.mem_preimage, Finset.mem_insert, mem_toFinset] at hξ;
    rcases hξ with (hξ | hξ);
    . subst hξ; tauto;
    . tauto;

lemma mem_cancel_box_prebox (h : φ ∈ □'□'⁻¹l) : φ ∈ l := by simpa using mem_cancel_multibox_premultibox h

lemma mem_decancel_multibox_premultibox (h : □^[n]φ ∈ l) : (□^[n]φ) ∈ □'^[n]□'⁻¹^[n]l := by
  apply multibox_mem_of;
  simpa;

lemma mem_decancel_box_prebox (h : □φ ∈ l) : □φ ∈ □'□'⁻¹l := by simpa using mem_decancel_multibox_premultibox h

/-
lemma multibox_cons (hl : φ ∉ l) : □'^[n](φ :: l) ~ □^[n]φ :: □'^[n]l := by
  simp [List.multibox];
  apply Finset.toList_insert;
  simp_all;
lemma box_cons (hl : φ ∉ l) : □'(φ :: l) ~ □φ :: □'l := by simpa using multibox_cons hl
-/

end

section

variable [Dia F]

@[simp] lemma eq_dia_multidia_one : ◇'l = ◇'^[1]l := by rfl

@[simp] lemma eq_predia_premultidia_one : ◇'⁻¹l = ◇'⁻¹^[1]l := by rfl


@[simp] lemma multidia_nil : (◇'^[n]([] :List F)) = [] := by simp;

@[simp] lemma dia_nil : (◇'([] : List F)) = [] := by simp;


@[simp] lemma premultidia_nil : (◇'⁻¹^[n]([] :List F)) = [] := by simp;

@[simp] lemma predia_nil : (◇'⁻¹([] : List F)) = [] := by simp;


@[simp] lemma multidia_single : (◇'^[n][φ]) = [◇^[n]φ] := by simp;

@[simp] lemma dia_single : (◇'[φ]) = [◇φ] := by simp;

lemma multidia_mem_of (h : φ ∈ l) : ◇^[n]φ ∈ ◇'^[n]l := by
  induction l with
  | nil => simp at h;
  | cons ψ l ih =>
    rcases (by simpa using h) with (rfl | h);
    . tauto;
    . tauto;

lemma dia_mem_of (h : φ ∈ l) : ◇φ ∈ ◇'l := by simpa using multidia_mem_of h

lemma multidia_nonempty (h : l ≠ []) : ◇'^[n]l ≠ [] := by
  induction l <;> simp_all;

lemma dia_nonempty (h : l ≠ []) : ◇'l ≠ [] := by simpa using multidia_nonempty h

lemma exists_of_multidia (h : φ ∈ ◇'^[n]l) : ∃ ψ ∈ l, φ = ◇^[n]ψ := by
  induction l with
  | nil => simp at h;
  | cons ψ l ih =>
    simp only [mem_cons] at h;
    rcases h with (h | h);
    . use ψ; tauto;
    . obtain ⟨ξ, hξ₁, hξ₂⟩ := ih h;
      use ξ;
      constructor <;> tauto;

lemma exists_of_dia (h : φ ∈ ◇'l) : ∃ ψ ∈ l, φ = ◇ψ := by simpa using exists_of_multidia h

lemma mem_cancel_multidia_premultidia (h : φ ∈ ◇'^[n]◇'⁻¹^[n]l) : φ ∈ l := by
  induction l with
  | nil => simp at h;
  | cons ψ l ih =>
    obtain ⟨ξ, hξ, rfl⟩ := exists_of_multidia h;
    clear h;
    simp only [Finset.mem_toList, toFinset_cons, Finset.mem_preimage, Finset.mem_insert, mem_toFinset] at hξ;
    rcases hξ with (hξ | hξ);
    . subst hξ; tauto;
    . tauto;

lemma mem_cancel_dia_predia (h : φ ∈ ◇'◇'⁻¹l) : φ ∈ l := by simpa using mem_cancel_multidia_premultidia h

lemma mem_decancel_multidia_premultidia (h : ◇^[n]φ ∈ l) : (◇^[n]φ) ∈ ◇'^[n]◇'⁻¹^[n]l := by
  apply multidia_mem_of;
  simpa;

lemma mem_decancel_dia_predia (h : ◇φ ∈ l) : ◇φ ∈ ◇'◇'⁻¹l := by simpa using mem_decancel_multidia_premultidia h


/-
lemma multidia_cons (hl : φ ∉ l) : ◇'^[n](φ :: l) ~ ◇^[n]φ :: ◇'^[n]l := by
  simp [List.multidia];
  apply Finset.toList_insert;
  simp_all;

lemma dia_cons (hl : φ ∉ l) : ◇'(φ :: l) ~ ◇φ :: ◇'l := by simpa using multidia_cons hl
-/

end

end List

end
