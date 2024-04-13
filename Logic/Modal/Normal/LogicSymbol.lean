 import Logic.Logic.LogicSymbol

namespace LO.Modal.Normal

@[notation_class]
class Box (α : Sort _) where
  box : α → α

@[notation_class]
class Dia (α : Sort _) where
  dia : α → α

class ModalLogicSymbol (α : Sort _) extends LogicalConnective α, Box α, Dia α

prefix:74 "□" => Box.box
prefix:74 "◇" => Dia.dia

attribute [match_pattern]
  Box.box
  Dia.dia

class ModalDuality (F : Type*) [ModalLogicSymbol F] where
  /-- Diamond(`◇`) defined by Box(`□`) -/
  dia_to_box {p : F} : ◇p = ~(□(~p))

@[simp]
def Box.multibox [Box F] (n : ℕ) (p : F) : F :=
  match n with
  | 0 => p
  | n + 1 => □(multibox n p)

notation:74 "□[" n:90 "]" p:80 => Box.multibox n p

@[simp]
lemma Box.multibox_zero [Box F] (p : F) : □[0]p = p := rfl

@[simp]
lemma Box.multibox_succ [Box F] (n : ℕ) (p : F) : □[(n + 1)]p = □(□[n]p) := rfl

lemma Box.multibox_prepost [Box F] (n : ℕ) (p : F) : □□[n]p = □[n](□p) := by induction n <;> simp_all

@[simp]
def Dia.multidia [Dia F] (n : ℕ) (p : F) : F :=
  match n with
  | 0 => p
  | n + 1 => ◇(multidia n p)

notation:74 "◇[" n:90 "]" p:80 => Dia.multidia n p

@[simp]
lemma Dia.multidia_zero [Dia F] (p : F) : ◇[0]p = p := rfl

@[simp]
lemma Dia.multidia_succ [Dia F] (n : ℕ) (p : F) : ◇[(n + 1)]p = ◇(◇[n]p) := rfl

lemma Dia.multidia_prepost [Dia F] (n : ℕ) (p : F) : ◇◇[n]p = ◇[n](◇p) := by induction n <;> simp_all

class ModalInjective (F) [Box F] [Dia F] where
  box_injective : Function.Injective (Box.box : F → F)
  dia_injective : Function.Injective (Dia.dia : F → F)

variable [Box F] [Dia F] [ModalInjective F]

@[simp]
lemma ModalInjective.box_injective' {p q : F} : □p = □q ↔ p = q := by
  constructor;
  . intro h; exact box_injective h;
  . simp_all;

@[simp]
lemma ModalInjective.dia_injective' {p q : F} : ◇p = ◇q ↔ p = q := by
  constructor;
  . intro h; exact dia_injective h;
  . simp_all;

@[simp]
lemma ModalInjective.multibox_injective' {n} {p q : F} : (□[n]p = □[n]q) ↔ (p = q) := by induction n <;> simp [*]

@[simp]
lemma ModalInjective.multibox_injective : Function.Injective (Box.multibox n : F → F) := by simp [Function.Injective];

@[simp]
lemma ModalInjective.multidia_injective' {n} {p q : F} : (◇[n]p = ◇[n]q) ↔ (p = q) := by induction n <;> simp [*]

lemma ModalInjective.multidia_injective : Function.Injective (Dia.multidia n : F → F) := by simp [Function.Injective];

end LO.Modal.Normal

namespace Set

open LO.Modal.Normal

variable [ModalLogicSymbol α] [ModalInjective α]

variable {s t : Set α} {n : ℕ} {a : α}

def multibox (n : ℕ) (s : Set α) : Set α := (Box.multibox n) '' s

@[simp] lemma multibox_empty : (∅ : Set α).multibox n = ∅ := by simp [multibox]

@[simp] lemma multibox_zero : s.multibox 0 = s := by simp [multibox]

@[simp] lemma multibox_mem_intro : a ∈ s → □[n]a ∈ s.multibox n := by simp_all [multibox];

@[simp] lemma multibox_injOn : Set.InjOn (Box.multibox n) (Box.multibox n ⁻¹' s) := by simp [InjOn];

lemma multibox_subset (h : s ⊆ t) : s.multibox n ⊆ t.multibox n := by simp_all [subset_def, multibox];

@[simp] lemma multibox_union : (s ∪ t).multibox n = (s.multibox n) ∪ (t.multibox n) := by simp_all [image_union, multibox];

lemma multibox_mem_iff : a ∈ s.multibox n ↔ (∃ b ∈ s, □[n]b = a) := by simp_all [Set.mem_image, multibox]

lemma forall_multibox_of_subset_multibox (h : s ⊆ t.multibox n) : ∀ p ∈ s, ∃ q ∈ t, p = □[n]q := by
  intro p hp;
  obtain ⟨q, hq₁, hq₂⟩ := h hp;
  use q;
  simp_all;


@[simp] def box (s : Set α) : Set α := s.multibox 1

@[simp] lemma box_empty : (∅ : Set α).box = ∅ := by simp

@[simp] lemma box_mem_intro {a : α} : a ∈ s → □a ∈ s.box := by apply multibox_mem_intro;

@[simp] lemma box_injOn : Set.InjOn Box.box s := by simp [Set.InjOn]

lemma box_subset (h : s ⊆ t) : s.box ⊆ t.box := by apply multibox_subset; assumption;

@[simp] lemma box_union : (s ∪ t).box = s.box ∪ t.box := by simp;

lemma box_mem_iff {p : α} : p ∈ s.box ↔ (∃ q ∈ s, □q = p) := by apply multibox_mem_iff;

lemma box_injective : Function.Injective (λ {s : Set α} => Set.box s) := Function.Injective.image_injective ModalInjective.box_injective

lemma forall_box_of_subset_box (h : s ⊆ t.box) : ∀ p ∈ s, ∃ q ∈ t, p = □q := forall_multibox_of_subset_multibox h


def premultibox (n : ℕ) (s : Set α) := Box.multibox n ⁻¹' s

@[simp]
lemma multibox_premultibox_eq : (s.multibox n).premultibox n = s := by
  apply Set.preimage_image_eq;
  exact ModalInjective.multibox_injective;

lemma premultibox_multibox_eq_of_subset_premultibox (hs : s ⊆ t.multibox n) : (s.premultibox n).multibox n = s := by
  apply Set.eq_of_subset_of_subset;
  . intro p hp;
    obtain ⟨q, hq₁, hq₂⟩ := hp;
    simp_all [premultibox];
  . intro p hp;
    obtain ⟨q, _, hq₂⟩ := forall_multibox_of_subset_multibox hs p hp;
    simp_all [multibox, premultibox];

@[simp] lemma premultibox_multibox_subset : (s.premultibox n).multibox n ⊆ s := by simp [Set.subset_def, multibox, premultibox];

lemma premultibox_subset (h : s ⊆ t) : s.premultibox n ⊆ t.premultibox n := by simp_all [Set.subset_def, premultibox];

lemma subset_premulitibox_iff_multibox_subset (h : s ⊆ t.premultibox n) : s.multibox n ⊆ t := by
  intro p hp;
  obtain ⟨_, h₁, h₂⟩ := multibox_subset h hp;
  subst h₂;
  assumption;

lemma subset_multibox_iff_premulitibox_subset (h : s ⊆ t.multibox n) : s.premultibox n ⊆ t := by
  intro p hp;
  obtain ⟨_, h₁, h₂⟩ := premultibox_subset h hp;
  simp_all;


@[simp] def prebox (s : Set α) := s.premultibox 1

@[simp] lemma box_prebox_eq : s.box.prebox = s := by simp;

lemma prebox_box_eq_of_subset_box (hs : s ⊆ t.box) : s.prebox.box = s := premultibox_multibox_eq_of_subset_premultibox hs

@[simp] lemma prebox_box_subset : s.prebox.box ⊆ s := by simp;

lemma prebox_subset (h : s ⊆ t) : s.prebox ⊆ t.prebox := premultibox_subset h

lemma subset_prebox_iff_box_subset (h : s ⊆ t.prebox) : s.box ⊆ t := subset_premulitibox_iff_multibox_subset h

lemma subset_box_iff_prebox_subset (h : s ⊆ t.box) : s.prebox ⊆ t := subset_multibox_iff_premulitibox_subset h


def multidia (n : ℕ) (s : Set α) : Set α := (Dia.multidia n) '' s

@[simp] lemma multidia_empty : (∅ : Set α).multidia n = ∅ := by simp [multidia]

@[simp] lemma multidia_zero : s.multidia 0 = s := by simp [multidia]

@[simp] lemma multidia_mem_intro : a ∈ s → ◇[n]a ∈ s.multidia n := by simp_all [multidia];

lemma multidia_subset (h : s ⊆ t) : s.multidia n ⊆ t.multidia n := by simp_all [subset_def, multidia];

@[simp] lemma multidia_union : (s ∪ t).multidia n = (s.multidia n) ∪ (t.multidia n) := by simp_all [image_union, multidia];

@[simp] lemma multidia_injOn : Set.InjOn (Dia.multidia n) (Dia.multidia n ⁻¹' s) := by simp [InjOn];

lemma multidia_mem_iff : a ∈ s.multidia n ↔ (∃ b ∈ s, ◇[n]b = a) := by simp_all [Set.mem_image, multidia]

lemma forall_multidia_of_subset_multidia (h : s ⊆ t.multidia n) : ∀ p ∈ s, ∃ q ∈ t, p = ◇[n]q := by
  intro p hp;
  obtain ⟨q, hq₁, hq₂⟩ := h hp;
  use q;
  simp_all;

@[simp] def dia (s : Set α) : Set α := s.multidia 1

@[simp] lemma dia_empty : (∅ : Set α).dia = ∅ := by simp

@[simp] lemma dia_mem_intro {a : α} : a ∈ s → ◇a ∈ s.dia := by apply multidia_mem_intro;

lemma dia_subset (h : s ⊆ t) : s.dia ⊆ t.dia := by apply multidia_subset; assumption;

@[simp] lemma dia_union : (s ∪ t).dia = s.dia ∪ t.dia := by apply multidia_union;

@[simp] lemma dia_injOn : Set.InjOn Dia.dia s := by simp [Set.InjOn]

lemma dia_mem_iff {p : α} : p ∈ s.dia ↔ (∃ q ∈ s, ◇q = p) := by apply multidia_mem_iff;

lemma dia_injective : Function.Injective (λ {s : Set α} => Set.dia s) := Function.Injective.image_injective ModalInjective.dia_injective

lemma forall_dia_of_subset_dia (h : s ⊆ t.dia) : ∀ p ∈ s, ∃ q ∈ t, p = ◇q := forall_multidia_of_subset_multidia h


def premultidia (n : ℕ) (s : Set α) := Dia.multidia n ⁻¹' s

@[simp]
lemma multidia_premultidia_eq : (s.multidia n).premultidia n = s := by
  apply Set.preimage_image_eq;
  exact ModalInjective.multidia_injective;

lemma premultidia_multidia_eq_of_subset_premultidia (hs : s ⊆ t.multidia n) : (s.premultidia n).multidia n = s := by
  apply Set.eq_of_subset_of_subset;
  . intro p hp;
    obtain ⟨q, hq₁, hq₂⟩ := hp;
    simp_all [premultidia];
  . intro p hp;
    obtain ⟨q, _, hq₂⟩ := forall_multidia_of_subset_multidia hs p hp;
    simp_all [multidia, premultidia];

@[simp] lemma premultidia_multidia_subset : (s.premultidia n).multidia n ⊆ s := by simp [Set.subset_def, multidia, premultidia];

lemma premultidia_subset (h : s ⊆ t) : s.premultidia n ⊆ t.premultidia n := by simp_all [Set.subset_def, premultidia];

lemma subset_premulitidia_iff_multidia_subset (h : s ⊆ t.premultidia n) : s.multidia n ⊆ t := by
  intro p hp;
  obtain ⟨_, h₁, h₂⟩ := multidia_subset h hp;
  subst h₂;
  assumption;

lemma subset_multidia_iff_premulitidia_subset (h : s ⊆ t.multidia n) : s.premultidia n ⊆ t := by
  intro p hp;
  obtain ⟨_, h₁, h₂⟩ := premultidia_subset h hp;
  simp_all;


@[simp] def predia (s : Set α) := s.premultidia 1

@[simp] lemma dia_predia_eq : s.dia.predia = s := by simp;

lemma predia_dia_eq_of_subset_dia (hs : s ⊆ t.dia) : s.predia.dia = s := premultidia_multidia_eq_of_subset_premultidia hs

@[simp] lemma predia_dia_subset : s.predia.dia ⊆ s := by simp;

lemma predia_subset (h : s ⊆ t) : s.predia ⊆ t.predia := premultidia_subset h

lemma subset_predia_iff_dia_subset (h : s ⊆ t.predia) : s.dia ⊆ t := subset_premulitidia_iff_multidia_subset h

lemma subset_dia_iff_predia_subset (h : s ⊆ t.dia) : s.predia ⊆ t := subset_multidia_iff_premulitidia_subset h

end Set


namespace List

open LO.Modal.Normal

variable [ModalLogicSymbol α] [DecidableEq α] [ModalInjective α]

variable {n : ℕ} {l : List α}

def multibox (n : ℕ) (l : List α) : List α := l.map (Box.multibox n)

@[simp] def box (l : List α) : List α := l.multibox 1

@[simp] lemma multibox_empty : ([] : List α).multibox n = [] := by simp [List.multibox]

@[simp] lemma multibox_zero : l.multibox 0 = l := by simp [List.multibox]


def premultibox (n : ℕ) (l : List α) := l.filter (λ p => □[n]p ∈ l)

@[simp] def prebox (l : List α) := premultibox 1 l


def multidia (n : ℕ) (l : List α) : List α := l.map (Dia.multidia n)

@[simp] def dia (l : List α) : List α := l.multidia 1

@[simp] lemma multidia_empty : ([] : List α).multidia n = [] := by simp [List.multidia]

@[simp] lemma multidia_zero : l.multidia 0 = l := by simp [List.multidia]


def premultidia (n : ℕ) (l : List α) := l.filter (λ p => ◇[n]p ∈ l)

@[simp] def predia (l : List α) := premultidia 1 l

end List


namespace Finset

open LO.Modal.Normal

variable [ModalLogicSymbol α] [DecidableEq α] [ModalInjective α]

variable {n : ℕ} {s t : Finset α}

@[simp] noncomputable def multibox (n : ℕ) (s : Finset α) : Finset α := s.toList.multibox n |>.toFinset

@[simp] noncomputable def box (s : Finset α) : Finset α := s.multibox 1

lemma multibox_def : s.multibox n = s.image (Box.multibox n) := by simp [List.multibox, List.toFinset_map];

@[simp] lemma multibox_coe : ↑(s.multibox n) = (↑s : Set α).multibox n := by simp_all [Set.multibox, List.multibox]; rfl;

@[simp] lemma multibox_zero : s.multibox 0 = s := by simp

@[simp]
lemma multibox_union : ((s ∪ t).multibox n : Finset α) = (s.multibox n ∪ t.multibox n : Finset α) := by
  simp [List.toFinset_map, List.multibox];
  aesop;

@[simp] noncomputable def premultibox (n : ℕ) (s : Finset α) := s.preimage (Box.multibox n) (by simp)

@[simp] noncomputable def prebox (s : Finset α) := s.premultibox 1

@[simp] lemma premultibox_coe : ↑(s.premultibox n) = (↑s : Set α).premultibox n := by apply Finset.coe_preimage;

lemma premultibox_multibox_eq_of_subset_multibox {s : Finset α} {t : Set α} (hs : ↑s ⊆ t.multibox n) : (s.premultibox n).multibox n = s := by
  have := Set.premultibox_multibox_eq_of_subset_premultibox hs;
  rw [←premultibox_coe, ←multibox_coe] at this;
  exact coe_inj.mp this;


@[simp] noncomputable def multidia (n : ℕ) (s : Finset α) : Finset α := s.toList.multidia n |>.toFinset

@[simp] noncomputable def dia (s : Finset α) : Finset α := s.multidia 1

@[simp] lemma multidia_coe : ↑(s.multidia n) = (↑s : Set α).multidia n := by simp_all [Set.multidia, List.multidia]; rfl;

@[simp] lemma multidia_zero : s.multidia 0 = s := by simp

@[simp]
lemma multidia_union : ((s ∪ t).multidia n : Finset α) = (s.multidia n ∪ t.multidia n : Finset α) := by
  simp [List.toFinset_map, List.multidia];
  aesop;

@[simp] noncomputable def premultidia (n : ℕ) (s : Finset α) := s.preimage (Dia.multidia n) (by simp)

@[simp] noncomputable def predia (s : Finset α) := s.premultidia 1

@[simp] lemma premultidia_coe : ↑(s.premultidia n) = (↑s : Set α).premultidia n := by apply Finset.coe_preimage;

@[simp] lemma predia_coe : ↑(s.predia) = (↑s : Set α).predia := by apply premultidia_coe;

lemma premultidia_multidia_eq_of_subset_multidia {s : Finset α} {t : Set α} (hs : ↑s ⊆ t.multidia n) : (s.premultidia n).multidia n = s := by
  have := Set.premultidia_multidia_eq_of_subset_premultidia hs;
  rw [←premultidia_coe, ←multidia_coe] at this;
  exact coe_inj.mp this;

end Finset
