 import Logic.Logic.LogicSymbol

namespace LO.Modal.Normal

@[notation_class] class Box (α : Sort _) where
  box : α → α

@[notation_class] class Dia (α : Sort _) where
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

attribute [simp] ModalDuality.dia_to_box

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

class ModalInj (F) [Box F] [Dia F] where
  box_inj : ∀ {p q : F}, (□p = □q) ↔ (p = q)
  dia_inj : ∀ {p q : F}, (◇p = ◇q) ↔ (p = q)

attribute [simp] ModalInj.box_inj ModalInj.dia_inj

@[simp]
lemma ModalInj.multibox_inj [Box F] [Dia F] [ModalInj F] {n} {p q : F} : (□[n]p = □[n]q) ↔ (p = q) := by induction n <;> simp [*]

@[simp]
lemma ModalInj.multidia_inj [Box F] [Dia F] [ModalInj F] {n} {p q : F} : (◇[n]p = ◇[n]q) ↔ (p = q) := by induction n <;> simp [*]

end LO.Modal.Normal


namespace Set

open LO.Modal.Normal

variable [ModalLogicSymbol α] [ModalInj α]

def box (s : Set α) : Set α := Box.box '' s

@[simp]
lemma box_empty : (∅ : Set α).box = ∅ := by simp [Set.box]

lemma box_subset {s t : Set α} (h : s ⊆ t) : s.box ⊆ t.box := by simp_all [Set.subset_def, box];

lemma box_union {s t : Set α} : (s ∪ t).box = s.box ∪ t.box := by simp_all [Set.image_union, box];

@[simp]
lemma box_mem_intro {s : Set α} {a : α} : a ∈ s → □a ∈ s.box := by simp_all [box];

lemma box_mem_iff {s : Set α} {p : α} : p ∈ s.box ↔ (∃ q ∈ s, □q = p) := by simp_all [Set.mem_image, box]

lemma box_injective (h : Function.Injective (λ {p : α} => Box.box p)) : Function.Injective (λ {s : Set α} => Set.box s) := Function.Injective.image_injective h

lemma box_injOn {s : Set α} : Set.InjOn Box.box s := by simp [Set.InjOn]

lemma forall_box_of_subset_box {s t : Set α} (h : s ⊆ t.box) : ∀ p ∈ s, ∃ q ∈ t, p = □q := by
  intro p hp;
  obtain ⟨q, hq₁, hq₂⟩ := h hp;
  use q;
  simp_all;

def prebox (s : Set α) := Box.box ⁻¹' s

lemma prebox_box_eq_of_surjective (h : Function.Surjective (λ {p : α} => Box.box p)) {s : Set α} : s.prebox.box = s := by
  apply Set.image_preimage_eq;
  simpa;

lemma box_prebox_eq_of_injective (h : Function.Injective (λ {p : α} => Box.box p)) {s : Set α} : s.box.prebox = s := by
  apply Set.preimage_image_eq ;
  simpa;

@[simp]
lemma prebox_box_eq {s : Set α} : s.prebox.box = { □p | (p : α) (_ : □p ∈ s) } := by simp_all; rfl;

lemma prebox_box_eq_of_subset_box {s t : Set α} (hs : s ⊆ t.box) : s.prebox.box = s := by
  simp only [prebox_box_eq];
  apply Set.eq_of_subset_of_subset;
  . intro p hp;
    obtain ⟨q, hq₁, hq₂⟩ := hp;
    simp_all;
  . intro p hp;
    have ⟨q, _⟩ := forall_box_of_subset_box hs p hp;
    simp_all;

@[simp]
lemma prebox_box_subset {s : Set α} : s.prebox.box ⊆ s := by simp [Set.subset_def];

lemma prebox_subset {s t : Set α} (h : s ⊆ t) : s.prebox ⊆ t.prebox := by simp_all [Set.subset_def, prebox];

lemma subset_prebox_iff_box_subset {s t : Set α} (h : s ⊆ t.prebox) : s.box ⊆ t := by
  intro p hp;
  obtain ⟨_, h₁, h₂⟩ := box_subset h hp;
  subst h₂;
  assumption;

def multibox (n : ℕ) (s : Set α) : Set α := (Box.multibox n) '' s

@[simp]
lemma multibox_zero (s : Set α) : s.multibox 0 = s := by simp [Set.multibox]

@[simp]
lemma multibox_mem_intro {s : Set α} {a : α} {n : ℕ} : a ∈ s → □[n]a ∈ s.multibox n := by simp_all [Set.multibox];

lemma multibox_subset {s t : Set α} (h : s ⊆ t) : s.multibox n ⊆ t.multibox n := by simp_all [Set.subset_def, multibox];

lemma multibox_injOn {n : ℕ} {s : Set α} : Set.InjOn (Box.multibox n) (Box.multibox n ⁻¹' s) := by simp [Set.InjOn];

lemma forall_multibox_of_subset_multibox {s t : Set α} (h : s ⊆ t.multibox n) : ∀ p ∈ s, ∃ q ∈ t, p = □[n]q := by
  intro p hp;
  obtain ⟨q, hq₁, hq₂⟩ := h hp;
  use q;
  simp_all;

def premultibox (n : ℕ) (s : Set α) := Box.multibox n ⁻¹' s

@[simp]
lemma premultibox_multibox_eq {s : Set α} : (s.premultibox n).multibox n = { □[n]p | (p : α) (_ : □[n]p ∈ s) } := by simp_all; rfl;

lemma premultibox_multibox_eq_of_subset_premultibox {s t : Set α} (hs : s ⊆ t.multibox n) : (s.premultibox n).multibox n = s := by
  simp only [premultibox_multibox_eq];
  apply Set.eq_of_subset_of_subset;
  . intro p hp;
    obtain ⟨q, hq₁, hq₂⟩ := hp;
    simp_all;
  . intro p hp;
    obtain ⟨q, _, hq₂⟩ := forall_multibox_of_subset_multibox hs p hp;
    simp_all;

lemma premultibox_subset {s t : Set α} (h : s ⊆ t) : s.premultibox n ⊆ t.premultibox n := by simp_all [Set.subset_def, premultibox];

lemma subset_premulitibox_iff_multibox_subset {s t : Set α} (h : s ⊆ t.premultibox n) : s.multibox n ⊆ t := by
  intro p hp;
  obtain ⟨_, h₁, h₂⟩ := multibox_subset h hp;
  subst h₂;
  assumption;

lemma subset_multibox_iff_premulitibox_subset {s t : Set α} (h : s ⊆ t.multibox n) : s.premultibox n ⊆ t := by
  intro p hp;
  obtain ⟨_, h₁, h₂⟩ := premultibox_subset h hp;
  simp_all;

lemma multibox_premultibox_eq_of_injective (h : Function.Injective (λ {p : α} => Box.multibox n p)) {s : Set α} : (s.multibox n).premultibox n = s := by
  apply Set.preimage_image_eq;
  simpa;

def dia (s : Set α) : Set α := Dia.dia '' s

@[simp]
lemma dia_empty : (∅ : Set α).dia = ∅ := by simp [Set.dia]

lemma dia_subset {s t : Set α} (h : s ⊆ t) : s.dia ⊆ t.dia := by simp_all [Set.subset_def, dia];

lemma dia_union {s t : Set α} : (s ∪ t).dia = s.dia ∪ t.dia := by simp_all [Set.image_union, dia];

@[simp]
lemma dia_mem_intro {s : Set α} {a : α} : a ∈ s → ◇a ∈ s.dia := by simp_all [dia];

lemma dia_mem_iff {s : Set α} {p : α} : p ∈ s.dia ↔ (∃ q ∈ s, ◇q = p) := by simp_all [Set.mem_image, dia]

lemma dia_injective (h : Function.Injective (λ {p : α} => Dia.dia p)) : Function.Injective (λ {s : Set α} => Set.dia s) := Function.Injective.image_injective h

lemma dia_injOn {s : Set α} : Set.InjOn Dia.dia s := by simp [Set.InjOn]

lemma forall_dia_of_subset_dia {s t : Set α} (h : s ⊆ t.dia) : ∀ p ∈ s, ∃ q ∈ t, p = ◇q := by
  intro p hp;
  obtain ⟨q, hq₁, hq₂⟩ := h hp;
  use q;
  simp_all;

def predia (s : Set α) := Dia.dia ⁻¹' s

@[simp]
lemma predia_dia_eq {s : Set α} : s.predia.dia = { ◇p | (p : α) (_ : ◇p ∈ s) } := by simp_all; rfl;

lemma predia_dia_eq_of_subset_dia {s t : Set α} (hs : s ⊆ t.dia) : s.predia.dia = s := by
  simp only [predia_dia_eq];
  apply Set.eq_of_subset_of_subset;
  . intro p hp;
    obtain ⟨q, hq₁, hq₂⟩ := hp;
    simp_all;
  . intro p hp;
    obtain ⟨q, _, hq₂⟩ := forall_dia_of_subset_dia hs p hp;
    simp_all;

lemma dia_predia_eq_of_injectve (h : Function.Injective (λ {p : α} => Dia.dia p)) {s : Set α} : s.dia.predia = s := by
  apply Function.Injective.preimage_image;
  exact h;

@[simp]
lemma predia_dia_subset {s : Set α} : s.predia.dia ⊆ s := by simp [Set.subset_def];

lemma predia_subset {s t : Set α} (h : s ⊆ t) : s.predia ⊆ t.predia := by simp_all [Set.subset_def, predia];

lemma subset_predia_iff_dia_subset {s t : Set α} (h : s ⊆ t.predia) : s.dia ⊆ t := by
  intro p hp;
  obtain ⟨_, h₁, h₂⟩ := dia_subset h hp;
  subst h₂;
  assumption;

lemma subset_dia_iff_predia_subset {s t : Set α} (h : s ⊆ t.dia) : s.predia ⊆ t := by
  intro p hp;
  obtain ⟨_, h₁, h₂⟩ := predia_subset h hp;
  simp_all;

def multidia (n : ℕ) (s : Set α) : Set α := (Dia.multidia n) '' s

@[simp]
lemma multidia_zero (s : Set α) : s.multidia 0 = s := by simp [Set.multidia]

@[simp]
lemma multidia_mem_intro {s : Set α} {a : α} {n : ℕ} : a ∈ s → ◇[n]a ∈ s.multidia n := by simp_all [Set.multidia];

lemma multidia_subset {s t : Set α} (h : s ⊆ t) : s.multidia n ⊆ t.multidia n := by simp_all [Set.subset_def, multidia];

lemma multidia_injOn {n : ℕ} {s : Set α} : Set.InjOn (Dia.multidia n) (Dia.multidia n ⁻¹' s) := by simp [Set.InjOn];

lemma forall_multidia_of_subset_multidia {s t : Set α} (h : s ⊆ t.multidia n) : ∀ p ∈ s, ∃ q ∈ t, p = ◇[n]q := by
  intro p hp;
  obtain ⟨q, hq₁, hq₂⟩ := h hp;
  use q;
  simp_all;

def premultidia (n : ℕ) (s : Set α) := Dia.multidia n ⁻¹' s

@[simp]
lemma premultidia_multidia_eq {s : Set α} : (s.premultidia n).multidia n = { ◇[n]p | (p : α) (_ : ◇[n]p ∈ s) } := by simp_all; rfl;

lemma premultidia_multidia_eq_of_subset_premultidia {s t : Set α} (hs : s ⊆ t.multidia n) : (s.premultidia n).multidia n = s := by
  simp only [premultidia_multidia_eq];
  apply Set.eq_of_subset_of_subset;
  . intro p hp;
    obtain ⟨q, hq₁, hq₂⟩ := hp;
    simp_all;
  . intro p hp;
    obtain ⟨q, _, hq₂⟩ := forall_multidia_of_subset_multidia hs p hp;
    simp_all;

lemma premultidia_subset {s t : Set α} (h : s ⊆ t) : s.premultidia n ⊆ t.premultidia n := by simp_all [Set.subset_def, premultidia];

lemma subset_premulitidia_iff_multidia_subset {s t : Set α} (h : s ⊆ t.premultidia n) : s.multidia n ⊆ t := by
  intro p hp;
  obtain ⟨_, h₁, h₂⟩ := multidia_subset h hp;
  subst h₂;
  assumption;

lemma subset_multidia_iff_premulitidia_subset {s t : Set α} (h : s ⊆ t.multidia n) : s.premultidia n ⊆ t := by
  intro p hp;
  obtain ⟨_, h₁, h₂⟩ := premultidia_subset h hp;
  simp_all;

lemma multidia_premultidia_eq_of_injective (h : Function.Injective (λ {p : α} => Dia.multidia n p)) {s : Set α} : (s.multidia n).premultidia n = s := by
  apply Set.preimage_image_eq;
  simpa;

end Set


namespace Finset

open LO.Modal.Normal

variable [ModalLogicSymbol α] [DecidableEq α] [ModalInj α]

def box (s : Finset α) : Finset α := s.image Box.box

lemma box_union {s t : Finset α} : ((s ∪ t).box : Finset α) = (s.box ∪ t.box : Finset α) := by simp_all [Finset.image_union, box];

@[simp]
lemma box_coe {s : Finset α} : (↑s : Set α).box = ↑(s.box) := by simp only [Set.box, Finset.box, Finset.coe_image];

noncomputable def prebox (s : Finset α) := s.preimage Box.box Set.box_injOn

@[simp]
lemma prebox_coe {s : Finset α} : (↑s : Set α).prebox = ↑(s.prebox) := by simp_all [Set.prebox, Finset.prebox, Finset.coe_preimage];

def multibox (n : ℕ) (s : Finset α) : Finset α := s.image (Box.multibox n)

def dia (s : Finset α) : Finset α := s.image Dia.dia

lemma dia_union {s t : Finset α} : ((s ∪ t).dia : Finset α) = (s.dia ∪ t.dia : Finset α) := by simp_all [Finset.image_union, dia];

@[simp]
lemma dia_coe {s : Finset α} :(↑s : Set α).dia = ↑(s.dia) := by simp only [Set.dia, Finset.dia, Finset.coe_image];

noncomputable def predia (s : Finset α) := s.preimage Dia.dia Set.dia_injOn

@[simp]
lemma predia_coe {s : Finset α} : (↑s : Set α).predia = ↑(s.predia) := by simp_all [Set.predia, Finset.predia, Finset.coe_preimage];

@[simp]
lemma multibox_coe {n : ℕ} {s : Finset α} : (↑s : Set α).multibox n = ↑(s.multibox n) := by simp_all [Set.multibox, Finset.multibox, Finset.coe_image];

def multidia (n : ℕ) (s : Finset α) : Finset α := s.image (Dia.multidia n)

@[simp]
lemma multidia_coe {n : ℕ} {s : Finset α} : (↑s : Set α).multidia n = ↑(s.multidia n) := by simp_all [Set.multidia, Finset.multidia, Finset.coe_image];

noncomputable def premultibox (n : ℕ) (s : Finset α) := s.preimage (Box.multibox n) Set.multibox_injOn

@[simp]
lemma premultibox_coe {n : ℕ} {s : Finset α} : (↑s : Set α).premultibox n = ↑(s.premultibox n) := by simp_all [Set.premultibox, Finset.premultibox, Finset.coe_preimage];

noncomputable def premultidia (n : ℕ) (s : Finset α) := s.preimage (Dia.multidia n) Set.multidia_injOn

@[simp]
lemma premultidia_coe {n : ℕ} {s : Finset α} : (↑s : Set α).premultidia n = ↑(s.premultidia n) := by simp_all [Set.premultidia, Finset.premultidia, Finset.coe_preimage];

lemma premultidia_multidia_eq_of_subset_multidia {s : Finset α} {t : Set α} (hs : ↑s ⊆ t.multidia n) : (s.premultidia n).multidia n = s := by
  simpa using Set.premultidia_multidia_eq_of_subset_premultidia hs;

end Finset
