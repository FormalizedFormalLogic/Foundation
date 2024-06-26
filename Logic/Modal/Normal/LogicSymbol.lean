 import Logic.Logic.LogicSymbol

namespace LO.Modal.Normal

@[notation_class] class Box (α : Sort _) where
  box : α → α

@[notation_class] class Dia (α : Sort _) where
  dia : α → α

class ModalLogicSymbol (α : Sort _) extends LogicSymbol α, Box α, Dia α

prefix:74 "□" => Box.box
prefix:74 "◇" => Dia.dia

attribute [match_pattern]
  Box.box
  Dia.dia

/-- Diamond(`◇`) defined by Box(`□`) -/
class ModalDuality (F : Type*) [ModalLogicSymbol F] where
  dia {p : F} : ◇p = ~(□(~p))

attribute [simp] ModalDuality.dia

/-- Box(`□`) defined by Diamond(`◇`) -/
class ModalDuality' (F : Type*) [ModalLogicSymbol F] where
  box {p : F} : □p = ~(◇(~p))

attribute [simp] ModalDuality'.box

end LO.Modal.Normal


namespace Set

open LO.Modal.Normal

variable [ModalLogicSymbol α]

def box (s : Set α) : Set α := Box.box '' s

@[simp]
lemma box_empty : (∅ : Set α).box = ∅ := by simp [Set.box]

lemma box_subset {s t : Set α} (h : s ⊆ t) : s.box ⊆ t.box := by simp_all [Set.subset_def, box]; aesop;

lemma box_union {s t : Set α} : (s ∪ t).box = s.box ∪ t.box := by simp_all [Set.image_union, box];

@[simp]
lemma box_mem_intro {s : Set α} {a : α} : a ∈ s → □a ∈ s.box := by simp_all [box]; aesop;

lemma box_mem_iff {s : Set α} {p : α} : p ∈ s.box ↔ (∃ q ∈ s, □q = p) := by simp_all [Set.mem_image, box]


def dia (s : Set α) : Set α := Dia.dia '' s

@[simp]
lemma dia_empty : (∅ : Set α).dia = ∅ := by simp [Set.dia]

lemma dia_subset {s t : Set α} (h : s ⊆ t) : s.dia ⊆ t.dia := by simp_all [Set.subset_def, dia]; aesop;

lemma dia_union {s t : Set α} : (s ∪ t).dia = s.dia ∪ t.dia := by simp_all [Set.image_union, dia];

@[simp]
lemma dia_mem_intro {s : Set α} {a : α} : a ∈ s → ◇a ∈ s.dia := by simp_all [dia]; aesop;

lemma dia_mem_iff {s : Set α} {p : α} : p ∈ s.dia ↔ (∃ q ∈ s, ◇q = p) := by simp_all [Set.mem_image, dia]


def prebox (s : Set α) := Box.box ⁻¹' s

@[simp]
lemma prebox_box_eq (s : Set α) : s.prebox.box = { □p | (p : α) (_ : □p ∈ s) } := by aesop;

@[simp]
lemma prebox_box_subset {s : Set α} : s.prebox.box ⊆ s := by simp [Set.subset_def];

lemma prebox_subset {s t : Set α} (h : s ⊆ t) : s.prebox ⊆ t.prebox := by simp_all [Set.subset_def, prebox];


def predia (s : Set α) := Dia.dia ⁻¹' s

@[simp]
lemma predia_dia_eq (s : Set α) : s.predia.dia = { ◇p | (p : α) (_ : ◇p ∈ s) } := by aesop;

@[simp]
lemma predia_dia_subset {s : Set α} : s.predia.dia ⊆ s := by simp [Set.subset_def];

lemma predia_subset {s t : Set α} (h : s ⊆ t) : s.predia ⊆ t.predia := by simp_all [Set.subset_def, predia];

end Set

/-
namespace Finset

open LO.Modal.Normal

variable [ModalLogicSymbol α] [DecidableEq α]

def box (s : Finset α) : Finset α := s.image Box.box

lemma box_union {s t : Finset α} : ((s ∪ t).box : Finset α) = (s.box ∪ t.box : Finset α) := by simp_all [Finset.image_union, box];

@[simp]
lemma box_coe {s : Finset α} : (↑s : Set α).box = ↑(s.box) := by simp only [Set.box, Finset.box, Finset.coe_image];


def dia (s : Finset α) : Finset α := s.image Dia.dia

lemma dia_union {s t : Finset α} : ((s ∪ t).dia : Finset α) = (s.dia ∪ t.dia : Finset α) := by simp_all [Finset.image_union, dia];

@[simp]
lemma dia_coe {s : Finset α} :(↑s : Set α).dia = ↑(s.dia) := by simp only [Set.dia, Finset.dia, Finset.coe_image];

end Finset
-/
