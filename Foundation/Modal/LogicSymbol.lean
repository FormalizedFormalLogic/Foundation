import Foundation.Logic.LogicSymbol
import Mathlib.Data.PNat.Basic

namespace LO

variable {F} {n m : ℕ} {φ : F}

@[notation_class]
class Box (F : Type*) where
  box : F → F

@[notation_class]
class Dia (F : Type*) where
  dia : F → F

namespace Box

variable [Box F]

prefix:76 "□" => Box.box
attribute [match_pattern] Box.box

abbrev boxItr (n : ℕ) : F → F := (□·)^[n]
notation:76 "□^[" n "]" φ:80 => boxItr n φ

@[simp, grind =] lemma boxItr_zero : (□^[0] φ) = φ := by rfl
@[simp, grind =] lemma boxItr_succ : (□^[n + 1] φ) = □(□^[n] φ) := by apply Function.iterate_succ_apply';
@[simp, grind =] lemma boxItr_add : (□^[n](□^[m]φ)) = □^[(n + m)]φ := by
  induction n with
  | zero => simp;
  | succ n ih => simp [ih, (show n + 1 + m = n + m + 1 by omega)];
@[simp, grind =] lemma boxItr_pred {n : ℕ+} : □(□^[(n - 1)]φ) = □^[n]φ := by induction n <;> simp;


section

variable [DecidableEq F] [Top F] [Wedge F]

noncomputable def boxLe (n : ℕ) (φ : F) := Finset.range (n + 1) |>.image (λ j => □^[j] φ) |>.conj
notation :90 "□^≤[" n "]" φ => boxLe n φ

@[simp, grind =] lemma boxLe_zero : (□^≤[0] φ) = φ := by dsimp [boxLe]; simp;

end

abbrev boxdot [Wedge F] (φ : F) : F := φ ⋏ □φ
prefix:76 "⊡" => boxdot

end Box


namespace Dia

variable [Dia F]

prefix:76 "◇" => Dia.dia
attribute [match_pattern] Dia.dia

abbrev diaItr (n : ℕ) : F → F := (◇·)^[n]
notation:76 "◇^[" n "]" φ:80 => diaItr n φ

@[simp, grind =] lemma diaItr_zero : (◇^[0] φ) = φ := by rfl
@[simp, grind =] lemma diaItr_succ : (◇^[n + 1] φ) = ◇(◇^[n] φ) := by apply Function.iterate_succ_apply';
@[simp, grind =] lemma diaItr_add : (◇^[n](◇^[m]φ)) = ◇^[(n + m)]φ := by
  induction n with
  | zero => simp;
  | succ n ih => simp [ih, (show n + 1 + m = n + m + 1 by omega)];
@[simp, grind =] lemma diaItr_pred {n : ℕ+} : ◇(◇^[(n - 1)]φ) = ◇^[n]φ := by induction n <;> simp;


section

variable [DecidableEq F] [Top F] [Wedge F]

noncomputable def diaLe (n : ℕ) (φ : F) := Finset.range (n + 1) |>.image (λ j => ◇^[j] φ) |>.conj
notation :90 "◇^≤[" n "]" φ => diaLe n φ

@[simp, grind =] lemma diaLe_zero : (◇^≤[0] φ) = φ := by dsimp [diaLe]; simp;

end

abbrev diadot [Vee F] (φ : F) : F := φ ⋎ ◇φ
prefix:76 "⟐" => diadot

end Dia


class BasicModalLogicalConnective (F : Type*) extends LogicalConnective F, Box F, Dia F where

class DiaByBox (F) [Box F] [Dia F] [Tilde F] where
  dia_by_box {φ : F} : ◇φ = ∼□(∼φ)
attribute [grind .] DiaByBox.dia_by_box

class BoxByDia (F) [Box F] [Dia F] [Tilde F] where
  box_by_dia {φ : F} : □φ = ∼◇(∼φ)
attribute [grind .] BoxByDia.box_by_dia

class ModalDeMorgan (F) [BasicModalLogicalConnective F] extends DeMorgan F where
  neg_dia {φ : F} : ∼◇φ = □(∼φ)
  neg_box {φ : F} : ∼□φ = ◇(∼φ)
attribute [grind .] ModalDeMorgan.neg_dia ModalDeMorgan.neg_box

class InjectiveBox (F : Type*) [Box F] where
  inj_box : Function.Injective (□· : F → F)
attribute [simp] InjectiveBox.inj_box

class InjectiveDia (F : Type*) [Dia F] where
  inj_dia : Function.Injective (◇· : F → F)
attribute [simp] InjectiveDia.inj_dia

@[simp]
lemma InjectiveBox.inj_multibox [Box F] [InjectiveBox F] : Function.Injective (□^[n]· : F → F) := by
  apply Function.Injective.iterate;
  simp;

@[simp]
lemma InjectiveDia.inj_multidia [Dia F] [InjectiveDia F] : Function.Injective (◇^[n]· : F → F) := by
  apply Function.Injective.iterate;
  simp;

end LO


section

open LO

variable {I : Type*} {F : Type*} [BasicModalLogicalConnective F]
variable {n : ℕ} {ι : I} {φ : F}

namespace Set.LO

variable {s t : Set F} {n : ℕ}

@[grind] def boxItr (n : ℕ) : Set F → Set F := Set.image (□^[n]·)
notation:90 "□^[" n "]'" s => Set.LO.boxItr n s

abbrev box : Set F → Set F := Set.LO.boxItr 1
prefix:90 "□'" => Set.LO.box

@[grind] def preboxItr (n : ℕ) : Set F → Set F := Set.preimage (□^[n]·)
notation:90 "□⁻¹^[" n "]'" s => Set.LO.preboxItr n s

abbrev prebox : Set F → Set F := preboxItr 1
prefix:90 "□⁻¹'" => Set.LO.prebox

@[simp, grind =] lemma eq_boxItr_one_box : (□^[1]'s) = (□'s) := by rfl
@[simp, grind =] lemma eq_preboxItr_one_prebox : (□⁻¹^[1]' s) = (□⁻¹' s) := by rfl

@[grind <=] lemma boxItr_subset_mono (h : s ⊆ t) : (□^[n]'s) ⊆ (□^[n]'t) := by dsimp [Set.LO.boxItr]; grind
@[grind <=] lemma box_subset_mono (h : s ⊆ t) : □'s ⊆ □'t := by grind;

@[grind <=] lemma mem_boxItr_of_mem (h : φ ∈ s) : (□^[n]φ) ∈ (□^[n]'s) := by dsimp [Set.LO.boxItr]; grind;
@[grind <=] lemma mem_box_of_mem (h : φ ∈ s) : □φ ∈ (□'s) := mem_boxItr_of_mem (n := 1) h

@[grind <=]
lemma preboxItr_subset_mono (h : s ⊆ t) : (□⁻¹^[n]'s) ⊆ (□⁻¹^[n]'t) := by
  dsimp [Set.LO.preboxItr];
  simp_all [Set.subset_def];
@[grind <=]
lemma prebox_subset_mono (h : s ⊆ t) : □⁻¹' s ⊆ □⁻¹' t := by grind;

@[grind =]
lemma iff_mem_preboxItr : φ ∈ (□⁻¹^[n]'s) ↔ (□^[n]φ) ∈ s := by
  dsimp [Set.LO.preboxItr];
  grind;

@[grind →]
lemma mem_of_mem_boxItr [InjectiveBox F] (h : □^[n]φ ∈ □^[n]'s) : φ ∈ s := by
  obtain ⟨ψ, hψ, h_eq⟩ := h;
  exact InjectiveBox.inj_multibox h_eq ▸ hψ;

@[grind →]
lemma mem_of_mem_box [InjectiveBox F] (h : □φ ∈ □'s) : φ ∈ s := mem_of_mem_boxItr (n := 1) h

@[grind! =>]
lemma mem_boxItr_of_mem_boxItr [InjectiveBox F] (h : □^[n]φ ∈ □^[n]'s) : □^[m]φ ∈ □^[m]'s := by
  apply mem_boxItr_of_mem;
  apply mem_of_mem_boxItr h;

@[grind! =>]
lemma exists_of_mem_boxItr (h : φ ∈ □^[n]'s) : ∃ ψ ∈ s, (□^[n]ψ) = φ := by
  dsimp [boxItr] at h;
  grind;
@[grind! =>]
lemma exists_of_mem_box (h : φ ∈ □'s) : ∃ ψ ∈ s, □ψ = φ := exists_of_mem_boxItr (n := 1) h

@[grind] def diaItr (n : ℕ) : Set F → Set F := Set.image (◇^[n]·)
notation:90 "◇^[" n "]'" s => diaItr n s

abbrev dia : Set F → Set F := diaItr 1
prefix:90 "◇'" => dia

@[grind] def prediaItr (n : ℕ) : Set F → Set F := Set.preimage (◇^[n]·)
notation:90 "◇⁻¹^[" n "]'" s => prediaItr n s

abbrev predia : Set F → Set F := prediaItr 1
prefix:90 "◇'⁻¹" => predia

@[simp, grind =] lemma eq_diaItr_one_dia : (◇^[1]'s) = (◇'s) := by rfl
@[simp, grind =] lemma eq_prediaItr_one_predia : (◇⁻¹^[1]' s) = (◇'⁻¹ s) := by rfl

@[grind <=]
lemma diaItr_subset_mono (h : s ⊆ t) : (◇^[n]'s) ⊆ (◇^[n]'t) := by
  dsimp [Set.LO.diaItr];
  grind
@[grind <=] lemma dia_subset_mono (h : s ⊆ t) : dia s ⊆ dia t := by grind;

@[grind <=]
lemma prediaItr_subset_mono (h : s ⊆ t) : (◇⁻¹^[n]'s) ⊆ (◇⁻¹^[n]'t) := by
  dsimp [Set.LO.prediaItr];
  simp_all [Set.subset_def];
@[grind <=]
lemma predia_subset_mono (h : s ⊆ t) : predia s ⊆ predia t := by apply prediaItr_subset_mono h;

end Set.LO



namespace Finset.LO

variable {s t : Finset F} {n : ℕ}

section

@[grind] def boxItr [DecidableEq F] (n : ℕ) : Finset F → Finset F := Finset.image (□^[n]·)
notation:90 "□^[" n "]'" s => Finset.LO.boxItr n s

abbrev box [DecidableEq F] : Finset F → Finset F := boxItr 1
prefix:90 "□'" => Finset.LO.box

variable [DecidableEq F]

@[simp, grind =] lemma eq_boxItr_one_box : (□^[1]'s) = (□'s) := by rfl

@[grind <=] lemma mem_boxItr_of_mem (h : φ ∈ s) : (□^[n]φ) ∈ (□^[n]'s) := by dsimp [Finset.LO.boxItr]; grind;
@[grind <=] lemma mem_box_of_mem (h : φ ∈ s) : □φ ∈ (□'s) := mem_boxItr_of_mem (n := 1) h

@[grind! =>]
lemma exists_of_mem_boxItr (h : φ ∈ □^[n]'s) : ∃ ψ ∈ s, (□^[n]ψ) = φ := by
  dsimp [boxItr] at h;
  grind;
@[grind! =>]
lemma exists_of_mem_box (h : φ ∈ □'s) : ∃ ψ ∈ s, □ψ = φ := exists_of_mem_boxItr (n := 1) h

@[simp, grind =] lemma eq_boxItr_toSet_toSet_boxItr : (↑(□^[n]'s) : Set F) = (□^[n]'(↑s : Set F)) := by
  ext φ;
  simp [Finset.LO.boxItr, Set.LO.boxItr];
@[simp, grind =] lemma eq_box_toSet_toSet_box : (↑(□'s) : Set F) = □'(↑s : Set F) := by grind

end


section

variable [InjectiveBox F]

@[grind]
noncomputable def preboxItr [InjectiveBox F] (n : ℕ) (s : Finset F) : Finset F := s.preimage (□^[n]·) $ by
  intro φ hφ ψ hψ;
  apply InjectiveBox.inj_multibox;
notation:90 "□⁻¹^[" n "]'" s => Finset.LO.preboxItr n s

noncomputable abbrev prebox (s : Finset F) : Finset F := preboxItr 1 s
prefix:90 "□⁻¹'" => Finset.LO.prebox

@[simp, grind =] lemma preboxItr_empty : (□⁻¹^[n]'(∅ : Finset F)) = ∅ := by simp [preboxItr];
@[simp, grind =] lemma prebox_empty : (□⁻¹'(∅ : Finset F)) = ∅ := preboxItr_empty (n := 1)

@[simp, grind =]
lemma preboxItr_singleton : (□⁻¹^[n]'{□^[n]φ} : Finset F) = {φ} := by
  ext ψ;
  simp only [preboxItr, mem_preimage, mem_singleton];
  constructor;
  . apply InjectiveBox.inj_multibox;
  . grind;

@[simp, grind =] lemma eq_preboxItr_one_prebox : (□⁻¹^[1]'s) = (□⁻¹'s) := by rfl

@[grind →]
lemma mem_boxItr_of_mem_preboxItr (h : φ ∈ (□⁻¹^[n]'s)) : (□^[n]φ) ∈ s := by simpa [preboxItr] using h;
@[grind →] lemma mem_box_of_mem_prebox (h : φ ∈ (□⁻¹'s)) : □φ ∈ s := mem_boxItr_of_mem_preboxItr (n := 1) h

@[grind <=] lemma mem_boxItr_preboxItr_of_mem_of_mem_boxItr [DecidableEq F] (h : □^[n]φ ∈ s) : □^[n]φ ∈ □^[n]'□⁻¹^[n]'s := by
  simp [preboxItr, boxItr];
  grind;
@[grind <=] lemma mem_box_prebox_of_mem_of_mem_box [DecidableEq F] (h : □φ ∈ s) : □φ ∈ □'□⁻¹'s := mem_boxItr_preboxItr_of_mem_of_mem_boxItr (n := 1) h

@[grind →] lemma mem_of_mem_boxItr_preboxItr [DecidableEq F]  (h : φ ∈ □^[n]'□⁻¹^[n]'s) : φ ∈ s := by grind;
@[grind →] lemma mem_of_mem_box_prebox [DecidableEq F] (h : φ ∈ □'□⁻¹'s) : φ ∈ s := mem_of_mem_boxItr_preboxItr (n := 1) h


end



section

@[grind] def diaItr [DecidableEq F] (n : ℕ) : Finset F → Finset F := Finset.image (◇^[n]·)
notation:90 "◇^[" n "]'" s => Finset.LO.diaItr n s

abbrev dia [DecidableEq F] : Finset F → Finset F := diaItr 1
prefix:90 "◇'" => Finset.LO.dia

variable [DecidableEq F]

@[simp, grind =] lemma eq_diaItr_one_dia : (◇^[1]'s) = (◇'s) := by rfl

@[grind! =>]
lemma exists_of_mem_diaItr (h : φ ∈ ◇^[n]'s) : ∃ ψ ∈ s, (◇^[n]ψ) = φ := by
  dsimp [diaItr] at h;
  grind;
@[grind! =>]
lemma exists_of_mem_dia (h : φ ∈ ◇'s) : ∃ ψ ∈ s, ◇ψ = φ := exists_of_mem_diaItr (n := 1) h

end


section

@[grind]
def prediaItr (n : ℕ) (s : Finset F) [DecidablePred (λ φ ↦ ◇^[n]φ ∈ s)] : Finset F := { φ ∈ s | (◇^[n]φ) ∈ s }
notation:90 "◇⁻¹^[" n "]'" s => Finset.LO.prediaItr n s

abbrev predia (s : Finset F) [DecidablePred (λ φ ↦ ◇^[1]φ ∈ s)] : Finset F := prediaItr 1 s
prefix:90 "◇'⁻¹" => Finset.LO.predia

@[simp, grind =] lemma eq_prediaItr_one_predia [DecidablePred (λ φ ↦ ◇^[1]φ ∈ s)] : (◇⁻¹^[1]'s) = (◇'⁻¹s) := by rfl

end

end Finset.LO


namespace List.LO

open Classical

variable {s t : List F} {n m : ℕ}

@[grind] def boxItr (n : ℕ) : List F → List F := List.map (□^[n]·)
notation:90 "□^[" n "]'" s => List.LO.boxItr n s

abbrev box : List F → List F := boxItr 1
prefix:90 "□'" => List.LO.box


@[simp, grind =] lemma eq_boxItr_zero : (□^[0]'s) = s := by induction s <;> simp_all [boxItr];
@[simp, grind =] lemma eq_boxItr_one_box : (□^[1]'s) = □'s := by rfl

@[grind <=] lemma not_nil_boxItr_of_not_nil (h : s ≠ []) : (□^[n]'s) ≠ [] := by induction s <;> simp_all [boxItr];
@[grind <=] lemma not_nil_box_of_not_nil (h : s ≠ []) : (□'s) ≠ [] := not_nil_boxItr_of_not_nil (n := 1) h

@[simp, grind =] lemma boxItr_nil : (□^[n]'([] : List F)) = [] := by rfl

@[simp, grind =] lemma boxItr_single : (□^[n]'[φ]) = [□^[n]φ] := by dsimp [boxItr];

@[simp, grind =] lemma eq_boxItr_conn : (□^[n]'(ψ :: s)) = (□^[n]ψ) :: (□^[n]'s) := by induction s <;> simp_all [boxItr];
@[simp, grind =] lemma eq_box_conn : (□' (ψ :: s)) = (□ψ) :: □'s := eq_boxItr_conn (n := 1)

@[grind =] lemma mem_boxItr_cons : φ ∈ (□^[n]'(ψ :: s)) ↔ (φ = □^[n]ψ) ∨ (φ ∈ (□^[n]'s)) := by grind;
@[grind =] lemma mem_box_cons : φ ∈ (□'(ψ :: s)) ↔ (φ = □ψ) ∨ (φ ∈ □'s) := mem_boxItr_cons (n := 1)

@[grind =_ ]
lemma mem_boxItr_add : φ ∈ (□^[m + n]' s) ↔ φ ∈ □^[n]'□^[m]'s := by
  dsimp [boxItr];
  grind;


@[grind <=]
lemma mem_boxItr_of_mem (h : φ ∈ s) : (□^[n]φ) ∈ (□^[n]'s) := by
  dsimp [boxItr];
  grind;

@[grind =>]
lemma exists_of_mem_boxItr (h : φ ∈ □^[n]'s) : ∃ ψ ∈ s, (□^[n]ψ) = φ := by
  dsimp [boxItr] at h;
  grind;
@[grind =>]
lemma exists_of_mem_box (h : φ ∈ □'s) : ∃ ψ ∈ s, □ψ = φ := exists_of_mem_boxItr (n := 1) h

@[grind =>] lemma mono_boxItr (h : s ⊆ t) : (□^[n]'s) ⊆ (□^[n]'t) := by intro; grind;
@[grind =>] lemma mono_box (h : s ⊆ t) : (□'s) ⊆ (□'t) := mono_boxItr (n := 1) h

section

variable [InjectiveBox F] [DecidableEq F]

@[grind]
noncomputable def preboxItr [InjectiveBox F] [DecidableEq F] (n : ℕ) : List F → List F := λ s => (□⁻¹^[n]'(s.toFinset)).toList
notation:90 "□⁻¹^[" n "]'" s => List.LO.preboxItr n s

noncomputable abbrev prebox [InjectiveBox F] [DecidableEq F] : List F → List F := preboxItr 1
prefix:90 "□⁻¹'" => List.LO.prebox

@[simp, grind =] lemma eq_preboxItr_one_prebox : (□⁻¹^[1]'s) = □⁻¹'s := by rfl
@[simp, grind =] lemma preboxItr_nil : (□⁻¹^[n]'([] : List F)) = [] := by
  simp [preboxItr];

@[grind →] lemma mem_of_mem_boxItr_preboxItr (h : φ ∈ □^[n]'□⁻¹^[n]'s) : φ ∈ s := by
  apply mem_toFinset.mp $ Finset.LO.mem_of_mem_boxItr_preboxItr (n := n) ?_;
  simp only [boxItr, preboxItr, mem_map, Finset.mem_toList] at h;
  grind;
@[grind →] lemma mem_of_mem_box_prebox (h : φ ∈ □'□⁻¹'s) : φ ∈ s := mem_of_mem_boxItr_preboxItr (n := 1) h

@[grind <=]
lemma mem_boxItr_preboxItr_of_mem_of_mem_boxItr (h : □^[n]φ ∈ s) : □^[n]φ ∈ □^[n]'□⁻¹^[n]'s := by
  simpa [preboxItr, boxItr, Finset.LO.boxItr, Finset.LO.preboxItr];

@[grind <=]
lemma mem_box_prebox_of_mem_of_mem_box (h : □φ ∈ s) : □φ ∈ □'□⁻¹'s := mem_boxItr_preboxItr_of_mem_of_mem_boxItr (n := 1) h


end


@[grind] def diaItr (n : ℕ) : List F → List F := List.map (◇^[n]·)
notation:90 "◇^[" n "]'" s => List.LO.diaItr n s

abbrev dia : List F → List F := diaItr 1
prefix:90 "◇'" => List.LO.dia

@[grind] noncomputable def prediaItr (n : ℕ) : List F → List F := λ s => s.filter (λ φ => (◇^[n]φ) ∈ s)
notation:90 "◇⁻¹^[" n "]'" s => List.LO.prediaItr n s

noncomputable abbrev predia : List F → List F := prediaItr 1
prefix:90 "◇'⁻¹" => List.LO.predia

@[simp, grind =] lemma eq_diaItr_zero : (◇^[0]'s) = s := by induction s <;> simp_all [diaItr];
@[simp, grind =] lemma eq_diaItr_one_dia : (◇^[1]'s) = ◇'s := by rfl
@[simp, grind =] lemma eq_prediaItr_one_predia : (◇⁻¹^[1]'s) = ◇'⁻¹s := by rfl

@[grind =>] lemma not_nil_diaItr_of_not_nil (h : s ≠ []) : (◇^[n]'s) ≠ [] := by induction s <;> simp_all [diaItr];
@[grind =>] lemma not_nil_dia_of_not_nil (h : s ≠ []) : (◇'s) ≠ [] := not_nil_diaItr_of_not_nil (n := 1) h

@[simp, grind =] lemma diaItr_nil : (◇^[n]'([] : List F)) = [] := by rfl
@[simp, grind =] lemma prediaItr_nil : (◇⁻¹^[n]'([] : List F)) = [] := by rfl

@[simp, grind =] lemma diaItr_single : (◇^[n]'[φ]) = [◇^[n]φ] := by dsimp [diaItr];

@[simp, grind =] lemma eq_diaItr_conn : (◇^[n]'(ψ :: s)) = (◇^[n]ψ) :: (◇^[n]'s) := by induction s <;> simp_all [diaItr];
@[simp, grind =] lemma eq_dia_conn : (◇' (ψ :: s)) = (◇ψ) :: ◇'s := eq_diaItr_conn (n := 1)

@[grind =] lemma mem_diaItr_cons : φ ∈ (◇^[n]'(ψ :: s)) ↔ (φ = ◇^[n]ψ) ∨ (φ ∈ (◇^[n]'s)) := by grind;
@[grind =] lemma mem_dia_cons : φ ∈ (◇'(ψ :: s)) ↔ (φ = ◇ψ) ∨ (φ ∈ ◇'s) := mem_diaItr_cons (n := 1)

@[grind =]
lemma mem_diaItr_add : φ ∈ (◇^[m + n]'s) ↔ φ ∈ ◇^[n]'◇^[m]'s := by
  dsimp [diaItr];
  grind;

@[grind <=]
lemma mem_diaItr_of_mem (h : φ ∈ s) : (◇^[n]φ) ∈ (◇^[n]'s) := by
  dsimp [diaItr];
  grind;

@[grind =>]
lemma exists_of_mem_diaItr (h : φ ∈ ◇^[n]'s) : ∃ ψ ∈ s, (◇^[n]ψ) = φ := by
  dsimp [diaItr] at h;
  grind;
@[grind =>]
lemma exists_of_mem_dia (h : φ ∈ ◇'s) : ∃ ψ ∈ s, ◇ψ = φ := exists_of_mem_diaItr (n := 1) h

noncomputable abbrev diaFilter (n : ℕ) : List F → List F := λ s => ◇^[n]'◇⁻¹^[n]'s

end List.LO


namespace Finset.LO

variable [DecidableEq F] {s : Finset F}

@[grind! <=]
lemma mem_boxItr_of_toList_boxItr (h : φ ∈ □^[n]'s.toList) : φ ∈ (□^[n]'s) := by
  obtain ⟨ψ, hψ₁, hψ₂⟩ := List.LO.exists_of_mem_boxItr h;
  simp only [boxItr, mem_image];
  use ψ;
  constructor;
  . simpa using hψ₁;
  . assumption;
@[grind! <=]
lemma mem_box_of_toList_box (h : φ ∈ □'s.toList) : φ ∈ □'s := mem_boxItr_of_toList_boxItr h

@[grind! <=]
lemma mem_boxItr_toList_of_mem (h : φ ∈ (□^[n]'s)) : φ ∈ □^[n]'s.toList := by
  obtain ⟨ψ, hψ₁, rfl⟩ := Finset.LO.exists_of_mem_boxItr h;
  simp only [List.LO.boxItr, List.mem_map, mem_toList]
  use ψ;
@[grind <=]
lemma mem_box_toList_of_mem (h : φ ∈ □'s) : φ ∈ □'s.toList := mem_boxItr_toList_of_mem (n := 1) h


@[grind <=]
lemma mem_diaItr_of_toList_diaItr (h : φ ∈ ◇^[n]'s.toList) : φ ∈ (◇^[n]'s) := by
  obtain ⟨ψ, hψ₁, hψ₂⟩ := List.LO.exists_of_mem_diaItr h;
  simp only [diaItr, mem_image];
  use ψ;
  constructor;
  . simpa using hψ₁;
  . assumption;

@[grind <=]
lemma mem_dia_of_toList_dia (h : φ ∈ ◇'s.toList) : φ ∈ ◇'s := mem_diaItr_of_toList_diaItr h

end Finset.LO

end
