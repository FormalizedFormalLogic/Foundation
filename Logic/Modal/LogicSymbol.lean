import Logic.Logic.LogicSymbol

open Function

namespace LO

class UnaryModalOperator (ι : Type*) (F : Type*) where
  mop (i : ι) : F → F
  mop_injective {i} : Function.Injective (mop i)

attribute [simp] UnaryModalOperator.mop_injective

namespace UnaryModalOperator

variable [UnaryModalOperator ι F]
variable {i : ι} {p q : F}

@[simp]
lemma mop_injective' : ((mop i) p) = ((mop i) q) ↔ p = q := by
  constructor;
  . intro h; exact mop_injective h;
  . simp_all;

@[simp] lemma multimop_succ : (mop i)^[(n + 1)] p = (mop i) ((mop i)^[n] p) := by apply iterate_succ_apply'

@[simp] lemma multimop_injective : Function.Injective (((mop i)^[n]) : F → F) := by apply Function.Injective.iterate (by simp);

@[simp]
lemma multimop_injective' : ((mop i)^[n] p = (mop i)^[n] q) ↔ (p = q) := by
  constructor;
  . intro h; exact multimop_injective h;
  . simp_all;

end UnaryModalOperator

end LO


section

open LO UnaryModalOperator

variable [UnaryModalOperator ι F] [DecidableEq F]
variable {i : ι} {n : ℕ} {p q : F}


namespace Set

protected abbrev mop (i : ι) : Set F → Set F := image (mop i)

protected abbrev multimop (i : ι) (n : ℕ) : Set F → Set F := image (mop i)^[n]

protected abbrev premop (i : ι) : Set F → Set F := preimage (mop i)

protected abbrev premultimop (i : ι) (n : ℕ) : Set F → Set F := preimage (mop i)^[n]

variable {s t : Set F}

@[simp] lemma mop_iff_multimop_one : s.mop i = s.multimop i 1 := by rfl

@[simp] lemma premop_iff_premultimop_one : s.premop i = s.premultimop i 1 := by rfl


lemma multimop_subset (h : s ⊆ t) : s.multimop i n ⊆ t.multimop i n := by simp_all [Set.subset_def];

lemma premultimop_subset (h : s ⊆ t) : s.premultimop i n ⊆ t.premultimop i n := by simp_all [Set.subset_def];

lemma subset_premulitimop_iff_multimop_subset (h : s ⊆ t.premultimop i n) : s.multimop i n ⊆ t := by
  intro p hp;
  obtain ⟨_, h₁, h₂⟩ := multimop_subset h hp;
  subst h₂;
  assumption;

lemma subset_multimop_iff_premulitimop_subset (h : s ⊆ t.multimop i n) : s.premultimop i n ⊆ t := by
  intro p hp;
  obtain ⟨_, h₁, h₂⟩ := premultimop_subset h hp;
  simp_all;

lemma forall_multimop_of_subset_multimop (h : s ⊆ t.multimop i n) : ∀ p ∈ s, ∃ q ∈ t, p = (mop i)^[n] q := by
  intro p hp;
  obtain ⟨q, hq₁, hq₂⟩ := h hp;
  use q;
  simp_all;

lemma eq_premultimop_multimop_of_subset_premultimop (h : s ⊆ t.multimop i n) : (s.premultimop i n |>.multimop i n) = s := by
  apply Set.eq_of_subset_of_subset;
  . intro p hp;
    obtain ⟨q, hq₁, hq₂⟩ := hp;
    simp_all [Set.premultimop];
  . intro p hp;
    obtain ⟨q, _, hq₂⟩ := forall_multimop_of_subset_multimop h p hp;
    simp_all [Set.premultimop];

end Set


namespace Finset

protected noncomputable abbrev multimop (i : ι) (n : ℕ) (s : Finset F) : Finset F := s.image ((mop i)^[n])

protected noncomputable abbrev mop (i : ι) (s : Finset F) : Finset F := s.multimop i 1

protected noncomputable abbrev premultimop (i : ι) (n : ℕ) (s : Finset F) : Finset F := s.preimage ((mop i)^[n]) (by simp [Set.InjOn])

protected noncomputable abbrev premop (i : ι) (s : Finset F) : Finset F := s.premultimop i 1

variable {s t : Finset F}

@[simp] lemma iff_mop_multimop_one : s.mop i = s.multimop i 1 := by rfl;

@[simp] lemma iff_premop_premultimop_one : s.premop i = s.premultimop i 1 := by rfl;


lemma multimop_coe : ↑(s.multimop i n) = (↑s : Set F).multimop i n := by simp_all;

lemma multimop_mem_coe : p ∈ s.multimop i n ↔ p ∈ (↑s : Set F).multimop i n := by constructor <;> simp_all

lemma premultimop_coe : ↑(s.premultimop i n) = (↑s : Set F).premultimop i n := by apply Finset.coe_preimage;

lemma premultimop_multimop_eq_of_subset_multimop {s : Finset F} {t : Set F} (hs : ↑s ⊆ t.multimop i n) : (s.premultimop i n).multimop i n = s := by
  have := Set.eq_premultimop_multimop_of_subset_premultimop hs;
  rw [←premultimop_coe, ←multimop_coe] at this;
  exact Finset.coe_inj.mp this;

end Finset


namespace List

variable [LO.UnaryModalOperator ι F] [DecidableEq F]

protected noncomputable abbrev multimop (i : ι) (n : ℕ) (l : List F) : List F := l.toFinset.multimop i n |>.toList

protected noncomputable abbrev mop (i : ι) (l : List F) : List F := l.toFinset.mop i |>.toList

protected noncomputable abbrev premultimop (i : ι) (n : ℕ) (l : List F) := l.toFinset.premultimop i n |>.toList

protected noncomputable abbrev premop (i : ι) (l : List F) := l.toFinset.premop i |>.toList

variable {l : List F} {s : Set F}

@[simp] lemma mop_iff_multimop_one : l.mop i = l.multimop i 1 := by rfl

@[simp] lemma iff_premop_premultimop_one : l.premop i = l.premultimop i 1 := by rfl

@[simp] lemma multimop_nil : (([] :List F).multimop i n) = [] := by simp;

@[simp] lemma multimop_single : (([p] :List F).multimop i n) = [((mop i)^[n] p)] := by simp;

lemma multimop_cons (hl : p ∉ l) : ((p :: l).multimop i n) ~ ((mop i)^[n] p :: l.multimop i n) := by
  simp [List.multimop];
  apply Finset.toList_insert;
  simp_all;

@[simp] lemma premultimop_nil : (([] :List F).premultimop i n) = [] := by simp;

lemma forall_multimop_of_subset_multimop (h : ∀ p ∈ l, p ∈ s.multimop i n) : ∀ p ∈ l, ∃ q ∈ s, p = (mop i)^[n] q := by
  intro p hp;
  obtain ⟨q, _, _⟩ := by simpa only [Set.mem_image] using h p hp;
  use q; subst_vars; simpa;

end List

end


namespace LO

open UnaryModalOperator

/--
  Symbols for standard modal logic, which has 2 modal unary operators `□`, `◇`, and `◇` is defined as dual of `□`
-/
class StandardModalLogicalConnective (F : Sort _) extends LogicalConnective F, UnaryModalOperator Bool F where
  duality {p : F} : (mop false) p = ~((mop true) (~p))

namespace StandardModalLogicalConnective

variable [StandardModalLogicalConnective F]

abbrev box : F → F := mop true
prefix:74 "□" => box

abbrev dia : F → F := mop false
prefix:74 "◇" => dia

abbrev boxdot (p : F) : F := p ⋏ □p
prefix:74 "⊡" => boxdot

-- abbrev diadot (p : F) : F := p ⋏ ◇p
-- prefix:74 "⟐" => diadot

lemma duality' {p : F} : (◇p) = ~(□(~p)) := by apply duality

abbrev multibox (n : ℕ) : F → F := (mop true)^[n]
notation:74 "□^[" n:90 "]" p:80 => multibox n p

abbrev multidia (n : ℕ) : F → F := (mop false)^[n]
notation:74 "◇^[" n:90 "]" p:80 => multidia n p

end LO.StandardModalLogicalConnective


section

variable [LO.StandardModalLogicalConnective F] [DecidableEq F]

-- TODO: Remove `'` of `□'`

namespace Set

abbrev multibox (n : ℕ) (s : Set F) : Set F := Set.multimop true n s
notation "□''^[" n:90 "]" s:80 => Set.multibox n s

abbrev box (s : Set F) : Set F := Set.mop true s
notation "□''" s:80 => Set.box s

abbrev premultibox (n : ℕ) (s : Set F) : Set F := Set.premultimop true n s
notation "□''⁻¹^[" n:90 "]" s:80 => Set.premultibox n s

abbrev prebox (s : Set F) : Set F := Set.premop true s
notation "□''⁻¹" s:80 => Set.prebox s

abbrev multidia (n : ℕ) (s : Set F) : Set F := Set.multimop false n s
notation "◇''^[" n:90 "]" s:80 => Set.multidia n s

abbrev dia (s : Set F) : Set F := Set.mop false s
notation "◇''" s:80 => Set.dia s

abbrev premultidia (n : ℕ) (s : Set F) : Set F := Set.premultimop false n s
notation "◇''⁻¹^[" n:90 "]" s:80 => Set.premultidia n s

abbrev predia (s : Set F) : Set F := Set.premop false s
notation "◇''⁻¹" s:80 => Set.predia s

end Set


/-
namespace Finset

noncomputable abbrev multibox (n : ℕ) (s : Finset F) : Finset F := Finset.multimop true n s
notation "□'^[" n:90 "]" s:80 => Finset.multibox n s

noncomputable abbrev box (s : Finset F) : Finset F := Finset.mop true s
notation "□'" s:80 => Finset.box s

noncomputable abbrev premultibox (n : ℕ) (s : Finset F) : Finset F := Finset.premultimop true n s
notation "□'⁻¹^[" n:90 "]" s:80 => Finset.premultibox n s

noncomputable abbrev prebox (s : Finset F) : Finset F := Finset.premop true s
notation "□'⁻¹" s:80 => Finset.prebox s

noncomputable abbrev multidia (n : ℕ) (s : Finset F) : Finset F := Finset.multimop false n s
notation "◇'^[" n:90 "]" s:80 => Finset.multidia n s

noncomputable abbrev dia (s : Finset F) : Finset F := Finset.mop false s
notation "◇'" s:80 => Finset.dia s

noncomputable abbrev premultidia (n : ℕ) (s : Finset F) : Finset F := Finset.premultimop false n s
notation "◇'⁻¹^[" n:90 "]" s:80 => Finset.premultidia n s

noncomputable abbrev predia (s : Finset F) : Finset F := Finset.premop false s
notation "◇'⁻¹" s:80 => Finset.predia s

end Finset
-/


namespace List

variable (n : ℕ) (l : List F)

noncomputable abbrev multibox : List F := List.multimop true n l
notation "□'^[" n:90 "]" l:80 => List.multibox n l

noncomputable abbrev box : List F := List.mop true l
notation "□'" l:80 => List.box l

noncomputable abbrev multidia : List F := List.multimop false n l
notation "◇'^[" n:90 "]" l:80 => List.multidia n l

noncomputable abbrev dia : List F := List.mop false l
notation "◇'" l:80 => List.dia l

noncomputable abbrev premultibox : List F := List.premultimop true n l
notation "□'⁻¹^[" n:90 "]" l:80 => List.premultibox n l

noncomputable abbrev prebox : List F := List.premop true l
notation "□'⁻¹" l:80 => List.prebox l

noncomputable abbrev premultidia : List F := List.premultimop false n l
notation "◇'⁻¹^[" n:90 "]" l:80 => List.premultidia n l

noncomputable abbrev predia : List F := List.premop false l
notation "◇'⁻¹" l:80 => List.predia l

end List

end
