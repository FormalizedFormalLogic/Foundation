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

@[simp] lemma mop_injective' : ((mop i) p) = ((mop i) q) ↔ p = q := by constructor; intro h; exact mop_injective h; simp_all;

@[simp] lemma multimop_zero : (mop i)^[0] p = p := rfl

lemma multimop_succ : (mop i)^[(n + 1)] p = (mop i)^[n] ((mop i) p) := by apply iterate_succ_apply

@[simp] lemma multimop_succ' : (mop i)^[(n + 1)] p = (mop i) ((mop i)^[n] p) := by apply iterate_succ_apply'

lemma multimop_prepost : ((mop i) ((mop i)^[n] p)) = ((mop i)^[n] ((mop i) p)) := by induction n <;> simp_all

@[simp] lemma multimop_injective' : ((mop i)^[n] p = (mop i)^[n] q) ↔ (p = q) := by induction n <;> simp [*]

@[simp] lemma multimop_injective : Function.Injective (((mop i)^[n]) : F → F) := by apply Function.Injective.iterate (by simp);

end UnaryModalOperator

end LO


section

open LO UnaryModalOperator

variable [UnaryModalOperator ι F] [DecidableEq F]
variable {i : ι} {n : ℕ} {a : F}

namespace Set

variable {s t : Set F}

protected abbrev mop (i : ι) : Set F → Set F := image (mop i)

protected abbrev multimop (i : ι) (n : ℕ) : Set F → Set F := image (mop i)^[n]

@[simp] lemma mop_iff_multimop_one : (Set.mop i s) = (Set.multimop i 1 s) := by rfl


protected abbrev premultimop (i : ι) (n : ℕ) : Set F → Set F := Set.preimage ((mop i)^[n])

protected abbrev premop (i : ι) : Set F → Set F := Set.premultimop i 1

@[simp] lemma premop_iff_premultimop_one : (Set.premop i s) = (Set.premultimop i 1 s) := by rfl


@[simp] lemma multimop_subset (h : s ⊆ t) : (Set.multimop i n s) ⊆ (Set.multimop i n t) := by simp_all [Set.subset_def];

lemma multimop_mem_iff : a ∈ (Set.multimop i n s) ↔ (∃ b ∈ s, (mop i)^[n] b = a) := by simp_all [Set.mem_image, Set.multimop];

lemma forall_multimop_of_subset_multimop (h : s ⊆ Set.multimop i n t) : ∀ p ∈ s, ∃ q ∈ t, p = (mop i)^[n] q := by
  intro p hp;
  obtain ⟨q, hq₁, hq₂⟩ := h hp;
  use q;
  simp_all;

protected lemma mop_injective : Function.Injective (λ {s : Set F} => Set.mop i s) := Function.Injective.image_injective mop_injective

lemma forall_mop_of_subset_mop (h : s ⊆ (Set.mop i t)) : ∀ p ∈ s, ∃ q ∈ t, p = mop i q := forall_multimop_of_subset_multimop (by simpa using h)



lemma multimop_premultimop_eq : (Set.premultimop i n) (Set.multimop i n s) = s := by
  apply Set.preimage_image_eq;
  exact multimop_injective;

lemma premultimop_multimop_eq_of_subset_premultimop (hs : s ⊆ Set.multimop i n t) : Set.multimop i n ((Set.premultimop i n) s) = s := by
  apply Set.eq_of_subset_of_subset;
  . intro p hp;
    obtain ⟨q, hq₁, hq₂⟩ := hp;
    simp_all [Set.premultimop];
  . intro p hp;
    obtain ⟨q, _, hq₂⟩ := forall_multimop_of_subset_multimop hs p hp;
    simp_all [Set.premultimop];



lemma premultimop_subset (h : s ⊆ t) : ((Set.premultimop i n) s) ⊆ ((Set.premultimop i n) t) := by simp_all [Set.subset_def];

lemma subset_premulitimop_iff_multimop_subset (h : s ⊆ (Set.premultimop i n) t) : Set.multimop i n s ⊆ t := by
  intro p hp;
  obtain ⟨_, h₁, h₂⟩ := multimop_subset h hp;
  subst h₂;
  assumption;

lemma subset_multimop_iff_premulitimop_subset (h : s ⊆ (Set.multimop i n t)) : ((Set.premultimop i n) s) ⊆ t := by
  intro p hp;
  obtain ⟨_, h₁, h₂⟩ := premultimop_subset h hp;
  simp_all;

@[simp] lemma mop_premop_eq : (Set.premop i $ Set.mop i s) = s := by apply multimop_premultimop_eq;

lemma premop_mop_eq_of_subset_mop (hs : s ⊆ (Set.mop i t)) : (Set.mop i $ Set.premop i s) = s := premultimop_multimop_eq_of_subset_premultimop hs

lemma premop_subset (h : s ⊆ t) : (Set.premop i s) ⊆ (Set.premop i t) := premultimop_subset h

lemma subset_premop_iff_mop_subset (h : s ⊆ Set.premop i t) : (Set.mop i s) ⊆ t := subset_premulitimop_iff_multimop_subset h

lemma subset_mop_iff_premop_subset (h : s ⊆ Set.mop i t) : (Set.premop i s) ⊆ t := subset_multimop_iff_premulitimop_subset h

end Set


namespace List

open LO
open UnaryModalOperator

variable {l : List F}

protected abbrev mop (i : ι) : List F → List F := List.map (mop i)

protected abbrev multimop (i : ι) (n : ℕ) : List F → List F := List.map ((mop i)^[n])

protected abbrev premultimop (i : ι) (n : ℕ) := List.filter (λ (p : F) => (mop i)^[n] p ∈ l)

protected abbrev premop (i : ι) (l : List F) := l.filter (λ (p : F) => (mop i) p ∈ l)

end List


namespace Finset

variable {s t : Finset F}

protected noncomputable abbrev multimop (i : ι) (n : ℕ) (s : Finset F) : Finset F := (s.toList).multimop i n |>.toFinset

protected noncomputable abbrev mop (i : ι) (s : Finset F) : Finset F := (s.toList).multimop i 1 |>.toFinset

protected noncomputable abbrev premultimop (i : ι) (n : ℕ) (s : Finset F) : Finset F := s.preimage ((mop i)^[n]) (by simp [Set.InjOn])

protected noncomputable abbrev premop (i : ι) (s : Finset F) : Finset F := s.premultimop i 1

lemma multimop_coe : ↑(Finset.multimop i n s : Finset F) = Set.multimop i n (↑s : Set F) := by simp_all [Set.multimop, List.multimop]; rfl;

@[simp]
lemma multimop_union : (Finset.multimop i n (s ∪ t) : Finset F) = (Finset.multimop i n s ∪ Finset.multimop i n t) := by
  simp [List.toFinset_map];
  aesop;

lemma multimop_mem_coe {s : Finset F} : a ∈ Finset.multimop i n s ↔ a ∈ Set.multimop i n (↑s : Set F) := by
  constructor <;> simp_all [Set.multimop];

lemma premultimop_coe : ↑(s.premultimop i n) = (↑s : Set F).premultimop i n := by apply Finset.coe_preimage;

lemma premop_coe : ↑(s.premop i) = (↑s : Set F).premop i := by apply premultimop_coe;

lemma premultimop_multimop_eq_of_subset_multimop {s : Finset F} {t : Set F} (hs : ↑s ⊆ Set.multimop i n t) : (s.premultimop i n).multimop i n = s := by
  have := Set.premultimop_multimop_eq_of_subset_premultimop hs;
  rw [←premultimop_coe, ←multimop_coe] at this;
  exact Finset.coe_inj.mp this;

end Finset

end


namespace LO

open UnaryModalOperator

/--
  Standard modal logic, which has 2 modal unary operators `□`, `◇`, and `◇` is defined as dual of `□`
-/
class StandardModalLogicalConnective (F : Sort _) extends LogicalConnective F, UnaryModalOperator Bool F where
  duality {p : F} : (mop false) p = ~((mop true) (~p))

namespace StandardModalLogicalConnective

variable [StandardModalLogicalConnective F] [DecidableEq F]

@[match_pattern]
abbrev box : F → F := mop true
prefix:74 "□" => StandardModalLogicalConnective.box

@[match_pattern]
abbrev dia : F → F := mop false
prefix:74 "◇" => StandardModalLogicalConnective.dia

lemma duality' {p : F} : (◇p) = ~(□(~p)) := by apply StandardModalLogicalConnective.duality

abbrev multibox (n : ℕ) : F → F := (mop true)^[n]
notation:74 "□[" n:90 "]" p:80 => StandardModalLogicalConnective.multibox n p

abbrev multidia (n : ℕ) : F → F := (mop false)^[n]
notation:74 "◇[" n:90 "]" p:80 => StandardModalLogicalConnective.multidia n p

end LO.StandardModalLogicalConnective


section

variable [LO.StandardModalLogicalConnective F] [DecidableEq F]


namespace Set

abbrev multibox (n : ℕ) (s : Set F) : Set F := Set.multimop true n s
notation "□[" n:90 "]" s:80 => Set.multibox n s

abbrev box (s : Set F) : Set F := Set.mop true s
notation "□" s:80 => Set.box s

abbrev premultibox (n : ℕ) (s : Set F) : Set F := Set.premultimop true n s
notation "□⁻¹[" n:90 "]" s:80 => Set.premultibox n s

abbrev prebox (s : Set F) : Set F := Set.premop true s
notation "□⁻¹" s:80 => Set.prebox s

abbrev multidia (n : ℕ) (s : Set F) : Set F := Set.multimop false n s
notation "◇[" n:90 "]" s:80 => Set.multidia n s

abbrev dia (s : Set F) : Set F := Set.mop false s
notation "◇" s:80 => Set.dia s

abbrev premultidia (n : ℕ) (s : Set F) : Set F := Set.premultimop false n s
notation "◇⁻¹[" n:90 "]" s:80 => Set.premultidia n s

abbrev predia (s : Set F) : Set F := Set.premop false s
notation "◇⁻¹" s:80 => Set.predia s

end Set


namespace List

abbrev multibox (n : ℕ) (l : List F) : List F := List.multimop true n l

abbrev box (l : List F) : List F := List.mop true l

abbrev multidia (n : ℕ) (l : List F) : List F := List.multimop false n l

abbrev dia (l : List F) : List F := List.mop false l

end List


namespace Finset

noncomputable abbrev multibox (n : ℕ) (s : Finset F) : Finset F := Finset.multimop true n s
notation "□[" n:90 "]" s:80 => Finset.multibox n s

noncomputable abbrev box (s : Finset F) : Finset F := Finset.mop true s
notation "□" s:80 => Finset.box s

noncomputable abbrev premultibox (n : ℕ) (s : Finset F) : Finset F := Finset.premultimop true n s
notation "□⁻¹[" n:90 "]" s:80 => Finset.premultibox n s

noncomputable abbrev prebox (s : Finset F) : Finset F := Finset.premop true s
notation "□⁻¹" s:80 => Finset.prebox s

noncomputable abbrev multidia (n : ℕ) (s : Finset F) : Finset F := Finset.multimop false n s
notation "◇[" n:90 "]" s:80 => Finset.multidia n s

noncomputable abbrev dia (s : Finset F) : Finset F := Finset.mop false s
notation "◇" s:80 => Finset.dia s

noncomputable abbrev premultidia (n : ℕ) (s : Finset F) : Finset F := Finset.premultimop false n s
notation "◇⁻¹[" n:90 "]" s:80 => Finset.premultidia n s

noncomputable abbrev predia (s : Finset F) : Finset F := Finset.premop false s
notation "◇⁻¹" s:80 => Finset.predia s

end Finset

end
