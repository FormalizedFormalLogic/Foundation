 import Logic.Logic.LogicSymbol

namespace LO

class UnaryModalOperator (m : ℕ) (F : Sort _) where
  mop (i : Fin m) : F → F
  mop_injective {i} : Function.Injective (mop i)

notation:76 "△[" i "]" p => UnaryModalOperator.mop i p

namespace UnaryModalOperator

variable [UnaryModalOperator m F]
variable {i : Fin m} {p q : F}

@[simp] lemma mop_injective' : (△[i]p) = (△[i]q) ↔ p = q := by constructor; intro h; exact mop_injective h; simp_all;

def multimop (i : Fin m) (n : ℕ) (p : F) : F :=
  match n with
  | 0 => p
  | n + 1 => △[i]((multimop i n p))

notation:76 "△[" i:90 "]" "[" n:90 "]" p:max => multimop i n p

@[simp] lemma multimop_zero : △[i][0]p = p := rfl

@[simp] lemma multimop_succ : △[i][(n + 1)]p = △[i](△[i][n]p) := rfl

lemma multimop_prepost : (△[i]△[i][n]p) = (△[i][n](△[i]p)) := by induction n <;> simp_all

@[simp] lemma multimop_injective' : (△[i][n]p = △[i][n]q) ↔ (p = q) := by induction n <;> simp [*]

@[simp] lemma multimop_injective : Function.Injective ((△[i][n]·) : F → F) := by simp [Function.Injective];

end UnaryModalOperator

namespace Set

open LO
open UnaryModalOperator

variable [UnaryModalOperator m F]
variable {i : Fin m} {s t : Set F} {n : ℕ} {a : F}

protected def multimop (i : Fin m) (n : ℕ) (s : Set F) : Set F := (multimop i n) '' s
notation:76 "△[" i:90 "]" "[" n:90 "]" s:max => Set.multimop i n s

@[simp] lemma multimop_empty : △[i][n](∅ : Set F) = ∅ := by simp [Set.multimop]

@[simp] lemma multimop_zero : △[i][0]s = s := by simp [Set.multimop]

@[simp] lemma multimop_mem_intro : a ∈ s → △[i][n]a ∈ (△[i][n]s) := by tauto;

@[simp] lemma multimop_injOn : Set.InjOn (multimop i n) (multimop i n ⁻¹' s) := by simp [Set.InjOn];

@[simp] lemma multimop_subset (h : s ⊆ t) : (△[i][n]s) ⊆ (△[i][n]t) := by simp_all [Set.subset_def, Set.multimop];

@[simp] lemma multimop_union : (△[i][n](s ∪ t)) = (△[i][n]s) ∪ (△[i][n]t) := by simp_all [Set.image_union, Set.multimop];

lemma multimop_mem_iff : a ∈ (△[i][n]s) ↔ (∃ b ∈ s, △[i][n]b = a) := by simp_all [Set.mem_image, Set.multimop];

lemma forall_multimop_of_subset_multimop (h : s ⊆ △[i][n]t) : ∀ p ∈ s, ∃ q ∈ t, p = △[i][n]q := by
  intro p hp;
  obtain ⟨q, hq₁, hq₂⟩ := h hp;
  use q;
  simp_all;

protected def mop (i : Fin m) (s : Set F) : Set F := Set.multimop i 1 s
notation:76 "△[" i "]" s => Set.mop i s

@[simp] lemma mop_empty : (△[i](∅ : Set F)) = ∅ := by simp [Set.mop]

@[simp] lemma mop_mem_intro : a ∈ s → (△[i]a) ∈ (△[i]s) := by apply multimop_mem_intro;

@[simp] lemma mop_injOn : Set.InjOn (multimop i n) s := by simp [Set.InjOn]

lemma mop_subset (h : s ⊆ t) : (△[i]s) ⊆ (△[i]t) := by apply multimop_subset; assumption;

@[simp] lemma mop_union : (△[i](s ∪ t)) = (△[i]s) ∪ (△[i]t) := by apply multimop_union;

lemma mop_mem_iff : p ∈ (△[i]s) ↔ (∃ q ∈ s, (△[i]q) = p) := by apply multimop_mem_iff;

protected lemma mop_injective : Function.Injective (λ {s : Set F} => Set.mop i s) := Function.Injective.image_injective mop_injective

lemma forall_mop_of_subset_mop (h : s ⊆ (Set.mop i t)) : ∀ p ∈ s, ∃ q ∈ t, p = △[i]q := forall_multimop_of_subset_multimop h


@[simp] protected def premultimop (i : Fin m) (n : ℕ) (s : Set F) := (multimop i n) ⁻¹' s
notation:76 "△⁻¹[" i:90 "]" "[" n:90 "]" s:max => Set.premultimop i n s

lemma multimop_premultimop_eq : △⁻¹[i][n](△[i][n]s) = s := by
  apply Set.preimage_image_eq;
  exact multimop_injective;

lemma premultimop_multimop_eq_of_subset_premultimop (hs : s ⊆ △[i][n]t) : △[i][n](△⁻¹[i][n]s) = s := by
  apply Set.eq_of_subset_of_subset;
  . intro p hp;
    obtain ⟨q, hq₁, hq₂⟩ := hp;
    simp_all [Set.premultimop];
  . intro p hp;
    obtain ⟨q, _, hq₂⟩ := forall_multimop_of_subset_multimop hs p hp;
    simp_all [multimop, Set.premultimop];

@[simp] lemma premultimop_multimop_subset : △[i][n](△⁻¹[i][n]s) ⊆ s := by simp [Set.subset_def, Set.multimop, Set.premultimop];

lemma premultimop_subset (h : s ⊆ t) : (△⁻¹[i][n]s) ⊆ (△⁻¹[i][n]t) := by simp_all [Set.subset_def, Set.premultimop];

lemma subset_premulitimop_iff_multimop_subset (h : s ⊆ △⁻¹[i][n]t) : △[i][n]s ⊆ t := by
  intro p hp;
  obtain ⟨_, h₁, h₂⟩ := multimop_subset h hp;
  subst h₂;
  assumption;

lemma subset_multimop_iff_premulitimop_subset (h : s ⊆ (△[i][n]t)) : (△⁻¹[i][n]s) ⊆ t := by
  intro p hp;
  obtain ⟨_, h₁, h₂⟩ := premultimop_subset h hp;
  simp_all;


protected def premop (i : Fin m) (s : Set F) := Set.premultimop i 1 s
notation:76 "△⁻¹[" i "]" s => Set.premop i s

@[simp] lemma mop_premop_eq : (△⁻¹[i]△[i]s) = s := by apply multimop_premultimop_eq;

lemma premop_mop_eq_of_subset_mop (hs : s ⊆ △[i]t) : (△[i]△⁻¹[i]s) = s := premultimop_multimop_eq_of_subset_premultimop hs

@[simp] lemma premop_mop_subset : (△[i]△⁻¹[i]s) ⊆ s := by apply premultimop_multimop_subset;

lemma premop_subset (h : s ⊆ t) : (△⁻¹[i]s) ⊆ (△⁻¹[i]t) := premultimop_subset h

lemma subset_premop_iff_mop_subset (h : s ⊆ △⁻¹[i]t) : (△[i]s) ⊆ t := subset_premulitimop_iff_multimop_subset h

lemma subset_mop_iff_premop_subset (h : s ⊆ △[i]t) : (△⁻¹[i]s) ⊆ t := subset_multimop_iff_premulitimop_subset h

end Set


namespace List

open LO
open UnaryModalOperator

variable [UnaryModalOperator m F] [DecidableEq F]
variable {i : Fin m} {n : ℕ} {l : List F}

protected def multimop (i : Fin m) (n : ℕ) (l : List F) : List F := l.map (multimop i n)
notation "△[" i:90 "]" "[" n:90 "]" l:max => List.multimop i n l

@[simp] protected def mop (i : Fin m) (l : List F) : List F := △[i][1]l
notation "△[" n:90 "]" l:max => List.mop n l

@[simp] lemma multimop_empty : △[i][n]([] : List F) = [] := by simp [List.multimop]

@[simp] lemma multimop_zero : △[i][0]l = l := by simp [List.multimop, multimop]

def premultimop (i : Fin m) (n : ℕ) (l : List F) := l.filter (λ (p : F) => △[i][n]p ∈ l)
notation "△⁻¹[" i:90 "]" "[" n:90 "]" l:max => List.premultimop i n l

@[simp] def premop (i : Fin m) (l : List F) := △[i][1]l
notation "△⁻¹[" i:90 "]" l:max => List.premop i l

end List


namespace Finset

open LO
open UnaryModalOperator

variable [UnaryModalOperator m F] [DecidableEq F]
variable {i : Fin m} {n : ℕ} {s t : Finset F}

@[simp] protected noncomputable def multimop (i : Fin m) (n : ℕ) (s : Finset F) : Finset F := (△[i][n](s.toList)).toFinset
notation "△[" i:90 "]" "[" n:90 "]" s:max => Finset.multimop i n s

@[simp] protected noncomputable def mop (i : Fin m) (s : Finset F) : Finset F := △[i][1]s
notation "△[" i:90 "]" s:max => Finset.mop i s

lemma multimop_def : (△[i][n]s : Finset F) = s.image (multimop i n) := by simp [List.multimop, List.toFinset_map];

@[simp] lemma multimop_coe : ↑(△[i][n]s : Finset F) = △[i][n](↑s : Set F) := by simp_all [Set.multimop, List.multimop]; rfl;

@[simp] lemma multimop_zero : (△[i][0]s : Finset F) = s := by simp

@[simp]
lemma multimop_union : (△[i][n](s ∪ t) : Finset F) = (△[i][n]s ∪ △[i][n]t : Finset F) := by
  simp [List.toFinset_map, List.multimop];
  aesop;

@[simp] noncomputable def premultimop (i : Fin m) (n : ℕ) (s : Finset F) : Finset F := s.preimage (multimop i n) (by simp)
notation "△⁻¹[" i:90 "]" "[" n:90 "]" s:max => Finset.premultimop i n s

@[simp] noncomputable def premop (i : Fin m) (s : Finset F) : Finset F := △⁻¹[i][1]s
notation "△⁻¹[" i:90 "]" s:max => Finset.premop i s

@[simp] lemma premultimop_coe : ↑(△⁻¹[i][n]s : Finset F) = △⁻¹[i][n](↑s : Set F) := by apply Finset.coe_preimage;

lemma premultimop_multimop_eq_of_subset_multimop {s : Finset F} {t : Set F} (hs : ↑s ⊆ △[i][n]t) : (△[i][n](△⁻¹[i][n]s : Finset F) : Finset F) = s := by
  have := Set.premultimop_multimop_eq_of_subset_premultimop hs;
  rw [←premultimop_coe, ←multimop_coe] at this;
  exact Finset.coe_inj.mp this;

end Finset

class StandardModalLogicalConnective (F : Sort _) extends LogicalConnective F, UnaryModalOperator 2 F where
  duality {p : F} : (mop 1) p = ~((mop 0) (~p))

namespace StandardModalLogicalConnective

variable [hS : StandardModalLogicalConnective F] [DecidableEq F]

@[match_pattern]
abbrev box : F → F := hS.mop 0
prefix:74 "□" => StandardModalLogicalConnective.box

@[match_pattern]
abbrev dia : F → F := hS.mop 1
prefix:74 "◇" => StandardModalLogicalConnective.dia

abbrev multibox (n : ℕ) : F → F := hS.multimop 0 n
notation:74 "□[" n:90 "]" p:80 => multibox n p

abbrev multidia (n : ℕ) : F → F := hS.multimop 1 n
notation:74 "◇[" n:90 "]" p:80 => multidia n p


abbrev _root_.Set.multibox (n : ℕ) (s : Set F) : Set F := @Set.multimop _ _ hS.toUnaryModalOperator 0 n s
notation "□[" n:90 "]" s:80 => Set.multibox n s

abbrev _root_.Set.box (s : Set F) : Set F := @Set.mop _ _ hS.toUnaryModalOperator 0 s
notation "□" s:80 => Set.box s

abbrev _root_.Set.premultibox (n : ℕ) (s : Set F) : Set F := @Set.premultimop _ _ hS.toUnaryModalOperator 0 n s
notation "□⁻¹[" n:90 "]" s:80 => Set.premultibox n s

abbrev _root_.Set.prebox (s : Set F) : Set F := @Set.premop _ _ hS.toUnaryModalOperator 0 s
notation "□⁻¹" s:80 => Set.prebox s

abbrev _root_.Set.multidia (n : ℕ) (s : Set F) : Set F := @Set.multimop _ _ hS.toUnaryModalOperator 1 n s
notation "◇[" n:90 "]" s:80 => Set.multidia n s

abbrev _root_.Set.dia (s : Set F) : Set F := @Set.mop _ _ hS.toUnaryModalOperator 1 s
notation "◇" s:80 => Set.dia s

abbrev _root_.Set.premultidia (n : ℕ) (s : Set F) : Set F := @Set.premultimop _ _ hS.toUnaryModalOperator 1 n s
notation "◇⁻¹[" n:90 "]" s:80 => Set.premultidia n s

abbrev _root_.Set.predia (s : Set F) : Set F := @Set.premop _ _ hS.toUnaryModalOperator 1 s
notation "◇⁻¹" s:80 => Set.predia s


abbrev _root_.List.multibox (n : ℕ) (l : List F) : List F := @List.multimop _ _ hS.toUnaryModalOperator 0 n l

abbrev _root_.List.box (l : List F) : List F := @List.mop _ _ hS.toUnaryModalOperator 0 l

abbrev _root_.List.multidia (n : ℕ) (l : List F) : List F := @List.multimop _ _ hS.toUnaryModalOperator 1 n l

abbrev _root_.List.dia (l : List F) : List F := @List.mop _ _ hS.toUnaryModalOperator 1 l


noncomputable abbrev _root_.Finset.multibox (n : ℕ) (s : Finset F) : Finset F := @Finset.multimop _ _ hS.toUnaryModalOperator _ 0 n s
notation "□[" n:90 "]" s:80 => Finset.multibox n s

noncomputable abbrev _root_.Finset.box (s : Finset F) : Finset F := @Finset.mop _ _ hS.toUnaryModalOperator _ 0 s
notation "□" s:80 => Finset.box s

noncomputable abbrev _root_.Finset.multidia (n : ℕ) (s : Finset F) : Finset F := @Finset.multimop _ _ hS.toUnaryModalOperator _ 1 n s
notation "◇[" n:90 "]" s:80 => Finset.multidia n s

noncomputable abbrev _root_.Finset.dia (s : Finset F) : Finset F := @Finset.mop _ _ hS.toUnaryModalOperator _ 1 s
notation "◇" s:80 => Finset.dia s

end StandardModalLogicalConnective

end LO
