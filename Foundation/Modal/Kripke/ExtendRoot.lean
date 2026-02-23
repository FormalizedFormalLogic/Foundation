module

public import Foundation.Modal.Boxdot.Basic
public import Foundation.Modal.Kripke.Tree
public import Foundation.Modal.Kripke.AxiomL
public import Foundation.Vorspiel.Finset.Card

public import Mathlib.Data.Finite.Sum

@[expose] public section

namespace LO.Modal

open Formula.Kripke

namespace Kripke

abbrev Frame.extendRoot (F : Kripke.Frame) (n : ℕ+) : Kripke.Frame where
  World := Fin n ⊕ F.World
  Rel x y :=
    match x, y with
    | .inr x, .inr y => x ≺ y
    | .inr _, .inl _ => False
    | .inl _, .inr _ => True
    | .inl i, .inl j => j < i

namespace Frame.extendRoot

variable {F : Frame} {x y : F.World} {n : ℕ+}

abbrev extend (i : Fin n) : F.extendRoot n := .inl i

@[coe] abbrev embed (x : F) : F.extendRoot n := .inr x

instance : Coe (F.World) ((F.extendRoot n).World) := ⟨embed⟩

instance isFinite [F.IsFinite] : (F.extendRoot n).IsFinite := by
  unfold Frame.extendRoot;
  infer_instance;

instance fintype [Fintype F] : Fintype (F.extendRoot n) := instFintypeSum (Fin n) F

protected abbrev defaultRoot (F n) : (extendRoot F n).Root := ⟨.inl ⟨n - 1, by simp⟩, by grind⟩

instance : (F.extendRoot n).IsPointRooted where
  default := extendRoot.defaultRoot F n
  uniq {r} := by
    by_contra! hC;
    have : r ≺ (extendRoot.defaultRoot F n).1 := r.2 _ $ (by grind);
    grind;

protected abbrev chain (F n) : List (extendRoot F n) := List.finRange n |>.reverse.map (extend ·)

@[simp]
lemma chain_length : (extendRoot.chain F n |>.length) = n := by simp

@[simp]
lemma chain_IsChain : List.IsChain (· ≺ ·) (extendRoot.chain F n) := by
  apply List.isChain_map_of_isChain (R := λ a b => a > b);
  . tauto;
  . simp;

instance isAsymmetric [F.IsAsymmetric] : (F.extendRoot n).IsAsymmetric := ⟨by grind⟩
instance isTransitive [F.IsTransitive] : (F.extendRoot n).IsTransitive := ⟨by grind⟩
instance isIrreflexive [F.IsIrreflexive] : (F.extendRoot n).IsIrreflexive := ⟨by grind⟩
instance [F.IsFinite] [F.IsIrreflexive] [F.IsTransitive] : (F.extendRoot n).IsConverseWellFounded := by infer_instance;

instance isTree [F.IsRooted] [F.IsTree] : (F.extendRoot n).IsTree where
instance isFiniteTree [F.IsRooted] [F.IsFinite] : (F.extendRoot n).IsFiniteTree where

protected abbrev pMorphism : F →ₚ F.extendRoot n where
  toFun := embed
  forth := by grind;
  back {x y} h := by grind;


@[simp]
lemma embed_rel_embed_iff_rel {i j : F} : embed (n := n) i ≺ embed j ↔ i ≺ j :=
  extendRoot.pMorphism.toFun_rel_toFun_iff_of_inj Sum.inr_injective

@[simp]
lemma embed_rel_iterate_embed_iff_rel {i j : F} : embed (n := n) i ≺^[k] embed j ↔ i ≺^[k] j :=
  extendRoot.pMorphism.toFun_rel_iterate_toFun_iff_of_inj Sum.inr_injective

@[simp]
lemma rel_root_original_root [F.IsRooted] : (F.extendRoot n).root.1 ≺ F.root.1 := by grind;

@[grind →]
lemma not_eq_extendRoot_root_of_rel_original_root [F.IsIrreflexive] (x : F.extendRoot n) (h : (extendRoot F n).root ≺ x) : x ≠ (extendRoot F n).root := by
  grind;


lemma eq_extend_or_eq_original (x : F.extendRoot n)
  : (∃ i : Fin n, x = extend i) ∨ (∃ x₀ : F, x = x₀) := by
  match x with
  | .inl i => left; use i;
  | .inr x => grind;


section

lemma eq_root_or_rel_original_root_of_rel_extendRoot_root₁ [F.IsIrreflexive] (x : F.extendRoot 1) (h : (extendRoot F 1).root ≺ x)
  : ∃ x₀ : F, x = x₀ := by
  rcases eq_extend_or_eq_original x with (⟨i, hi, rfl⟩ | _);
  . simp [Frame.root, default] at h;
  . simp_all;

lemma eq_root_or_rel_original_root_of_neq_extendRoot_root₁ [F.IsIrreflexive] (x : F.extendRoot 1) (h : x ≠ (extendRoot F 1).root)
  : ∃ x₀ : F, x = x₀ := by
  apply eq_root_or_rel_original_root_of_rel_extendRoot_root₁;
  grind;

end

end Frame.extendRoot


abbrev Model.extendRoot (M : Kripke.Model) (r : M.Root) (n : ℕ+) : Kripke.Model where
  toFrame := M.toFrame.extendRoot n
  Val a x :=
    match x with
    | .inl _ => M.Val a r
    | .inr x => M.Val a x

namespace Model.extendRoot

variable {M : Model} {r : M.Root} {x y : M.World} {n : ℕ+} {i : Fin n} {φ}

@[coe] abbrev extend (i : Fin n) : M.extendRoot r n := .inl i
@[coe] abbrev embed (x : M) : M.extendRoot r n := .inr x

def pMorphism : M →ₚ M.extendRoot r n := PseudoEpimorphism.ofAtomic Frame.extendRoot.pMorphism $ by grind;

lemma modal_equivalence_original_world : (embed x : M.extendRoot r n) ↭ x :=
  Model.PseudoEpimorphism.modal_equivalence pMorphism _ |>.symm

@[simp]
lemma inr_satisfies_iff : Satisfies (M.extendRoot r n) (embed x) φ ↔ x ⊧ φ := modal_equivalence_original_world

open Formula.Kripke in
lemma inl_satisfies_boxdot_iff [M.IsTransitive] : Satisfies (M.extendRoot r n) (extend i) (φᵇ) ↔ r.1 ⊧ φᵇ := by
  induction φ generalizing i with
  | hatom φ => rfl;
  | hfalsum => rfl;
  | himp φ ψ ihA ihB =>
    replace ihA := @ihA i;
    replace ihB := @ihB i;
    simp_all [Formula.boxdotTranslate, Satisfies];
  | hbox φ ih =>
    dsimp [Formula.boxdotTranslate];
    constructor;
    . intro h;
      replace ⟨h₁, h₂⟩ := Satisfies.and_def.mp h;
      apply Satisfies.and_def.mpr;
      constructor;
      . apply ih.mp h₁;
      . intro x Rix;
        exact inr_satisfies_iff.mp $ @h₂ (Sum.inr x) $ by grind;
    . intro h;
      obtain ⟨h₁, h₂⟩ := Satisfies.and_def.mp h;
      apply Satisfies.and_def.mpr;
      constructor;
      . exact ih.mpr h₁;
      . intro x Rix;
        match x with
        | .inl j => apply ih.mpr h₁;
        | .inr x =>
          apply inr_satisfies_iff.mpr;
          by_cases erx : r = x;
          . subst erx;
            exact h₁;
          . apply h₂;
            grind;

end Model.extendRoot

section

open Classical

variable {M : Kripke.Model} [Finite M.World] [IsTrans _ M.Rel] [Std.Irrefl M.Rel]
variable {A : Formula _}
variable {l : List M.World} {n : ℕ+}

lemma atmost_one_validates_axiomT_in_irrefl_trans_isChain (l_chain : List.IsChain (· ≺ ·) l) :
    (∀ x ∈ l, x ⊧ □A ➝ A) ∨ (∃! x ∈ l, ¬x ⊧ □A ➝ A) := by
  apply or_iff_not_imp_left.mpr;
  push_neg;
  rintro ⟨x, x_l, hx⟩;
  use x;
  constructor;
  . simp_all;
  . rintro y ⟨y_l, hy⟩;
    wlog neyx : y ≠ x;
    . tauto;
    obtain ⟨hx₁, hx₂⟩ : x ⊧ □A ∧ ¬(x ⊧ A) := by simpa using hx;
    obtain ⟨hy₁, hy₂⟩ : y ⊧ □A ∧ ¬(y ⊧ A) := by simpa using hy;
    rcases (List.IsChain.connected_of_trans l_chain y_l x_l (by tauto)) with Ryx | Rxy;
    . have : x ⊧ A := hy₁ x Ryx; contradiction;
    . have : y ⊧ A := hx₁ y Rxy; contradiction;

lemma atmost_one_validates_axiomT_in_irrefl_trans_chain
    (l_chain : List.IsChain (· ≺ ·) l) :
    haveI : Fintype M.World := Fintype.ofFinite _;
    Finset.card { x | x ∈ l ∧ ¬x ⊧ (□A ➝ A) } ≤ 1 := by
  apply Nat.le_one_iff_eq_zero_or_eq_one.mpr;
  rcases atmost_one_validates_axiomT_in_irrefl_trans_isChain (l_chain := l_chain) (A := A) with h | h;
  . left;
    apply Finset.card_filter_eq_zero_iff.mpr;
    simp_all;
  . right;
    apply Finset.card_eq_one.mpr;
    apply Finset.singleton_iff_unique_mem _ |>.mpr;
    simp_all;

lemma validates_axiomT_set_in_irrefl_trans_chain
    (Γ : Finset (Modal.Formula ℕ))
    (l_length : l.length = Γ.card + 1)
    (l_chain : List.IsChain (· ≺ ·) l) :
    ∃ x ∈ l, x ⊧ (Γ.image (λ γ => □γ ➝ γ)).conj := by
  haveI : Fintype M.World := Fintype.ofFinite _;
  let t₁ : Finset M.World := { x | x ∈ l ∧ ∃ A ∈ Γ, ¬x ⊧ (□A ➝ A) };
  let t₂ : Finset M.World := l.toFinset;
  have : t₁.card ≤ Γ.card :=
    calc
      _ = (Finset.biUnion Γ (λ A => { x | x ∈ l ∧ ¬x ⊧ (□A ➝ A) })).card := by
        apply Finset.eq_card_of_eq;
        ext x;
        constructor;
        . intro hx;
          obtain ⟨_, hx₁, ⟨A, hA₁, hA₂⟩⟩ := Finset.mem_filter.mp hx;
          apply Finset.mem_biUnion.mpr;
          use A;
          constructor;
          . assumption;
          . apply Finset.mem_filter.mpr;
            tauto;
        . intro hx;
          obtain ⟨A, _, hA⟩ := Finset.mem_biUnion.mp hx;
          obtain ⟨_, _, _⟩ := Finset.mem_filter.mp hA;
          apply Finset.mem_filter.mpr;
          tauto;
      _ ≤ ∑ a ∈ Γ, Finset.card { x | x ∈ l ∧ ¬x ⊧ □a ➝ a } := Finset.card_biUnion_le
      _ ≤ Γ.card * 1 := by
        apply Finset.sum_le_card;
        intro A hA;
        convert atmost_one_validates_axiomT_in_irrefl_trans_chain l_chain;
      _ = Γ.card := by omega;
  have : t₂.card = l.length :=
    calc
      _ = l.dedup.length := List.card_toFinset l
      _ = l.length       := by
        suffices l.dedup = l by rw [this];
        apply List.dedup_eq_self.mpr;
        apply List.IsChain.noDup_of_irrefl_trans l_chain;
  have : t₁ ⊂ t₂ := Finset.ssubset_of_subset_lt_card (by
    intro x hx;
    apply List.mem_toFinset.mpr;
    exact Finset.mem_filter.mp hx |>.2.1;
  ) (by omega);
  obtain ⟨x, hx₂, nhx₁⟩ := Finset.exists_of_ssubset this;
  replace hx₂ := List.mem_toFinset.mp hx₂;
  replace hx₁ := Finset.mem_filter.not.mp nhx₁;
  push_neg at hx₁;
  use x;
  constructor;
  . assumption;
  . apply Formula.Kripke.Satisfies.fconj_def.mpr;
    simp only [Finset.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂];
    intro A hA;
    apply hx₁;
    . simp;
    . assumption;
    . assumption;

end

namespace Model.extendRoot

open Classical

variable {M : Model} {r : M.Root} [M.IsFinite] [IsTrans _ M.Rel] [Std.Irrefl M.Rel] {x y : M.World}

lemma inr_satisfies_axiomT_set {Γ : Finset (Modal.Formula ℕ)} :
  letI n : ℕ+ := ⟨Γ.card + 1, by omega⟩;
  ∃ i : Fin n, Satisfies _ (extend i : M.extendRoot r n) (Γ.image (λ γ => □γ ➝ γ)).conj := by
  let n : ℕ+ := ⟨Γ.card + 1, by omega⟩;
  let M' := M.extendRoot r n;
  have : Finite M'.World := by
    unfold M' Model.extendRoot Frame.extendRoot;
    infer_instance;
  obtain ⟨x, hx₁, hx₂⟩ := @validates_axiomT_set_in_irrefl_trans_chain (M := M')
    (by infer_instance)
    inferInstance
    inferInstance
    (l := Frame.extendRoot.chain _ n)
    (Γ := Γ)
    (Frame.extendRoot.chain_length)
    (Frame.extendRoot.chain_IsChain)
  simp only [List.mem_map, M', n] at hx₁;
  obtain ⟨i, _, rfl⟩ := hx₁;
  use i;
  tauto;

end Model.extendRoot

end Kripke

end LO.Modal
end
