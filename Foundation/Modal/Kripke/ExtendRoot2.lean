import Foundation.Modal.Boxdot.Basic
import Foundation.Modal.Kripke.Tree
import Foundation.Vorspiel.List.Chain
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finite.Sum

namespace LO.Modal

namespace Kripke

def Frame.extendRoot₂ (F : Kripke.Frame) (r : outParam F.World) [F.IsRooted r] (n : ℕ+) : Kripke.Frame where
  World := Fin n ⊕ F.World
  Rel x y :=
    match x, y with
    | .inr x, .inr y => x ≺ y
    | .inr _, .inl _ => False
    | .inl _, .inr _ => True
    | .inl i, .inl j => i < j

namespace Frame.extendRoot₂

variable {F : Frame} {r : outParam F.World} [F.IsRooted r] {x y : F.World} {n : ℕ+}

instance : Coe (F.World) ((F.extendRoot₂ r n).World) := ⟨Sum.inr⟩

instance isFinite [F.IsFinite] : (F.extendRoot₂ r n).IsFinite := by
  unfold Frame.extendRoot₂;
  infer_instance;

protected abbrev root : (F.extendRoot₂ r n).World := .inl 0

instance instIsRooted : (F.extendRoot₂ r n).IsRooted extendRoot₂.root where
  root_generates := by
    intro x h;
    match x with
    | .inl j =>
      obtain ⟨j, hj⟩ := j;
      apply Relation.TransGen.single;
      apply Nat.zero_lt_of_not_zero;
      simp_all [Frame.Rel', Frame.extendRoot₂, extendRoot₂.root]
    | .inr x =>
      apply Relation.TransGen.single;
      tauto;

protected abbrev chain : List (F.extendRoot₂ r n |>.World) := List.finRange n |>.map (Sum.inl ·)

@[simp]
lemma chain_length : extendRoot₂.chain (F := F) (r := r) (n := n).length = n := by simp

@[simp]
lemma chain_Chain' : List.Chain' (· ≺ ·) (extendRoot₂.chain (F := F) (r := r) (n := n)) := by
  apply List.chain'_map_of_chain' (R := λ a b => a < b);
  . tauto;
  . simp;

instance isAsymm [IsAsymm _ F.Rel] : IsAsymm _ (F.extendRoot₂ r n).Rel := ⟨by
  intro x y hxy;
  match x, y with
  | .inr x, .inr y =>
    suffices ¬y ≺ x by tauto;
    exact IsAsymm.asymm _ _ hxy;
  | .inl i, .inl j => simp_all [Frame.Rel', Frame.extendRoot₂]; omega;
  | .inl _, .inr _ => simp_all [Frame.Rel', Frame.extendRoot₂];
  | .inr _, .inl _ => simp_all [Frame.Rel', Frame.extendRoot₂];
⟩

instance isTrans [IsTrans _ F.Rel] : IsTrans _ (F.extendRoot₂ r n).Rel := ⟨by
  intro x y z hxy hyz;
  match x, y, z with
  | .inr x, .inr y, .inr z =>
    have : x ≺ z := IsTrans.trans _ _ _ hxy hyz;
    assumption;
  | .inr _, .inl _, .inl _ => simp_all [Frame.extendRoot₂];
  | .inl _, .inr _, .inr _ => simp_all [Frame.extendRoot₂];
  | .inl _, .inl _, .inr _ => simp_all [Frame.extendRoot₂];
  | .inl _, .inl _, .inl _ => simp_all [Frame.extendRoot₂]; omega;
⟩

lemma rooted_original [IsTrans _ F.Rel] {x : F.World} : (extendRoot₂.root (F := F) (r := r) (n := n)) ≺ x := by
  apply extendRoot₂.instIsRooted (F := F) (r := r) |>.direct_rooted_of_trans x;
  tauto;

instance [F.IsTree r] : (F.extendRoot₂ r n).IsTree extendRoot₂.root where

instance instIsFiniteTree [F.IsFiniteTree r] : (F.extendRoot₂ r n).IsFiniteTree extendRoot₂.root where

def pMorphism : F →ₚ (F.extendRoot₂ r n) where
  toFun := Sum.inr
  forth := by simp [Frame.extendRoot₂];
  back {x y} h := by
    match y with
    | .inl r => simp [Frame.Rel', Frame.extendRoot₂] at h;
    | .inr y => use y; simpa using h;

end Frame.extendRoot₂


def Model.extendRoot₂ (M : Kripke.Model) (r : M.World) [M.IsRooted r] (n : ℕ+) : Kripke.Model where
  toFrame := M.toFrame.extendRoot₂ r n
  Val x a :=
    match x with
    | .inl _ => M.Val r a
    | .inr x => M.Val x a

namespace Model.extendRoot₂

variable {M : Model} {r : M.World} [M.IsRooted r] {x y : M.World} {n : ℕ+}

instance : Coe (M.World) ((M.extendRoot₂ r n).World) := ⟨Sum.inr⟩

protected abbrev root := Frame.extendRoot₂.root (F := M.toFrame) (r := r) (n := n)

lemma rooted_original [IsTrans _ M.Rel] : (extendRoot₂.root (M := M) (r := r) (n := n)) ≺ (Sum.inr x) := Frame.extendRoot₂.rooted_original

def pMorphism : Model.PseudoEpimorphism M (M.extendRoot₂ r n) := PseudoEpimorphism.ofAtomic (Frame.extendRoot₂.pMorphism) $ by
  intros;
  rfl;

lemma modal_equivalence_original_world {x : M.World} : ModalEquivalent (M₁ := M) (M₂ := M.extendRoot₂ r n) x (Sum.inr x) := by
  apply Model.PseudoEpimorphism.modal_equivalence pMorphism;

@[simp]
lemma inr_satisfies_iff {i : M.World} :
  Formula.Kripke.Satisfies (M.extendRoot₂ r n) (Sum.inr i) φ ↔ Formula.Kripke.Satisfies M i φ :=
  modal_equivalence_original_world.symm

open Formula.Kripke in
lemma inl_satisfies_boxdot_iff [IsTrans _ M.Rel] : Satisfies M r (φᵇ) ↔ Satisfies (M.extendRoot₂ r n) (Sum.inl i) (φᵇ) := by
  induction φ using Formula.rec' generalizing i with
  | hatom φ => rfl;
  | hfalsum => rfl;
  | himp φ ψ ihA ihB =>
    replace ihA := @ihA i;
    replace ihB := @ihB i;
    simp_all [Satisfies, Formula.BoxdotTranslation];
  | hbox φ ih =>
    dsimp [Formula.BoxdotTranslation];
    constructor;
    . intro h;
      obtain ⟨h₁, h₂⟩ := Satisfies.and_def.mp h;
      apply Satisfies.and_def.mpr;
      constructor;
      . exact ih.mp h₁;
      . intro x Rix;
        match x with
        | .inl j => apply ih.mp h₁;
        | .inr x =>
          apply inr_satisfies_iff.mpr;
          by_cases erx : r = x;
          . subst erx;
            exact h₁;
          . apply h₂;
            apply Frame.IsRooted.direct_rooted_of_trans;
            tauto;
    . intro h;
      replace ⟨h₁, h₂⟩ := Satisfies.and_def.mp h;
      apply Satisfies.and_def.mpr;
      constructor;
      . apply ih.mpr h₁;
      . intro x Rix;
        exact inr_satisfies_iff.mp $ @h₂ (Sum.inr x) $ by
          simp [Frame.Rel', Model.extendRoot₂, Frame.extendRoot₂]

end Model.extendRoot₂


section

open Classical

variable {M : Kripke.Model} [Finite M.World] [IsTrans _ M.Rel] [IsIrrefl _ M.Rel]
variable {A : Formula _}
variable {l : List M.World} {n : ℕ+}

lemma atmost_one_validates_axiomT_in_irrefl_trans_chain' (l_chain : List.Chain' (· ≺ ·) l)
  : (∀ x ∈ l, x ⊧ (□A ➝ A)) ∨ (∃! x ∈ l, ¬x ⊧ (□A ➝ A)) := by
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
    rcases (List.Chain'.connected_of_trans l_chain y_l x_l (by tauto)) with Ryx | Rxy;
    . have : x ⊧ A := hy₁ x Ryx; contradiction;
    . have : y ⊧ A := hx₁ y Rxy; contradiction;

lemma atmost_one_validates_axiomT_in_irrefl_trans_chain
  (l_chain : List.Chain' (· ≺ ·) l) :
  haveI : Fintype M.World := Fintype.ofFinite _;
  Finset.card { x | x ∈ l ∧ ¬x ⊧ (□A ➝ A) } ≤ 1 := by
  apply Nat.le_one_iff_eq_zero_or_eq_one.mpr;
  rcases atmost_one_validates_axiomT_in_irrefl_trans_chain' (M := M) (l := l) (l_chain := l_chain) (A := A) with h | h;
  . left;
    apply Finset.card_filter_eq_zero_iff.mpr;
    simp_all;
  . right;
    apply Finset.card_eq_one.mpr;
    apply Finset.singleton_iff_unique_mem _ |>.mpr;
    simp_all;

lemma _root_.Finset.ssubset_of_subset_lt_card {s t : Finset α}
  (h_subset : s ⊆ t)
  (h_card_le : s.card < t.card) : s ⊂ t := by
  constructor;
  . assumption;
  . by_contra hC;
    have : t = s := Finset.eq_iff_card_le_of_subset hC |>.mp (by omega);
    subst this;
    simp at h_card_le;

lemma _root_.Finset.eq_card_of_eq {s t : Finset α} (h : s = t) : s.card = t.card := by tauto;

lemma _root_.Finset.sum_le_card {n : ℕ} {s : Finset α} {f : α → ℕ} (hf : ∀ a ∈ s, f a ≤ n)
  : (∑ a ∈ s, f a) ≤ s.card * n :=
  calc
    _ ≤ (∑ x ∈ s, n) := by apply Finset.sum_le_sum hf
    _ = s.card * n   := by simp_all;

lemma validates_axiomT_set_in_irrefl_trans_chain
  (Γ : Finset (Modal.Formula ℕ))
  (l_length : l.length = Γ.card + 1)
  (l_chain : List.Chain' (· ≺ ·) l)
  : ∃ x ∈ l, x ⊧ (Γ.image (λ γ => □γ ➝ γ)).conj := by
  haveI : Fintype M.World := Fintype.ofFinite _;
  let t₁ : Finset M.World := { x | x ∈ l ∧ ∃ A ∈ Γ, ¬x ⊧ (□A ➝ A) };
  let t₂ : Finset M.World := l.toFinset;
  have h₁ : t₁.card ≤ Γ.card :=
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
  have h₂ : t₂.card = l.length :=
    calc
      _ = l.dedup.length := List.card_toFinset l
      _ = l.length       := by
        suffices l.dedup = l by rw [this];
        apply List.dedup_eq_self.mpr;
        apply List.Chain'.noDup_of_irrefl_trans l_chain;
  have : t₁ ⊂ t₂ := Finset.ssubset_of_subset_lt_card (by
    intro x hx;
    replace hx := Finset.mem_filter.mp hx;
    apply List.mem_toFinset.mpr;
    tauto;
  ) (by omega);
  obtain ⟨x, hx₂, nhx₁⟩ := Finset.exists_of_ssubset this;
  replace hx₂ := List.mem_toFinset.mp hx₂;
  replace hx₁ := Finset.mem_filter.not.mp nhx₁;
  push_neg at hx₁;
  use x;
  constructor;
  . assumption;
  . apply Formula.Kripke.Satisfies.finset_conj_def.mpr;
    simp only [Finset.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂];
    intro A hA;
    apply hx₁;
    . simp;
    . assumption;
    . assumption;

end

namespace Model.extendRoot₂

open Classical

variable {M : Model} {r : M.World} [M.IsFinite] [IsTrans _ M.Rel] [IsIrrefl _ M.Rel] [M.IsRooted r] {x y : M.World}

lemma inr_satisfies_axiomT_set
  {Γ : Finset (Modal.Formula ℕ)} :
  letI n : ℕ+ := ⟨Γ.card + 1, by omega⟩;
  ∃ i : Fin n, Formula.Kripke.Satisfies (M.extendRoot₂ r n) (.inl i) (Γ.image (λ γ => □γ ➝ γ) |>.conj)
  := by
  let n : ℕ+ := ⟨Γ.card + 1, by omega⟩;
  let M' := M.extendRoot₂ r n;
  have : Finite M'.World := by
    unfold M' Model.extendRoot₂ Frame.extendRoot₂;
    infer_instance;
  obtain ⟨x, hx₁, hx₂⟩ := @validates_axiomT_set_in_irrefl_trans_chain (M := M')
    (by infer_instance)
    (by apply Frame.extendRoot₂.isTrans)
    (by apply Frame.extendRoot₂.isAsymm.isIrrefl)
    (l := Frame.extendRoot₂.chain)
    (Γ := Γ)
    (Frame.extendRoot₂.chain_length)
    (Frame.extendRoot₂.chain_Chain')
  simp only [List.pure_def, List.bind_eq_flatMap, List.mem_map, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false, M', n] at hx₁;
  obtain ⟨i, _, rfl⟩ := hx₁;
  use i;
  exact hx₂;

end Model.extendRoot₂

end Kripke

end LO.Modal
