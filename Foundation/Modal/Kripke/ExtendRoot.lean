import Foundation.Modal.Boxdot.Basic
import Foundation.Modal.Kripke.Tree
import Foundation.Vorspiel.List.Chain
import Foundation.Vorspiel.Finset.Card
import Foundation.Vorspiel.Fin.Fin1
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finite.Sum


namespace LO.Modal

namespace Kripke

def Frame.extendRoot (F : Kripke.Frame) {r : F.World} [F.IsRootedBy r] (n : ℕ+) : Kripke.Frame where
  World := Fin n ⊕ F.World
  Rel x y :=
    match x, y with
    | .inr x, .inr y => x ≺ y
    | .inr _, .inl _ => False
    | .inl _, .inr _ => True
    | .inl i, .inl j => i < j

namespace Frame.extendRoot

variable {F : Frame} {r : outParam F.World} [F.IsRootedBy r] {x y : F.World} {n : ℕ+}

instance : Coe (F.World) ((F.extendRoot n).World) := ⟨Sum.inr⟩

instance isFinite [F.IsFinite] : (F.extendRoot n).IsFinite := by
  unfold Frame.extendRoot;
  infer_instance;

instance fintype [Fintype F] : Fintype (F.extendRoot n) := instFintypeSum (Fin n) F

protected abbrev root : (F.extendRoot n).World := .inl 0

abbrev extendedWorld (i : Fin n) : F.extendRoot n := .inl i

instance instIsRooted : (F.extendRoot n).IsRootedBy extendRoot.root where
  root_generates := by
    intro x h;
    match x with
    | .inl j =>
      obtain ⟨j, hj⟩ := j;
      apply Relation.TransGen.single;
      apply Nat.zero_lt_of_not_zero;
      simp_all [Frame.Rel', Frame.extendRoot]
    | .inr x =>
      apply Relation.TransGen.single;
      tauto;


protected abbrev chain : List (F.extendRoot n |>.World) := List.finRange n |>.map (Sum.inl ·)

@[simp]
lemma chain_length : extendRoot.chain (F := F) (r := r) (n := n).length = n := by simp

@[simp]
lemma chain_Chain' : List.Chain' (· ≺ ·) (extendRoot.chain (F := F) (r := r) (n := n)) := by
  apply List.chain'_map_of_chain' (R := λ a b => a < b);
  . tauto;
  . simp;


instance isAsymmetric [F.IsAsymmetric] : (F.extendRoot n).IsAsymmetric := ⟨by
  intro x y hxy;
  match x, y with
  | .inr x, .inr y =>
    suffices ¬y ≺ x by tauto;
    exact IsAsymm.asymm _ _ hxy;
  | .inl i, .inl j => simp_all [Frame.extendRoot]; omega;
  | .inl _, .inr _ => simp_all [Frame.extendRoot];
  | .inr _, .inl _ => simp_all [Frame.extendRoot];
⟩

instance isTransitive [F.IsTransitive] : (F.extendRoot n).IsTransitive := ⟨by
  intro x y z hxy hyz;
  match x, y, z with
  | .inr x, .inr y, .inr z =>
    have : x ≺ z := IsTrans.trans _ _ _ hxy hyz;
    assumption;
  | .inr _, .inl _, .inl _ => simp_all [Frame.extendRoot];
  | .inl _, .inr _, .inr _ => simp_all [Frame.extendRoot];
  | .inl _, .inl _, .inr _ => simp_all [Frame.extendRoot];
  | .inl _, .inl _, .inl _ => simp_all [Frame.extendRoot]; omega;
⟩

@[simp] lemma rooted_original [F.IsTransitive] {x : F.World} :
    (extendRoot.root (F := F) (r := r) (n := n)) ≺ x := by
  apply Frame.root_genaretes'!;
  tauto;

instance isTree [F.IsTree r] : (F.extendRoot n).IsTree extendRoot.root where

instance isFiniteTree [F.IsFiniteTree r] : (F.extendRoot n).IsFiniteTree extendRoot.root where

def pMorphism : F →ₚ (F.extendRoot n) where
  toFun := Sum.inr
  forth := by simp [Frame.extendRoot];
  back {x y} h := by
    match y with
    | .inl r => simp [Frame.Rel', Frame.extendRoot] at h;
    | .inr y => use y; simpa using h;

lemma not_root_of_from_root [F.IsTree r] {x : (F.extendRoot n).World} (h : extendRoot.root ≺ x)
  : (∃ i > 0, x = (Sum.inl i)) ∨ (x = r) ∨ (Sum.inr r ≺^+ x) := by
  match x with
  | .inl i =>
    left;
    use i;
    constructor;
    . simp_all [Frame.Rel', extendRoot];
    . tauto;
  | .inr x =>
    by_cases e : x = r;
    . tauto;
    . right;
      right;
      apply Relation.TransGen.single;
      apply pMorphism (F := F).forth;
      apply Frame.root_genaretes'! (x := x) (by tauto);

lemma not_root_of_from_root₁ [F.IsTree r] {x : (F.extendRoot 1).World} (h : extendRoot.root ≺ x)
  : (x = r) ∨ (Sum.inr r ≺^+ x) := by
  rcases not_root_of_from_root h with (⟨i, hi, rfl⟩ | hr | hr) <;> simp_all;

end Frame.extendRoot


def Model.extendRoot (M : Kripke.Model) {r : M.World} [M.IsRootedBy r] (n : ℕ+) : Kripke.Model where
  toFrame := M.toFrame.extendRoot n
  Val x a :=
    match x with
    | .inl _ => M.Val r a
    | .inr x => M.Val x a

namespace Model.extendRoot

variable {M : Model} {r : M.World} [M.IsRootedBy r] {x y : M.World} {n : ℕ+} {φ}

instance : Coe (M.World) ((M.extendRoot n).World) := ⟨Sum.inr⟩

protected abbrev root := Frame.extendRoot.root (F := M.toFrame) (r := r) (n := n)

@[simp] lemma rooted_original [M.IsTransitive] :
    (extendRoot.root (M := M) (r := r) (n := n)) ≺ (Sum.inr x) := Frame.extendRoot.rooted_original

instance isFinite [M.IsFinite] : (M.extendRoot n).IsFinite := Frame.extendRoot.isFinite

instance fintype [Fintype M] : Fintype (M.extendRoot n) := Frame.extendRoot.fintype

instance isTransitive [M.IsTransitive] : (M.extendRoot n).IsTransitive := Frame.extendRoot.isTransitive

instance isAsymmetric [M.IsAsymmetric] : (M.extendRoot n).IsAsymmetric := Frame.extendRoot.isAsymmetric

instance isTree [M.IsTree r] : (M.extendRoot n).IsTree extendRoot.root := Frame.extendRoot.isTree

instance isFiniteTree [M.IsFiniteTree r] : (M.extendRoot n).IsFiniteTree extendRoot.root := Frame.extendRoot.isFiniteTree

def pMorphism : Model.PseudoEpimorphism M (M.extendRoot n) := PseudoEpimorphism.ofAtomic (Frame.extendRoot.pMorphism) $ by
  intros;
  rfl;

lemma modal_equivalence_original_world : ModalEquivalent (M₁ := M) (M₂ := M.extendRoot n) x (Sum.inr x) := by
  apply Model.PseudoEpimorphism.modal_equivalence pMorphism;

@[simp]
lemma inr_satisfies_iff : Formula.Kripke.Satisfies (M.extendRoot n) (Sum.inr x) φ ↔ x ⊧ φ := modal_equivalence_original_world.symm

open Formula.Kripke in
lemma inl_satisfies_boxdot_iff [IsTrans _ M.Rel] : r ⊧ (φᵇ) ↔ Satisfies (M.extendRoot n) (Sum.inl i) (φᵇ) := by
  induction φ generalizing i with
  | hatom φ => rfl;
  | hfalsum => rfl;
  | himp φ ψ ihA ihB =>
    replace ihA := @ihA i;
    replace ihB := @ihB i;
    simp_all [Satisfies, Formula.boxdotTranslate];
  | hbox φ ih =>
    dsimp [Formula.boxdotTranslate];
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
            apply Frame.root_genaretes'!;
            tauto;
    . intro h;
      replace ⟨h₁, h₂⟩ := Satisfies.and_def.mp h;
      apply Satisfies.and_def.mpr;
      constructor;
      . apply ih.mpr h₁;
      . intro x Rix;
        exact inr_satisfies_iff.mp $ @h₂ (Sum.inr x) $ by
          simp [Frame.Rel', Model.extendRoot, Frame.extendRoot]

end Model.extendRoot


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
  rcases atmost_one_validates_axiomT_in_irrefl_trans_chain' (l_chain := l_chain) (A := A) with h | h;
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
  (l_chain : List.Chain' (· ≺ ·) l)
  : ∃ x ∈ l, x ⊧ (Γ.image (λ γ => □γ ➝ γ)).conj := by
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
        apply List.Chain'.noDup_of_irrefl_trans l_chain;
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

variable {M : Model} {r : M.World} [M.IsFinite] [IsTrans _ M.Rel] [IsIrrefl _ M.Rel] [M.IsRootedBy r] {x y : M.World}

lemma inr_satisfies_axiomT_set
  {Γ : Finset (Modal.Formula ℕ)} :
  letI n : ℕ+ := ⟨Γ.card + 1, by omega⟩;
  ∃ i : Fin n, Formula.Kripke.Satisfies (M.extendRoot n) (.inl i) (Γ.image (λ γ => □γ ➝ γ) |>.conj)
  := by
  let n : ℕ+ := ⟨Γ.card + 1, by omega⟩;
  let M' := M.extendRoot n;
  have : Finite M'.World := by
    unfold M' Model.extendRoot Frame.extendRoot;
    infer_instance;
  obtain ⟨x, hx₁, hx₂⟩ := @validates_axiomT_set_in_irrefl_trans_chain (M := M')
    (by infer_instance)
    (by apply isTransitive)
    (by apply isAsymmetric.isIrrefl)
    (l := Frame.extendRoot.chain)
    (Γ := Γ)
    (Frame.extendRoot.chain_length)
    (Frame.extendRoot.chain_Chain')
  simp only [List.pure_def, List.bind_eq_flatMap, List.mem_map, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false, M', n] at hx₁;
  obtain ⟨i, _, rfl⟩ := hx₁;
  use i;
  exact hx₂;

end Model.extendRoot

end Kripke


end LO.Modal
