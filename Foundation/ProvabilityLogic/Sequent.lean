module

public import Foundation.ProvabilityLogic.Formula
public import Mathlib.Data.List.Sort

/-!
# Sequents
-/

@[expose] public section

namespace FFL.ProvabilityLogic

structure Sequent (α : Type*) where
  ant : FormulaFinset α
  suc : FormulaFinset α

infix:50 " ⟹ " => Sequent.mk

/-- A sequent labelled with one of `n` layers.

- [KK23]
-/
structure LayeredSequent (n : ℕ) (α : Type*) extends Sequent α where
  level : Fin n

notation:50 Γ:51 " ⟹[" ℓ "] " Δ:51 => LayeredSequent.mk (Sequent.mk Γ Δ) ℓ

namespace Sequent

variable {α : Type*} {S T : Sequent α} {B C : Formula α}

structure Subset (S T : Sequent α) : Prop where
  ant : S.ant ⊆ T.ant
  suc : S.suc ⊆ T.suc

instance : HasSubset (Sequent α) := ⟨Subset⟩

@[simp] lemma subset_iff : S ⊆ T ↔ S.ant ⊆ T.ant ∧ S.suc ⊆ T.suc := ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

structure Saturated (S : Sequent α) : Prop where
  impL : ∀ {A B}, A 🡒 B ∈ S.ant → A ∈ S.suc ∨ B ∈ S.ant
  impR : ∀ {A B}, A 🡒 B ∈ S.suc → A ∈ S.ant ∧ B ∈ S.suc

variable [DecidableEq α]

@[grind]
def subfmls (S : Sequent α) : FormulaFinset α := S.ant.subfmls ∪ S.suc.subfmls

@[grind .] lemma subset_subfmls : S.ant ∪ S.suc ⊆ S.subfmls := by
  have := FormulaFinset.subset_subfmls (Γ := S.ant);
  have := FormulaFinset.subset_subfmls (Γ := S.suc);
  grind;

@[grind →]
lemma mem_subfmls_subfmls (hB : B ∈ S.subfmls) (hC : C ∈ B.subfmls) : C ∈ S.subfmls := by
  grind [FormulaFinset.mem_subfmls_subfmls];

/-! ### Saturation -/

/-- `D` holds of every sequent sharing a formula between its two sides and is closed under the
implication rules; typically `D` is derivability in a sequent calculus. -/
structure IsImpClosed (D : Sequent α → Prop) : Prop where
  union {S : Sequent α} {A : Formula α} : A ∈ S.ant → A ∈ S.suc → D S
  impL {Γ Δ : FormulaFinset α} {A B : Formula α} :
    D (Γ ⟹ insert A Δ) → D (insert B Γ ⟹ Δ) → D (insert (A 🡒 B) Γ ⟹ Δ)
  impR {Γ Δ : FormulaFinset α} {A B : Formula α} :
    D (insert A Γ ⟹ insert B Δ) → D (Γ ⟹ insert (A 🡒 B) Δ)

variable {D : Sequent α → Prop} (hD : IsImpClosed D)

open Classical in
/-- One saturation step for a formula, keeping `D` false. -/
noncomputable def saturateStep : Formula α → { S // ¬D S } → { S // ¬D S }
  | A 🡒 B, ⟨S, hS⟩ =>
    if hAB : A 🡒 B ∈ S.ant then
      if h : D (S.ant ⟹ insert A S.suc) then
        ⟨insert B S.ant ⟹ S.suc, fun h' ↦ hS <| by
          simpa [Finset.insert_eq_of_mem hAB] using hD.impL h h'⟩
      else ⟨S.ant ⟹ insert A S.suc, h⟩
    else if hAB : A 🡒 B ∈ S.suc then
      ⟨insert A S.ant ⟹ insert B S.suc, fun h' ↦ hS <| by
        simpa [Finset.insert_eq_of_mem hAB] using hD.impR h'⟩
    else ⟨S, hS⟩
  | □A, ⟨S, hS⟩ =>
    if h : □A ∈ S.ant ∧ ¬D (insert A S.ant ⟹ S.suc) then ⟨insert A S.ant ⟹ S.suc, h.2⟩
    else ⟨S, hS⟩
  | _, S => S

/-- The saturation steps for a list of formulas, processed from the last to the first. -/
noncomputable def saturate (S₀ : Sequent α) (h₀ : ¬D S₀) (l : List (Formula α)) : { S // ¬D S } :=
  l.foldr (saturateStep hD) ⟨S₀, h₀⟩

variable {hD} {S : { S // ¬D S }} {x C A B : Formula α}

lemma subset_saturateStep : S.1 ⊆ (saturateStep hD x S).1 := by
  obtain ⟨S, hS⟩ := S;
  cases x <;> simp only [saturateStep] <;> (try split_ifs) <;> simp [Finset.subset_insert];

lemma saturateStep_new :
    (C ∈ (saturateStep hD x S).1.ant →
      C ∈ S.1.ant ∨ C ∈ x.subfmls ∧ C.complexity < x.complexity) ∧
    (C ∈ (saturateStep hD x S).1.suc →
      C ∈ S.1.suc ∨ C ∈ x.subfmls ∧ C.complexity < x.complexity) := by
  obtain ⟨S, hS⟩ := S;
  cases x <;> simp only [saturateStep] <;> (try split_ifs) <;> (try simp) <;> grind;

lemma saturateStep_imp :
    (A 🡒 B ∈ (saturateStep hD (A 🡒 B) S).1.ant →
      A ∈ (saturateStep hD (A 🡒 B) S).1.suc ∨ B ∈ (saturateStep hD (A 🡒 B) S).1.ant) ∧
    (A 🡒 B ∈ (saturateStep hD (A 🡒 B) S).1.suc →
      A ∈ (saturateStep hD (A 🡒 B) S).1.ant ∧ B ∈ (saturateStep hD (A 🡒 B) S).1.suc) := by
  obtain ⟨S, hS⟩ := S;
  have h₁ : A ≠ A 🡒 B := fun h ↦ by simpa using congrArg Formula.complexity h;
  have h₂ : B ≠ A 🡒 B := fun h ↦ by simpa using congrArg Formula.complexity h;
  have := h₁.symm;
  have := h₂.symm;
  have := fun h₁ h₂ ↦ hS (hD.union (A := A 🡒 B) h₁ h₂);
  simp only [saturateStep];
  split_ifs <;> simp_all;

lemma saturateStep_box (hbox : ∀ {Γ Δ A}, D (insert A Γ ⟹ Δ) → D (insert (□A) Γ ⟹ Δ)) :
    □A ∈ (saturateStep hD (□A) S).1.ant → A ∈ (saturateStep hD (□A) S).1.ant := by
  obtain ⟨S, hS⟩ := S;
  simp only [saturateStep];
  split_ifs with h;
  . simp;
  . intro hA;
    by_contra hA';
    exact hS <| by simpa [Finset.insert_eq_of_mem hA] using hbox (not_and.mp h hA |> not_not.mp);

variable {S₀ : Sequent α} {h₀ : ¬D S₀} {l : List (Formula α)}

lemma subset_saturate : S₀ ⊆ (saturate hD S₀ h₀ l).1 := by
  induction l with
  | nil => exact ⟨subset_refl _, subset_refl _⟩;
  | cons x l ih =>
    have h := subset_saturateStep (hD := hD) (x := x) (S := saturate hD S₀ h₀ l);
    exact ⟨ih.ant.trans h.ant, ih.suc.trans h.suc⟩;

lemma saturate_subset_subfmls {BS : Sequent α} (hS₀ : S₀.ant ∪ S₀.suc ⊆ BS.subfmls)
    (hl : ∀ C ∈ l, C ∈ BS.subfmls) :
    (saturate hD S₀ h₀ l).1.ant ∪ (saturate hD S₀ h₀ l).1.suc ⊆ BS.subfmls := by
  induction l with
  | nil => exact hS₀;
  | cons x l ih =>
    have ih := ih (fun C hC ↦ hl C (by simp [hC]));
    have hx := hl x (by simp);
    have h := fun {C} ↦ saturateStep_new (hD := hD) (x := x) (S := saturate hD S₀ h₀ l) (C := C);
    intro C hC;
    rcases Finset.mem_union.mp hC with hC | hC;
    . rcases h.1 hC with hC | ⟨hC, -⟩;
      . exact ih (Finset.mem_union_left _ hC);
      . exact mem_subfmls_subfmls hx hC;
    . rcases h.2 hC with hC | ⟨hC, -⟩;
      . exact ih (Finset.mem_union_right _ hC);
      . exact mem_subfmls_subfmls hx hC;

lemma saturate_saturated (hl : l.Pairwise (·.complexity ≤ ·.complexity)) :
    (∀ {A B}, A 🡒 B ∈ l → A 🡒 B ∈ (saturate hD S₀ h₀ l).1.ant →
      A ∈ (saturate hD S₀ h₀ l).1.suc ∨ B ∈ (saturate hD S₀ h₀ l).1.ant) ∧
    (∀ {A B}, A 🡒 B ∈ l → A 🡒 B ∈ (saturate hD S₀ h₀ l).1.suc →
      A ∈ (saturate hD S₀ h₀ l).1.ant ∧ B ∈ (saturate hD S₀ h₀ l).1.suc) ∧
    ((∀ {Γ Δ A}, D (insert A Γ ⟹ Δ) → D (insert (□A) Γ ⟹ Δ)) →
      ∀ {A}, □A ∈ l → □A ∈ (saturate hD S₀ h₀ l).1.ant → A ∈ (saturate hD S₀ h₀ l).1.ant) := by
  induction l with
  | nil => simp;
  | cons x l ih =>
    obtain ⟨hx, hl⟩ := List.pairwise_cons.mp hl;
    obtain ⟨ih₁, ih₂, ih₃⟩ := ih hl;
    have hsub : (saturate hD S₀ h₀ l).1 ⊆ (saturate hD S₀ h₀ (x :: l)).1 :=
      subset_saturateStep (hD := hD);
    have hnew := fun {C} ↦ saturateStep_new (hD := hD) (x := x) (S := saturate hD S₀ h₀ l) (C := C);
    have old : ∀ {C}, C ∈ l →
        (C ∈ (saturate hD S₀ h₀ (x :: l)).1.ant → C ∈ (saturate hD S₀ h₀ l).1.ant) ∧
        (C ∈ (saturate hD S₀ h₀ (x :: l)).1.suc → C ∈ (saturate hD S₀ h₀ l).1.suc) := by
      intro C hC;
      have := hx C hC;
      constructor;
      . intro h;
        rcases hnew.1 h with h | ⟨-, h⟩;
        . exact h;
        . omega;
      . intro h;
        rcases hnew.2 h with h | ⟨-, h⟩;
        . exact h;
        . omega;
    and_intros;
    . intro A B hAB h;
      rcases List.mem_cons.mp hAB with rfl | hAB;
      . exact (saturateStep_imp (hD := hD)).1 h;
      . rcases ih₁ hAB ((old hAB).1 h) with h | h;
        . exact .inl (hsub.suc h);
        . exact .inr (hsub.ant h);
    . intro A B hAB h;
      rcases List.mem_cons.mp hAB with rfl | hAB;
      . exact (saturateStep_imp (hD := hD)).2 h;
      . obtain ⟨h₁, h₂⟩ := ih₂ hAB ((old hAB).2 h);
        exact ⟨hsub.ant h₁, hsub.suc h₂⟩;
    . intro hbox A hA h;
      rcases List.mem_cons.mp hA with rfl | hA;
      . exact saturateStep_box (hD := hD) hbox h;
      . exact hsub.ant (ih₃ hbox hA ((old hA).1 h));

/-- The subformulas of `BS`, sorted by complexity. -/
noncomputable abbrev sortedSubfmls (BS : Sequent α) : List (Formula α) :=
  BS.subfmls.toList.insertionSort (·.complexity ≤ ·.complexity)

omit hD in
lemma sortedSubfmls_pairwise {BS : Sequent α} :
    (sortedSubfmls BS).Pairwise (·.complexity ≤ ·.complexity) :=
  haveI : Std.Total (fun A B : Formula α ↦ A.complexity ≤ B.complexity) := ⟨fun _ _ ↦ le_total _ _⟩;
  haveI : IsTrans _ (fun A B : Formula α ↦ A.complexity ≤ B.complexity) := ⟨fun _ _ _ ↦ le_trans⟩;
  List.pairwise_insertionSort _ _

/-- Every sequent on which `D` fails extends to a saturated one within the subformulas of `BS`,
which is moreover closed under `□A ↦ A` on the left if `D` is closed under that rule. -/
theorem exists_saturated (hD : IsImpClosed D) {BS S₀ : Sequent α} (h₀ : ¬D S₀)
    (hS₀ : S₀.ant ∪ S₀.suc ⊆ BS.subfmls) :
    ∃ S, S₀ ⊆ S ∧ ¬D S ∧ S.Saturated ∧ S.ant ∪ S.suc ⊆ BS.subfmls ∧
      ((∀ {Γ Δ A}, D (insert A Γ ⟹ Δ) → D (insert (□A) Γ ⟹ Δ)) →
        ∀ {A}, □A ∈ S.ant → A ∈ S.ant) := by
  have hl : ∀ {C}, C ∈ sortedSubfmls BS ↔ C ∈ BS.subfmls := by simp [List.mem_insertionSort];
  have hsub := saturate_subset_subfmls (hD := hD) (h₀ := h₀) hS₀ fun _ ↦ hl.mp;
  obtain ⟨h₁, h₂, h₃⟩ := saturate_saturated (hD := hD) (h₀ := h₀) sortedSubfmls_pairwise;
  use (saturate hD S₀ h₀ (sortedSubfmls BS)).1;
  and_intros;
  . exact subset_saturate;
  . exact (saturate hD S₀ h₀ (sortedSubfmls BS)).2;
  . exact ⟨fun h ↦ h₁ (hl.mpr (hsub (Finset.mem_union_left _ h))) h,
      fun h ↦ h₂ (hl.mpr (hsub (Finset.mem_union_right _ h))) h⟩;
  . exact hsub;
  . exact fun hbox _ h ↦ h₃ hbox (hl.mpr (hsub (Finset.mem_union_left _ h))) h;

end Sequent

namespace LayeredSequent

variable {α : Type*} [DecidableEq α] {n : ℕ}

/-- `D` is closed under the structural and propositional rules at every layer. -/
structure IsPropClosed (D : LayeredSequent n α → Prop) : Prop where
  axm (ℓ : Fin n) (A : Formula α) : D ({A} ⟹[ℓ] {A})
  botL (ℓ : Fin n) : D ({⊥} ⟹[ℓ] ∅)
  wkL {ℓ : Fin n} {Γ Γ' Δ : FormulaFinset α} : D (Γ ⟹[ℓ] Δ) → Γ ⊆ Γ' → D (Γ' ⟹[ℓ] Δ)
  wkR {ℓ : Fin n} {Γ Δ Δ' : FormulaFinset α} : D (Γ ⟹[ℓ] Δ) → Δ ⊆ Δ' → D (Γ ⟹[ℓ] Δ')
  impL {ℓ : Fin n} {Γ Δ : FormulaFinset α} {A B : Formula α} :
    D (Γ ⟹[ℓ] insert A Δ) → D (insert B Γ ⟹[ℓ] Δ) → D (insert (A 🡒 B) Γ ⟹[ℓ] Δ)
  impR {ℓ : Fin n} {Γ Δ : FormulaFinset α} {A B : Formula α} :
    D (insert A Γ ⟹[ℓ] insert B Δ) → D (Γ ⟹[ℓ] insert (A 🡒 B) Δ)

namespace IsPropClosed

variable {D : LayeredSequent n α → Prop} (hD : IsPropClosed D) {ℓ : Fin n}
         {Γ Δ : FormulaFinset α} {A : Formula α}
include hD

lemma union (A : Formula α) (hΓ : A ∈ Γ) (hΔ : A ∈ Δ) : D (Γ ⟹[ℓ] Δ) :=
  hD.wkR (hD.wkL (hD.axm ℓ A) (by simpa)) (by simpa)

lemma botL_mem (h : ⊥ ∈ Γ) : D (Γ ⟹[ℓ] Δ) := hD.wkR (hD.wkL (hD.botL ℓ) (by simpa)) (by simp)

lemma isImpClosed (ℓ : Fin n) : Sequent.IsImpClosed fun S ↦ D (S.ant ⟹[ℓ] S.suc) :=
  ⟨fun h₁ h₂ ↦ hD.union _ h₁ h₂, hD.impL, hD.impR⟩

end IsPropClosed

end LayeredSequent

end FFL.ProvabilityLogic

end
