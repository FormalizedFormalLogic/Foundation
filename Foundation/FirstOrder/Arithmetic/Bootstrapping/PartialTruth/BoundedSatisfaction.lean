module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.PartialTruth.BoundedSatisfactionTable
public import Foundation.FirstOrder.Arithmetic.HFS.Superexp
import Mathlib.Tactic.Ring

/-!
# Satisfaction for $\Delta_0$ formulas

Every well-formed internal $\Delta_0$ code `z` has a satisfaction table under every assignment
`e`. The statement is $\Pi_2$, so the induction on `z` is run on a bounded form of it: tables are
bounded by `tableBound z e`, an exponential tower whose height decreases along the induction.
`BoundedSatisfaction z e` says that some table rooted at `⟪z, e⟫` gives it the value `1`; by
uniqueness of tables it is $\Delta_1$-definable, and it satisfies Tarski's conditions, commutes
with negation and with substitution of coded terms.

## References

- [HP98, 1.64, Lemma I.1.68(2), Theorem I.1.70, Definition I.1.71, Lemma I.1.72, Lemma I.1.73]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL.FirstOrder.Bounding (HierarchySymbol)

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Existence of satisfaction tables -/

section existence

/-! ### Elementary exponential bounds -/

lemma mul_le_exp_add (a b : V) : a * b ≤ Exp.exp (a + b) :=
  calc a * b ≤ Exp.exp a * Exp.exp b :=
        mul_le_mul (le_of_lt (lt_exp a)) (le_of_lt (lt_exp b)) (by simp) (by simp)
    _ = Exp.exp (a + b) := (exp_add a b).symm

lemma exp_add_le (a c : V) : Exp.exp a + c ≤ Exp.exp (a + c + 1) := by
  have h1 : c + 2 ≤ Exp.exp (c + 1) := by
    have : c + 1 + 1 ≤ Exp.exp (c + 1) := succ_le_iff_lt.mpr (lt_exp (c + 1));
    simpa [add_assoc, one_add_one_eq_two] using this;
  have h2 : (1 : V) ≤ Exp.exp a := by
    have := succ_le_iff_lt.mpr (exp_pos a);
    simp;
  have hc : c ≤ Exp.exp a * c := le_mul_of_one_le_left (by simp) h2;
  have he : Exp.exp a ≤ Exp.exp a * 2 := le_mul_of_one_le_right (by simp) (by simp);
  calc Exp.exp a + c
      ≤ Exp.exp a * 2 + Exp.exp a * c := add_le_add he hc
    _ = Exp.exp a * (c + 2) := by rw [mul_add]; simp [add_comm]
    _ ≤ Exp.exp a * Exp.exp (c + 1) := mul_le_mul le_rfl h1 (by simp) (by simp)
    _ = Exp.exp (a + c + 1) := by rw [← exp_add]; simp [add_assoc];

lemma pair_le_exp (a b : V) : ⟪a, b⟫ ≤ Exp.exp (2 * a + 2 * b + 2) :=
  calc ⟪a, b⟫ ≤ (a + b + 1) ^ 2 := pair_polybound a b
    _ = (a + b + 1) * (a + b + 1) := by ring
    _ ≤ Exp.exp ((a + b + 1) + (a + b + 1)) := mul_le_exp_add _ _
    _ = Exp.exp (2 * a + 2 * b + 2) := by ring_nf

lemma adjoin_le_exp (a v : V) : a ∷ v ≤ Exp.exp (2 * a + 2 * v + 3) := by
  have h1 : (1 : V) ≤ Exp.exp (2 * a + 2 * v + 2) := by simp;
  calc a ∷ v = ⟪a, v⟫ + 1 := adjoin_def a v
    _ ≤ Exp.exp (2 * a + 2 * v + 2) + 1 := add_le_add (pair_le_exp a v) le_rfl
    _ ≤ 2 * Exp.exp (2 * a + 2 * v + 2) := by simp [two_mul]
    _ = Exp.exp (2 * a + 2 * v + 3) := by
        rw [show 2 * a + 2 * v + 3 = (2 * a + 2 * v + 2) + 1 from by ring, exp_succ];

lemma listMax_le_self (v : V) : listMax v ≤ v := by
  apply adjoin_induction 𝚷 (P := fun v ↦ listMax v ≤ v) (by definability) (by simp);
  intro x v ih;
  rw [listMax_adjoin];
  exact max_le (le_of_lt (lt_adjoin x v)) (le_trans ih (le_of_lt (lt_adjoin' x v)));

/-! ### The iterated exponential -/

lemma le_iterExp (x n : V) : x ≤ iterExp x n := by
  apply ISigma1.sigma1_succ_induction (P := fun n ↦ x ≤ iterExp x n) (by definability)
    (by simp);
  intro n ih;
  calc x ≤ iterExp x n := ih
    _ ≤ Exp.exp (iterExp x n) := le_of_lt (lt_exp _)
    _ = iterExp x (n + 1) := (iterExp_succ x n).symm;

lemma iterExp_le_iterExp_left {x y : V} (h : x ≤ y) (n : V) : iterExp x n ≤ iterExp y n := by
  apply ISigma1.sigma1_succ_induction (P := fun n ↦ iterExp x n ≤ iterExp y n) (by definability)
    (by simpa using h);
  intro n ih;
  simpa using exp_monotone_le.mpr ih;

lemma iterExp_add (x m n : V) : iterExp x (m + n) = iterExp (iterExp x m) n := by
  apply ISigma1.sigma1_succ_induction (P := fun n ↦ iterExp x (m + n) = iterExp (iterExp x m) n)
    (by definability) (by simp);
  intro n ih;
  rw [show m + (n + 1) = (m + n) + 1 from by ring, iterExp_succ, ih, iterExp_succ];

lemma iterExp_le_iterExp_right (x : V) {m n : V} (h : m ≤ n) : iterExp x m ≤ iterExp x n := by
  obtain ⟨k, rfl⟩ := le_iff_exists_add.mp h;
  rw [iterExp_add];
  exact le_iterExp _ k;

lemma iterExp_lt_iterExp_succ (x n : V) : iterExp x n < iterExp x (n + 1) := by
  simp;

lemma iterExp_lt_of_lt (x : V) {m n : V} (h : m < n) : iterExp x m < iterExp x n :=
  lt_of_lt_of_le (iterExp_lt_iterExp_succ x m) (iterExp_le_iterExp_right x (lt_iff_succ_le.mp h))

lemma two_mul_le_exp {a : V} (h : 2 ≤ a) : 2 * a ≤ Exp.exp a := by
  obtain ⟨c, rfl⟩ := le_iff_exists_add.mp h;
  have h4 : Exp.exp (2 + c : V) = 4 * Exp.exp c := by
    rw [show (2 : V) + c = c + 1 + 1 from by ring, exp_succ, exp_succ]; ring;
  have hc : c + 1 ≤ Exp.exp c := succ_le_iff_lt.mpr (lt_exp c);
  calc 2 * (2 + c) = 4 + 2 * c := by ring
    _ ≤ (4 + 2 * c) + 2 * c := le_self_add
    _ = 4 * (c + 1) := by ring
    _ ≤ 4 * Exp.exp c := mul_le_mul le_rfl hc (by simp) (by simp)
    _ = Exp.exp (2 + c) := h4.symm;

@[simp] lemma iterExp_one (x : V) : iterExp x 1 = Exp.exp x := by
  rw [show (1 : V) = 0 + 1 from by ring, iterExp_succ, iterExp_zero];

lemma iterExp_two (x : V) : iterExp x 2 = Exp.exp (Exp.exp x) := by
  rw [show (2 : V) = 1 + 1 from by ring, iterExp_succ, iterExp_one];

lemma iterExp_three (x : V) : iterExp x 3 = Exp.exp (Exp.exp (Exp.exp x)) := by
  rw [show (3 : V) = 2 + 1 from by ring, iterExp_succ, iterExp_two];

lemma iterExp_four (x : V) : iterExp x 4 = Exp.exp (Exp.exp (Exp.exp (Exp.exp x))) := by
  rw [show (4 : V) = 3 + 1 from by ring, iterExp_succ, iterExp_three];

/-! ### The bound on a partial satisfaction table -/

def tableExp (z e : V) : V := 4 * z + 3 * e + 31

noncomputable def tableBound (z e : V) : V := iterExp (tableExp z e) (8 * z + 24)

lemma tableExp_mono {p z e : V} (h : p ≤ z) : tableExp p e ≤ tableExp z e :=
  add_le_add (add_le_add (mul_le_mul le_rfl h (by simp) (by simp)) le_rfl) le_rfl

lemma node_le_iterExp {z e v : V} (hv : v ≤ 1) : ⟪⟪z, e⟫, v⟫ ≤ iterExp (tableExp z e) 2 := by
  have h1 : (2 : V) * ⟪z, e⟫ + 2 * v + 2 ≤ Exp.exp (2 * z + 2 * e + 3) + 4 := by
    calc (2 : V) * ⟪z, e⟫ + 2 * v + 2
        ≤ 2 * Exp.exp (2 * z + 2 * e + 2) + 2 * 1 + 2 :=
          add_le_add (add_le_add (mul_le_mul le_rfl (pair_le_exp z e) (by simp) (by simp))
            (mul_le_mul le_rfl hv (by simp) (by simp))) le_rfl
      _ = Exp.exp (2 * z + 2 * e + 2 + 1) + 4 := by rw [← exp_succ]; ring
      _ = Exp.exp (2 * z + 2 * e + 3) + 4 := by
          rw [show 2 * z + 2 * e + 2 + 1 = 2 * z + 2 * e + 3 from by ring];
  have h2 : Exp.exp (2 * z + 2 * e + 3) + 4 ≤ Exp.exp (2 * z + 2 * e + 8) := by
    calc Exp.exp (2 * z + 2 * e + 3) + 4 ≤ Exp.exp (2 * z + 2 * e + 3 + 4 + 1) := exp_add_le _ _
      _ = Exp.exp (2 * z + 2 * e + 8) := by
          rw [show 2 * z + 2 * e + 3 + 4 + 1 = 2 * z + 2 * e + 8 from by ring];
  have h3 : 2 * z + 2 * e + 8 ≤ tableExp z e := by
    calc 2 * z + 2 * e + 8 ≤ (2 * z + 2 * e + 8) + (2 * z + e + 23) := le_self_add
      _ = tableExp z e := by simp only [tableExp]; ring;
  calc ⟪⟪z, e⟫, v⟫ ≤ Exp.exp (2 * ⟪z, e⟫ + 2 * v + 2) := pair_le_exp _ _
    _ ≤ Exp.exp (Exp.exp (2 * z + 2 * e + 8)) := exp_monotone_le.mpr (le_trans h1 h2)
    _ ≤ Exp.exp (Exp.exp (tableExp z e)) := exp_monotone_le.mpr (exp_monotone_le.mpr h3)
    _ = iterExp (tableExp z e) 2 := (iterExp_two _).symm;

lemma tableExp_step {z p u x e : V} (hp : p < z) (hu : u < z) (hx : x < termVal (0 ∷ e) u) :
    tableExp p (x ∷ e) ≤ iterExp (tableExp z e) 4 := by
  have hxE : x ≤ Exp.exp ((e + 2) * (z + 1)) := by
    have h2 : listMax (0 ∷ e) ≤ e := by simpa using listMax_le_self e;
    have h3 : (listMax (0 ∷ e) + 2) * (u + 1) ≤ (e + 2) * (z + 1) :=
      mul_le_mul (add_le_add h2 le_rfl) (add_le_add (le_of_lt hu) le_rfl) (by simp) (by simp);
    exact le_of_lt (lt_of_lt_of_le hx
      (le_trans (termVal_le_poly _ _) (exp_monotone_le.mpr h3)));
  have hb : 3 * (x ∷ e) ≤ Exp.exp (2 * x + 2 * e + 5) := by
    calc 3 * (x ∷ e) ≤ 3 * Exp.exp (2 * x + 2 * e + 3) :=
          mul_le_mul le_rfl (adjoin_le_exp x e) (by simp) (by simp)
      _ ≤ 3 * Exp.exp (2 * x + 2 * e + 3) + Exp.exp (2 * x + 2 * e + 3) := le_self_add
      _ = 4 * Exp.exp (2 * x + 2 * e + 3) := by ring
      _ = Exp.exp (2 * x + 2 * e + 5) := by
          rw [show 2 * x + 2 * e + 5 = (2 * x + 2 * e + 3) + 1 + 1 from by ring, exp_succ,
            exp_succ];
          ring;
  have step1 : tableExp p (x ∷ e) ≤ Exp.exp (2 * x + 2 * e + 4 * z + 37) := by
    have hpz : 4 * p ≤ 4 * z := mul_le_mul le_rfl (le_of_lt hp) (by simp) (by simp);
    calc tableExp p (x ∷ e) = 4 * p + 3 * (x ∷ e) + 31 := rfl
      _ ≤ 4 * z + Exp.exp (2 * x + 2 * e + 5) + 31 := add_le_add (add_le_add hpz hb) le_rfl
      _ = Exp.exp (2 * x + 2 * e + 5) + (4 * z + 31) := by ring
      _ ≤ Exp.exp (2 * x + 2 * e + 5 + (4 * z + 31) + 1) := exp_add_le _ _
      _ = Exp.exp (2 * x + 2 * e + 4 * z + 37) := by
          rw [show 2 * x + 2 * e + 5 + (4 * z + 31) + 1 = 2 * x + 2 * e + 4 * z + 37 from by ring];
  have step2 : 2 * x + 2 * e + 4 * z + 37 ≤ Exp.exp ((e + 2) * (z + 1) + 2 * e + 4 * z + 39) := by
    have h2x : 2 * x ≤ Exp.exp ((e + 2) * (z + 1) + 1) := by
      calc 2 * x ≤ 2 * Exp.exp ((e + 2) * (z + 1)) := mul_le_mul le_rfl hxE (by simp) (by simp)
        _ = Exp.exp ((e + 2) * (z + 1) + 1) := (exp_succ _).symm;
    calc 2 * x + 2 * e + 4 * z + 37
        ≤ Exp.exp ((e + 2) * (z + 1) + 1) + 2 * e + 4 * z + 37 :=
          add_le_add (add_le_add (add_le_add h2x le_rfl) le_rfl) le_rfl
      _ = Exp.exp ((e + 2) * (z + 1) + 1) + (2 * e + 4 * z + 37) := by ring
      _ ≤ Exp.exp ((e + 2) * (z + 1) + 1 + (2 * e + 4 * z + 37) + 1) := exp_add_le _ _
      _ = Exp.exp ((e + 2) * (z + 1) + 2 * e + 4 * z + 39) := by
          rw [show (e + 2) * (z + 1) + 1 + (2 * e + 4 * z + 37) + 1
            = (e + 2) * (z + 1) + 2 * e + 4 * z + 39 from by ring];
  have step3 : (e + 2) * (z + 1) + 2 * e + 4 * z + 39 ≤ Exp.exp (5 * z + 3 * e + 43) := by
    have hEE : (e + 2) * (z + 1) ≤ Exp.exp (z + e + 3) := by
      calc (e + 2) * (z + 1) ≤ Exp.exp ((e + 2) + (z + 1)) := mul_le_exp_add _ _
        _ = Exp.exp (z + e + 3) := by rw [show (e + 2) + (z + 1) = z + e + 3 from by ring];
    calc (e + 2) * (z + 1) + 2 * e + 4 * z + 39
        ≤ Exp.exp (z + e + 3) + 2 * e + 4 * z + 39 :=
          add_le_add (add_le_add (add_le_add hEE le_rfl) le_rfl) le_rfl
      _ = Exp.exp (z + e + 3) + (2 * e + 4 * z + 39) := by ring
      _ ≤ Exp.exp (z + e + 3 + (2 * e + 4 * z + 39) + 1) := exp_add_le _ _
      _ = Exp.exp (5 * z + 3 * e + 43) := by
          rw [show z + e + 3 + (2 * e + 4 * z + 39) + 1 = 5 * z + 3 * e + 43 from by ring];
  have step4 : 5 * z + 3 * e + 43 ≤ Exp.exp (tableExp z e) := by
    have h2 : (2 : V) ≤ tableExp z e := by
      calc (2 : V) ≤ 2 + (4 * z + 3 * e + 29) := le_self_add
        _ = tableExp z e := by simp only [tableExp]; ring;
    calc 5 * z + 3 * e + 43 ≤ (5 * z + 3 * e + 43) + (3 * z + 3 * e + 19) := le_self_add
      _ = 2 * tableExp z e := by simp only [tableExp]; ring
      _ ≤ Exp.exp (tableExp z e) := two_mul_le_exp h2;
  calc tableExp p (x ∷ e) ≤ Exp.exp (2 * x + 2 * e + 4 * z + 37) := step1
    _ ≤ Exp.exp (Exp.exp ((e + 2) * (z + 1) + 2 * e + 4 * z + 39)) := exp_monotone_le.mpr step2
    _ ≤ Exp.exp (Exp.exp (Exp.exp (5 * z + 3 * e + 43))) :=
      exp_monotone_le.mpr (exp_monotone_le.mpr step3)
    _ ≤ Exp.exp (Exp.exp (Exp.exp (Exp.exp (tableExp z e)))) :=
        exp_monotone_le.mpr (exp_monotone_le.mpr (exp_monotone_le.mpr step4))
    _ = iterExp (tableExp z e) 4 := (iterExp_four _).symm;

/-! ### Atomic codes over `ℒₒᵣ` -/

lemma coe_quote_eq : (⌜(Language.Eq.eq : (ℒₒᵣ).Rel 2)⌝ : V) = 0 := coe_eqIndex_eq

lemma coe_quote_lt : (⌜(Language.LT.lt : (ℒₒᵣ).Rel 2)⌝ : V) = 1 := coe_ltIndex_eq

lemma rel_cases {k r v : V} (h : IsUFormula ℒₒᵣ (^rel k r v)) :
    (∃ t u, IsUTerm ℒₒᵣ t ∧ IsUTerm ℒₒᵣ u ∧ ^rel k r v = t ^= u) ∨
    (∃ t u, IsUTerm ℒₒᵣ t ∧ IsUTerm ℒₒᵣ u ∧ ^rel k r v = t ^< u) := by
  obtain ⟨hr, hv⟩ := IsUFormula.rel.mp h;
  rcases Arithmetic.isRel_iff_LOR.mp hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    obtain ⟨a, b, ha, hb, rfl⟩ := IsUTermVec.two_iff.mp hv;
  · left; exact ⟨a, b, ha, hb, by rw [Arithmetic.qqEQ, coe_quote_eq, coe_eqIndex_eq]⟩;
  · right; exact ⟨a, b, ha, hb, by rw [Arithmetic.qqLT, coe_quote_lt, coe_ltIndex_eq]⟩;

lemma nrel_cases {k r v : V} (h : IsUFormula ℒₒᵣ (^nrel k r v)) :
    (∃ t u, IsUTerm ℒₒᵣ t ∧ IsUTerm ℒₒᵣ u ∧ ^nrel k r v = t ^≠ u) ∨
    (∃ t u, IsUTerm ℒₒᵣ t ∧ IsUTerm ℒₒᵣ u ∧ ^nrel k r v = t ^≮ u) := by
  obtain ⟨hr, hv⟩ := IsUFormula.nrel.mp h;
  rcases Arithmetic.isRel_iff_LOR.mp hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    obtain ⟨a, b, ha, hb, rfl⟩ := IsUTermVec.two_iff.mp hv;
  · left; exact ⟨a, b, ha, hb, by rw [Arithmetic.qqNEQ, coe_quote_eq, coe_eqIndex_eq]⟩;
  · right; exact ⟨a, b, ha, hb, by rw [Arithmetic.qqNLT, coe_quote_lt, coe_ltIndex_eq]⟩;

/-! ### The clauses of a table as standalone predicates -/

namespace BoundedSatisfactionTable

variable {q q₁ q₂ Q z e z' e' n p p₁ p₂ u t v : V}

def Spec (q z' e' : V) : Prop := (z' = ^⊤ ∧ ⟪⟪z', e'⟫, 1⟫ ∈ q) ∨ (z' = ^⊥ ∧ ⟪⟪z', e'⟫, 0⟫ ∈ q) ∨
  (∃ t u, IsUTerm ℒₒᵣ t ∧ IsUTerm ℒₒᵣ u ∧ z' = t ^= u ∧
    (⟪⟪z', e'⟫, 1⟫ ∈ q ↔ termVal e' t = termVal e' u) ∧
    (⟪⟪z', e'⟫, 0⟫ ∈ q ↔ termVal e' t ≠ termVal e' u)) ∨
  (∃ t u, IsUTerm ℒₒᵣ t ∧ IsUTerm ℒₒᵣ u ∧ z' = t ^≠ u ∧
    (⟪⟪z', e'⟫, 1⟫ ∈ q ↔ termVal e' t ≠ termVal e' u) ∧
    (⟪⟪z', e'⟫, 0⟫ ∈ q ↔ termVal e' t = termVal e' u)) ∨
  (∃ t u, IsUTerm ℒₒᵣ t ∧ IsUTerm ℒₒᵣ u ∧ z' = t ^< u ∧
    (⟪⟪z', e'⟫, 1⟫ ∈ q ↔ termVal e' t < termVal e' u) ∧
    (⟪⟪z', e'⟫, 0⟫ ∈ q ↔ ¬termVal e' t < termVal e' u)) ∨
  (∃ t u, IsUTerm ℒₒᵣ t ∧ IsUTerm ℒₒᵣ u ∧ z' = t ^≮ u ∧
    (⟪⟪z', e'⟫, 1⟫ ∈ q ↔ ¬termVal e' t < termVal e' u) ∧
    (⟪⟪z', e'⟫, 0⟫ ∈ q ↔ termVal e' t < termVal e' u)) ∨
  (∃ p₁ p₂, z' = p₁ ^⋏ p₂ ∧ ⟪p₁, e'⟫ ∈ domain q ∧ ⟪p₂, e'⟫ ∈ domain q ∧
    (⟪⟪z', e'⟫, 1⟫ ∈ q ↔ ⟪⟪p₁, e'⟫, 1⟫ ∈ q ∧ ⟪⟪p₂, e'⟫, 1⟫ ∈ q) ∧
    (⟪⟪z', e'⟫, 0⟫ ∈ q ↔ ⟪⟪p₁, e'⟫, 0⟫ ∈ q ∨ ⟪⟪p₂, e'⟫, 0⟫ ∈ q)) ∨
  (∃ p₁ p₂, z' = p₁ ^⋎ p₂ ∧ ⟪p₁, e'⟫ ∈ domain q ∧ ⟪p₂, e'⟫ ∈ domain q ∧
    (⟪⟪z', e'⟫, 1⟫ ∈ q ↔ ⟪⟪p₁, e'⟫, 1⟫ ∈ q ∨ ⟪⟪p₂, e'⟫, 1⟫ ∈ q) ∧
    (⟪⟪z', e'⟫, 0⟫ ∈ q ↔ ⟪⟪p₁, e'⟫, 0⟫ ∈ q ∧ ⟪⟪p₂, e'⟫, 0⟫ ∈ q)) ∨
  (∃ u p, (∃ t, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧ z' = qqBall u p ∧
    (∀ x < termVal (0 ∷ e') u, ⟪p, x ∷ e'⟫ ∈ domain q) ∧
    (⟪⟪z', e'⟫, 1⟫ ∈ q ↔ ∀ x < termVal (0 ∷ e') u, ⟪⟪p, x ∷ e'⟫, 1⟫ ∈ q) ∧
    (⟪⟪z', e'⟫, 0⟫ ∈ q ↔ ∃ x < termVal (0 ∷ e') u, ⟪⟪p, x ∷ e'⟫, 0⟫ ∈ q)) ∨
  (∃ u p, (∃ t, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧ z' = qqBex u p ∧
    (∀ x < termVal (0 ∷ e') u, ⟪p, x ∷ e'⟫ ∈ domain q) ∧
    (⟪⟪z', e'⟫, 1⟫ ∈ q ↔ ∃ x < termVal (0 ∷ e') u, ⟪⟪p, x ∷ e'⟫, 1⟫ ∈ q) ∧
    (⟪⟪z', e'⟫, 0⟫ ∈ q ↔ ∀ x < termVal (0 ∷ e') u, ⟪⟪p, x ∷ e'⟫, 0⟫ ∈ q))

def MinChild (q n : V) : Prop :=
  (∃ p₁ p₂ e', ⟪p₁ ^⋏ p₂, e'⟫ ∈ domain q ∧ (n = ⟪p₁, e'⟫ ∨ n = ⟪p₂, e'⟫)) ∨
  (∃ p₁ p₂ e', ⟪p₁ ^⋎ p₂, e'⟫ ∈ domain q ∧ (n = ⟪p₁, e'⟫ ∨ n = ⟪p₂, e'⟫)) ∨
  (∃ u p e', ⟪qqBall u p, e'⟫ ∈ domain q ∧ ∃ x < termVal (0 ∷ e') u, n = ⟪p, x ∷ e'⟫) ∨
  (∃ u p e', ⟪qqBex u p, e'⟫ ∈ domain q ∧ ∃ x < termVal (0 ∷ e') u, n = ⟪p, x ∷ e'⟫)

lemma spec' (h : BoundedSatisfactionTable q z e) (hn : ⟪z', e'⟫ ∈ domain q) : Spec q z' e' :=
  h.spec z' e' hn

lemma minimal' (h : BoundedSatisfactionTable q z e) (hn : n ∈ domain q) : n = ⟪z, e⟫ ∨
    MinChild q n := h.minimal n hn

lemma MinChild.mono (hsub : ∀ m ∈ domain q, m ∈ domain Q) (h : MinChild q n) : MinChild Q n := by
  rcases h with ⟨a, b, e'', hd, hc⟩ | ⟨a, b, e'', hd, hc⟩ | ⟨a, b, e'', hd, hx⟩ |
    ⟨a, b, e'', hd, hx⟩;
  · disj 1; exact ⟨a, b, e'', hsub _ hd, hc⟩;
  · disj 2; exact ⟨a, b, e'', hsub _ hd, hc⟩;
  · disj 3; exact ⟨a, b, e'', hsub _ hd, hx⟩;
  · disj 4; exact ⟨a, b, e'', hsub _ hd, hx⟩;

lemma val_iff_of_subset (hQ : IsMapping Q) (hsub : q ⊆ Q) (hn : n ∈ domain q) :
    ⟪n, v⟫ ∈ Q ↔ ⟪n, v⟫ ∈ q := by
  obtain ⟨w, hw⟩ := mem_domain_iff.mp hn;
  exact ⟨fun h ↦ by rw [hQ.uniq h (hsub hw)]; exact hw, fun h ↦ hsub h⟩;

lemma Spec.mono (hQ : IsMapping Q) (hsub : q ⊆ Q) (hd : ⟪z', e'⟫ ∈ domain q) (h : Spec q z' e') :
    Spec Q z' e' := by
  have dom : ∀ m ∈ domain q, m ∈ domain Q := fun m hm ↦ domain_subset_domain_of_subset hsub hm;
  have root : ∀ w : V, ⟪⟪z', e'⟫, w⟫ ∈ Q ↔ ⟪⟪z', e'⟫, w⟫ ∈ q :=
    fun w ↦ val_iff_of_subset hQ hsub hd;
  rcases h with ⟨he, hv⟩ | ⟨he, hv⟩ |
    ⟨a, b, ha, hb, he, hA, hB⟩ | ⟨a, b, ha, hb, he, hA, hB⟩ |
    ⟨a, b, ha, hb, he, hA, hB⟩ | ⟨a, b, ha, hb, he, hA, hB⟩ |
    ⟨a, b, he, hc, hc', hA, hB⟩ | ⟨a, b, he, hc, hc', hA, hB⟩ |
    ⟨a, b, ht, he, hc, hA, hB⟩ | ⟨a, b, ht, he, hc, hA, hB⟩;
  · disj 1; exact ⟨he, hsub hv⟩;
  · disj 2; exact ⟨he, hsub hv⟩;
  · disj 3; exact ⟨a, b, ha, hb, he, (root 1).trans hA, (root 0).trans hB⟩;
  · disj 4; exact ⟨a, b, ha, hb, he, (root 1).trans hA, (root 0).trans hB⟩;
  · disj 5; exact ⟨a, b, ha, hb, he, (root 1).trans hA, (root 0).trans hB⟩;
  · disj 6; exact ⟨a, b, ha, hb, he, (root 1).trans hA, (root 0).trans hB⟩;
  · disj 7;
    exact ⟨a, b, he, dom _ hc, dom _ hc',
      by rw [root 1, hA, val_iff_of_subset hQ hsub hc, val_iff_of_subset hQ hsub hc'],
      by rw [root 0, hB, val_iff_of_subset hQ hsub hc, val_iff_of_subset hQ hsub hc']⟩;
  · disj 8;
    exact ⟨a, b, he, dom _ hc, dom _ hc',
      by rw [root 1, hA, val_iff_of_subset hQ hsub hc, val_iff_of_subset hQ hsub hc'],
      by rw [root 0, hB, val_iff_of_subset hQ hsub hc, val_iff_of_subset hQ hsub hc']⟩;
  · disj 9;
    use a, b;
    and_intros;
    · exact ht;
    · exact he;
    · exact fun x hx ↦ dom _ (hc x hx);
    · rw [root 1, hA];
      exact forall_congr' fun x ↦ imp_congr_right fun hx ↦
        (val_iff_of_subset hQ hsub (hc x hx)).symm;
    · rw [root 0, hB];
      exact exists_congr fun x ↦ and_congr_right fun hx ↦
        (val_iff_of_subset hQ hsub (hc x hx)).symm;
  · disj 10;
    use a, b;
    and_intros;
    · exact ht;
    · exact he;
    · exact fun x hx ↦ dom _ (hc x hx);
    · rw [root 1, hA];
      exact exists_congr fun x ↦ and_congr_right fun hx ↦
        (val_iff_of_subset hQ hsub (hc x hx)).symm;
    · rw [root 0, hB];
      exact forall_congr' fun x ↦ imp_congr_right fun hx ↦
        (val_iff_of_subset hQ hsub (hc x hx)).symm;

/-! ### Gluing tables together -/

variable {z₁ z₂ e₁ e₂ : V}

lemma val_agree (h₁ : BoundedSatisfactionTable q₁ z₁ e₁)
    (h₂ : BoundedSatisfactionTable q₂ z₂ e₂) {y₁ y₂ : V}
    (hn₁ : ⟪n, y₁⟫ ∈ q₁) (hn₂ : ⟪n, y₂⟫ ∈ q₂) : y₁ = y₂ := by
  have hd₁ : ⟪π₁ n, π₂ n⟫ ∈ domain q₁ := by rw [pair_unpair]; exact mem_domain_of_pair_mem hn₁;
  have hd₂ : ⟪π₁ n, π₂ n⟫ ∈ domain q₂ := by rw [pair_unpair]; exact mem_domain_of_pair_mem hn₂;
  obtain ⟨i1, i0⟩ := h₁.agree h₂ (π₁ n) (π₂ n) hd₁ hd₂;
  rw [pair_unpair] at i1 i0;
  rcases h₁.val_zero_or_one (π₁ n) (π₂ n) hd₁ with h' | h' <;> rw [pair_unpair] at h';
  · rw [h₁.isMapping.uniq hn₁ h', h₂.isMapping.uniq hn₂ (i1.mp h')];
  · rw [h₁.isMapping.uniq hn₁ h', h₂.isMapping.uniq hn₂ (i0.mp h')];

lemma isMapping_union (h₁ : BoundedSatisfactionTable q₁ z₁ e₁)
    (h₂ : BoundedSatisfactionTable q₂ z₂ e₂) : IsMapping (q₁ ∪ q₂) := by
  intro x hx;
  obtain ⟨y, hy⟩ := mem_domain_iff.mp hx;
  use y;
  and_intros;
  · exact hy;
  · intro y' hy';
    rcases mem_cup_iff.mp hy with h | h <;> rcases mem_cup_iff.mp hy' with h' | h';
    · exact h₁.isMapping.uniq h' h;
    · exact h₁.val_agree h₂ h h' |>.symm;
    · exact h₂.val_agree h₁ h h' |>.symm;
    · exact h₂.isMapping.uniq h' h;

lemma fst_le_of_mem_domain (h : BoundedSatisfactionTable q z e) : ∀ n ∈ domain q, π₁ n ≤ z := by
  have key : ∀ k n, n ∈ domain q → q ≤ π₁ n + k → π₁ n ≤ z := by
    apply ISigma1.pi1_succ_induction
      (P := fun k ↦ ∀ n, n ∈ domain q → q ≤ π₁ n + k → π₁ n ≤ z) (by definability);
    · intro n hn hle;
      exact absurd (by simpa using hle)
        (not_le.mpr (lt_of_le_of_lt (pi₁_le_self n) (lt_of_mem_domain hn)));
    · intro k IH n hn hle;
      have up : ∀ m, m ∈ domain q → π₁ n < π₁ m → π₁ m ≤ z := by
        intro m hm hlt;
        apply IH m hm;
        calc q ≤ π₁ n + (k + 1) := hle
          _ = π₁ n + 1 + k := by ring
          _ ≤ π₁ m + k := add_le_add (lt_iff_succ_le.mp hlt) le_rfl;
      rcases h.minimal n hn with rfl | ⟨a, b, e'', hm, hc⟩ | ⟨a, b, e'', hm, hc⟩ |
        ⟨w, r, e'', hm, x, hx, rfl⟩ | ⟨w, r, e'', hm, x, hx, rfl⟩;
      · simp;
      · rcases hc with rfl | rfl;
        · exact le_trans (le_of_lt (by simp)) (up _ hm (by simp));
        · exact le_trans (le_of_lt (by simp)) (up _ hm (by simp));
      · rcases hc with rfl | rfl;
        · exact le_trans (le_of_lt (by simp)) (up _ hm (by simp));
        · exact le_trans (le_of_lt (by simp)) (up _ hm (by simp));
      · exact le_trans (le_of_lt (by simp)) (up _ hm (by simp));
      · exact le_trans (le_of_lt (by simp)) (up _ hm (by simp));
  exact fun n hn ↦ key q n hn le_add_self;

lemma root_not_mem_domain (h : BoundedSatisfactionTable q p e₁) (hlt : p < z) :
    ⟪z, e⟫ ∉ domain q := by
  intro hc;
  have : π₁ (⟪z, e⟫ : V) ≤ p := h.fst_le_of_mem_domain _ hc;
  simp only [pi₁_pair] at this;
  exact absurd (lt_of_le_of_lt this hlt) (lt_irrefl z);

/-! ### Building tables -/

lemma of_atom (h : Spec ({⟪⟪z, e⟫, v⟫} : V) z e) :
    BoundedSatisfactionTable ({⟪⟪z, e⟫, v⟫} : V) z e := by
  constructor;
  · exact IsMapping.singleton _ _;
  · simp;
  · intro z' e' hn;
    obtain ⟨rfl, rfl⟩ : z' = z ∧ e' = e := by simpa using hn;
    exact h;
  · intro n hn;
    left;
    simpa using hn;

lemma of_and {N : V} (h₁ : BoundedSatisfactionTable q₁ p₁ e) (h₂ : BoundedSatisfactionTable q₂ p₂ e)
    (hn₁ : ∀ w ∈ q₁, w < N) (hn₂ : ∀ w ∈ q₂, w < N)
    (hr1 : ⟪⟪p₁ ^⋏ p₂, e⟫, 1⟫ < N) (hr0 : ⟪⟪p₁ ^⋏ p₂, e⟫, 0⟫ < N) :
    ∃ Q, BoundedSatisfactionTable Q (p₁ ^⋏ p₂) e ∧ ∀ w ∈ Q, w < N := by
  obtain ⟨v, hv, hv1, hv0⟩ :
      ∃ v : V, (v = 0 ∨ v = 1) ∧ (v = 1 ↔ ⟪⟪p₁, e⟫, 1⟫ ∈ q₁ ∧ ⟪⟪p₂, e⟫, 1⟫ ∈ q₂) ∧
        (v = 0 ↔ ⟪⟪p₁, e⟫, 0⟫ ∈ q₁ ∨ ⟪⟪p₂, e⟫, 0⟫ ∈ q₂) := by
    by_cases h : ⟪⟪p₁, e⟫, 1⟫ ∈ q₁ ∧ ⟪⟪p₂, e⟫, 1⟫ ∈ q₂;
    · use 1;
      and_intros;
      · simp;
      · exact iff_of_true rfl h;
      · apply iff_of_false (by simp);
        rintro (h0 | h0);
        · exact h₁.val_one_ne_zero h.1 h0;
        · exact h₂.val_one_ne_zero h.2 h0;
    · use 0;
      and_intros;
      · simp;
      · exact iff_of_false (by simp) h;
      · apply iff_of_true rfl;
        by_cases h1 : ⟪⟪p₁, e⟫, 1⟫ ∈ q₁;
        · have : ⟪⟪p₂, e⟫, 1⟫ ∉ q₂ := fun hc ↦ h ⟨h1, hc⟩;
          rcases h₂.val_zero_or_one p₂ e h₂.mem_dom_root with hc | hc;
          · exact absurd hc this;
          · right; exact hc;
        · rcases h₁.val_zero_or_one p₁ e h₁.mem_dom_root with hc | hc;
          · exact absurd hc h1;
          · left; exact hc;
  use insert ⟪⟪p₁ ^⋏ p₂, e⟫, v⟫ (q₁ ∪ q₂);
  and_intros;
  · have hnr : ⟪p₁ ^⋏ p₂, e⟫ ∉ domain (q₁ ∪ q₂) := by
      rw [domain_union];
      intro hc;
      rcases mem_cup_iff.mp hc with h | h;
      · exact h₁.root_not_mem_domain (by simp) h;
      · exact h₂.root_not_mem_domain (by simp) h;
    have hmU : IsMapping (q₁ ∪ q₂) := h₁.isMapping_union h₂;
    have hmQ : IsMapping (insert ⟪⟪p₁ ^⋏ p₂, e⟫, v⟫ (q₁ ∪ q₂)) := hmU.insert hnr;
    have hs₁ : q₁ ⊆ insert ⟪⟪p₁ ^⋏ p₂, e⟫, v⟫ (q₁ ∪ q₂) :=
      subset_trans (union_succ_union_left q₁ q₂) (susbset_insert _ _);
    have hs₂ : q₂ ⊆ insert ⟪⟪p₁ ^⋏ p₂, e⟫, v⟫ (q₁ ∪ q₂) :=
      subset_trans (union_succ_union_right q₁ q₂) (susbset_insert _ _);
    have hroot : ∀ w : V, ⟪⟪p₁ ^⋏ p₂, e⟫, w⟫ ∈ insert ⟪⟪p₁ ^⋏ p₂, e⟫, v⟫ (q₁ ∪ q₂) ↔ w = v := by
      intro w;
      constructor;
      · intro h;
        rcases (by simpa using h : ⟪⟪p₁ ^⋏ p₂, e⟫, w⟫ = ⟪⟪p₁ ^⋏ p₂, e⟫, v⟫ ∨ ⟪⟪p₁ ^⋏ p₂, e⟫, w⟫ ∈
          q₁ ∪ q₂) with h | h;
        · exact (pair_ext_iff.mp h).2;
        · exact absurd (mem_domain_of_pair_mem h) hnr;
      · rintro rfl; simp;
    constructor;
    · exact hmQ;
    · simp;
    · intro z' e' hn;
      rcases (by simpa [domain_union] using hn : ⟪z', e'⟫ = ⟪p₁ ^⋏ p₂, e⟫ ∨
          ⟪z', e'⟫ ∈ domain q₁ ∨ ⟪z', e'⟫ ∈ domain q₂) with h | h | h;
      · obtain ⟨rfl, rfl⟩ := pair_ext_iff.mp h;
        disj 7;
        use p₁, p₂;
        and_intros;
        · rfl;
        · exact domain_subset_domain_of_subset hs₁ h₁.mem_dom_root;
        · exact domain_subset_domain_of_subset hs₂ h₂.mem_dom_root;
        · rw [hroot 1, val_iff_of_subset hmQ hs₁ h₁.mem_dom_root,
            val_iff_of_subset hmQ hs₂ h₂.mem_dom_root];
          exact eq_comm.trans hv1;
        · rw [hroot 0, val_iff_of_subset hmQ hs₁ h₁.mem_dom_root,
            val_iff_of_subset hmQ hs₂ h₂.mem_dom_root];
          exact eq_comm.trans hv0;
      · exact (h₁.spec' h).mono hmQ hs₁ h;
      · exact (h₂.spec' h).mono hmQ hs₂ h;
    · intro n hn;
      rcases (by simpa [domain_union] using hn : n = ⟪p₁ ^⋏ p₂, e⟫ ∨ n ∈ domain q₁ ∨ n ∈ domain q₂)
        with h | h | h;
      · disj 1; exact h;
      · rcases h₁.minimal' h with rfl | hm;
        · disj 2; exact ⟨p₁, p₂, e, by simp, by simp⟩;
        · right; exact hm.mono (fun m hm ↦ domain_subset_domain_of_subset hs₁ hm);
      · rcases h₂.minimal' h with rfl | hm;
        · disj 2; exact ⟨p₁, p₂, e, by simp, by simp⟩;
        · right; exact hm.mono (fun m hm ↦ domain_subset_domain_of_subset hs₂ hm);
  · intro w hw;
    rcases (by simpa using hw : w = ⟪⟪p₁ ^⋏ p₂, e⟫, v⟫ ∨ w ∈ q₁ ∨ w ∈ q₂) with rfl | h | h;
    · rcases hv with rfl | rfl;
      · exact hr0;
      · exact hr1;
    · exact hn₁ _ h;
    · exact hn₂ _ h;

lemma of_or {N : V} (h₁ : BoundedSatisfactionTable q₁ p₁ e) (h₂ : BoundedSatisfactionTable q₂ p₂ e)
    (hn₁ : ∀ w ∈ q₁, w < N) (hn₂ : ∀ w ∈ q₂, w < N)
    (hr1 : ⟪⟪p₁ ^⋎ p₂, e⟫, 1⟫ < N) (hr0 : ⟪⟪p₁ ^⋎ p₂, e⟫, 0⟫ < N) :
    ∃ Q, BoundedSatisfactionTable Q (p₁ ^⋎ p₂) e ∧ ∀ w ∈ Q, w < N := by
  obtain ⟨v, hv, hv1, hv0⟩ :
      ∃ v : V, (v = 0 ∨ v = 1) ∧ (v = 1 ↔ ⟪⟪p₁, e⟫, 1⟫ ∈ q₁ ∨ ⟪⟪p₂, e⟫, 1⟫ ∈ q₂) ∧
        (v = 0 ↔ ⟪⟪p₁, e⟫, 0⟫ ∈ q₁ ∧ ⟪⟪p₂, e⟫, 0⟫ ∈ q₂) := by
    by_cases h : ⟪⟪p₁, e⟫, 1⟫ ∈ q₁ ∨ ⟪⟪p₂, e⟫, 1⟫ ∈ q₂;
    · use 1;
      and_intros;
      · simp;
      · exact iff_of_true rfl h;
      · apply iff_of_false (by simp);
        rintro ⟨h0₁, h0₂⟩;
        rcases h with h | h;
        · exact h₁.val_one_ne_zero h h0₁;
        · exact h₂.val_one_ne_zero h h0₂;
    · use 0;
      and_intros;
      · simp;
      · exact iff_of_false (by simp) h;
      · apply iff_of_true rfl;
        constructor;
        · rcases h₁.val_zero_or_one p₁ e h₁.mem_dom_root with hc | hc;
          · exact absurd hc (not_or.mp h).1;
          · exact hc;
        · rcases h₂.val_zero_or_one p₂ e h₂.mem_dom_root with hc | hc;
          · exact absurd hc (not_or.mp h).2;
          · exact hc;
  use insert ⟪⟪p₁ ^⋎ p₂, e⟫, v⟫ (q₁ ∪ q₂);
  and_intros;
  · have hnr : ⟪p₁ ^⋎ p₂, e⟫ ∉ domain (q₁ ∪ q₂) := by
      rw [domain_union];
      intro hc;
      rcases mem_cup_iff.mp hc with h | h;
      · exact h₁.root_not_mem_domain (by simp) h;
      · exact h₂.root_not_mem_domain (by simp) h;
    have hmU : IsMapping (q₁ ∪ q₂) := h₁.isMapping_union h₂;
    have hmQ : IsMapping (insert ⟪⟪p₁ ^⋎ p₂, e⟫, v⟫ (q₁ ∪ q₂)) := hmU.insert hnr;
    have hs₁ : q₁ ⊆ insert ⟪⟪p₁ ^⋎ p₂, e⟫, v⟫ (q₁ ∪ q₂) :=
      subset_trans (union_succ_union_left q₁ q₂) (susbset_insert _ _);
    have hs₂ : q₂ ⊆ insert ⟪⟪p₁ ^⋎ p₂, e⟫, v⟫ (q₁ ∪ q₂) :=
      subset_trans (union_succ_union_right q₁ q₂) (susbset_insert _ _);
    have hroot : ∀ w : V, ⟪⟪p₁ ^⋎ p₂, e⟫, w⟫ ∈ insert ⟪⟪p₁ ^⋎ p₂, e⟫, v⟫ (q₁ ∪ q₂) ↔ w = v := by
      intro w;
      constructor;
      · intro h;
        rcases (by simpa using h : ⟪⟪p₁ ^⋎ p₂, e⟫, w⟫ = ⟪⟪p₁ ^⋎ p₂, e⟫, v⟫ ∨ ⟪⟪p₁ ^⋎ p₂, e⟫, w⟫ ∈
          q₁ ∪ q₂) with h | h;
        · exact (pair_ext_iff.mp h).2;
        · exact absurd (mem_domain_of_pair_mem h) hnr;
      · rintro rfl; simp;
    constructor;
    · exact hmQ;
    · simp;
    · intro z' e' hn;
      rcases (by simpa [domain_union] using hn : ⟪z', e'⟫ = ⟪p₁ ^⋎ p₂, e⟫ ∨
          ⟪z', e'⟫ ∈ domain q₁ ∨ ⟪z', e'⟫ ∈ domain q₂) with h | h | h;
      · obtain ⟨rfl, rfl⟩ := pair_ext_iff.mp h;
        disj 8;
        use p₁, p₂;
        and_intros;
        · rfl;
        · exact domain_subset_domain_of_subset hs₁ h₁.mem_dom_root;
        · exact domain_subset_domain_of_subset hs₂ h₂.mem_dom_root;
        · rw [hroot 1, val_iff_of_subset hmQ hs₁ h₁.mem_dom_root,
            val_iff_of_subset hmQ hs₂ h₂.mem_dom_root];
          exact eq_comm.trans hv1;
        · rw [hroot 0, val_iff_of_subset hmQ hs₁ h₁.mem_dom_root,
            val_iff_of_subset hmQ hs₂ h₂.mem_dom_root];
          exact eq_comm.trans hv0;
      · exact (h₁.spec' h).mono hmQ hs₁ h;
      · exact (h₂.spec' h).mono hmQ hs₂ h;
    · intro n hn;
      rcases (by simpa [domain_union] using hn : n = ⟪p₁ ^⋎ p₂, e⟫ ∨ n ∈ domain q₁ ∨ n ∈ domain q₂)
        with h | h | h;
      · left; exact h;
      · rcases h₁.minimal' h with rfl | hm;
        · disj 3; exact ⟨p₁, p₂, e, by simp, by simp⟩;
        · right; exact hm.mono (fun m hm ↦ domain_subset_domain_of_subset hs₁ hm);
      · rcases h₂.minimal' h with rfl | hm;
        · disj 3; exact ⟨p₁, p₂, e, by simp, by simp⟩;
        · right; exact hm.mono (fun m hm ↦ domain_subset_domain_of_subset hs₂ hm);
  · intro w hw;
    rcases (by simpa using hw : w = ⟪⟪p₁ ^⋎ p₂, e⟫, v⟫ ∨ w ∈ q₁ ∨ w ∈ q₂) with rfl | h | h;
    · rcases hv with rfl | rfl;
      · exact hr0;
      · exact hr1;
    · exact hn₁ _ h;
    · exact hn₂ _ h;

lemma exists_family_union {p e X N : V}
    (H : ∀ x < X, ∃ q, BoundedSatisfactionTable q p (x ∷ e) ∧ ∀ w ∈ q, w < N) :
    ∃ W : V, IsMapping W ∧ (∀ w ∈ W, w < N) ∧
      (∀ n ∈ domain W, ∃ x < X, ∃ r, BoundedSatisfactionTable r p (x ∷ e) ∧ r ⊆ W ∧ n ∈ domain r) ∧
      (∀ x < X, ∃ r, BoundedSatisfactionTable r p (x ∷ e) ∧ r ⊆ W) := by
  obtain ⟨f, hfm, hfd, hfr⟩ :
      ∃ f, IsMapping f ∧ domain f = under X ∧
        ∀ x r : V, ⟪x, r⟫ ∈ f → BoundedSatisfactionTable r p (x ∷ e) ∧ ∀ w ∈ r, w < N :=
    sigmaOne_skolem (R := fun x r : V ↦ BoundedSatisfactionTable r p (x ∷ e) ∧ ∀ w ∈ r, w < N)
      (by definability) (fun x hx ↦ H x (by simpa using hx));
  obtain ⟨W, hW⟩ : ∃ W : V, ∀ w : V, w ∈ W ↔ ∃ x < f, ∃ r < f, ⟪x, r⟫ ∈ f ∧ w ∈ r :=
    (finite_comprehension₁! (Γ := 𝚺) (by definability)
      ⟨f, by rintro i ⟨x, -, r, hrf, -, hir⟩; exact lt_trans (lt_of_mem hir) hrf⟩).exists;
  have hsub : ∀ x r : V, ⟪x, r⟫ ∈ f → r ⊆ W := by
    intro x r hxr w hw;
    have hlt : ⟪x, r⟫ < f := lt_of_mem hxr;
    exact (hW w).mpr ⟨x, lt_of_le_of_lt (le_pair_left x r) hlt, r,
      lt_of_le_of_lt (le_pair_right x r) hlt, hxr, hw⟩;
  have hmem : ∀ w ∈ W, ∃ x r : V, ⟪x, r⟫ ∈ f ∧ w ∈ r := by
    intro w hw;
    obtain ⟨x, -, r, -, hxr, hwr⟩ := (hW w).mp hw;
    exact ⟨x, r, hxr, hwr⟩;
  have hxlt : ∀ x r : V, ⟪x, r⟫ ∈ f → x < X := by
    intro x r hxr;
    have hx : x ∈ domain f := mem_domain_of_pair_mem hxr;
    rw [hfd] at hx;
    simpa using hx;
  use W;
  and_intros;
  · intro n hn;
    obtain ⟨y, hy⟩ := mem_domain_iff.mp hn;
    use y;
    and_intros;
    · exact hy;
    · intro y' hy';
      obtain ⟨x, r, hxr, hyr⟩ := hmem _ hy;
      obtain ⟨x', r', hxr', hyr'⟩ := hmem _ hy';
      exact (hfr x' r' hxr').1.val_agree (hfr x r hxr).1 hyr' hyr;
  · intro w hw;
    obtain ⟨x, r, hxr, hwr⟩ := hmem w hw;
    exact (hfr x r hxr).2 w hwr;
  · intro n hn;
    obtain ⟨y, hy⟩ := mem_domain_iff.mp hn;
    obtain ⟨x, r, hxr, hyr⟩ := hmem _ hy;
    exact ⟨x, hxlt x r hxr, r, (hfr x r hxr).1, hsub x r hxr, mem_domain_of_pair_mem hyr⟩;
  · intro x hx;
    obtain ⟨r, hr⟩ := mem_domain_iff.mp (show x ∈ domain f by rw [hfd]; simpa using hx);
    exact ⟨r, (hfr x r hr).1, hsub x r hr⟩;

lemma of_ball {N : V} (hu : ∃ t, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) (hp : p < qqBall u p)
    (hr1 : ⟪⟪qqBall u p, e⟫, 1⟫ < N) (hr0 : ⟪⟪qqBall u p, e⟫, 0⟫ < N)
    (H : ∀ x < termVal (0 ∷ e) u, ∃ q, BoundedSatisfactionTable q p (x ∷ e) ∧ ∀ w ∈ q, w < N) :
    ∃ Q, BoundedSatisfactionTable Q (qqBall u p) e ∧ ∀ w ∈ Q, w < N := by
  obtain ⟨W, hmW, hWN, hWdom, hWfam⟩ := exists_family_union H;
  have hchild : ∀ x < termVal (0 ∷ e) u, ⟪p, x ∷ e⟫ ∈ domain W := by
    intro x hx;
    obtain ⟨r, hr, hrsub⟩ := hWfam x hx;
    exact domain_subset_domain_of_subset hrsub hr.mem_dom_root;
  have hval : ∀ x < termVal (0 ∷ e) u, ⟪⟪p, x ∷ e⟫, 1⟫ ∈ W ∨ ⟪⟪p, x ∷ e⟫, 0⟫ ∈ W := by
    intro x hx;
    obtain ⟨r, hr, hrsub⟩ := hWfam x hx;
    rcases hr.val_zero_or_one p (x ∷ e) hr.mem_dom_root with h | h;
    · left; exact hrsub h;
    · right; exact hrsub h;
  have hnotin : ⟪qqBall u p, e⟫ ∉ domain W := by
    intro hc;
    obtain ⟨x, -, r, hr, -, hn⟩ := hWdom _ hc;
    exact hr.root_not_mem_domain hp hn;
  obtain ⟨v, hv, hv1, hv0⟩ : ∃ v : V, (v = 0 ∨ v = 1) ∧
    (v = 1 ↔ ∀ x < termVal (0 ∷ e) u, ⟪⟪p, x ∷ e⟫, 1⟫ ∈ W) ∧
      (v = 0 ↔ ∃ x < termVal (0 ∷ e) u, ⟪⟪p, x ∷ e⟫, 0⟫ ∈ W) := by
    by_cases h : ∀ x < termVal (0 ∷ e) u, ⟪⟪p, x ∷ e⟫, 1⟫ ∈ W;
    · use 1;
      and_intros;
      · simp;
      · exact iff_of_true rfl h;
      · apply iff_of_false (by simp);
        rintro ⟨x, hx, h0⟩;
        exact absurd (hmW.uniq (h x hx) h0) (by simp);
    · use 0;
      and_intros;
      · simp;
      · exact iff_of_false (by simp) h;
      · apply iff_of_true rfl;
        push Not at h;
        obtain ⟨x, hx, h1⟩ := h;
        rcases hval x hx with hc | hc;
        · exact absurd hc h1;
        · exact ⟨x, hx, hc⟩;
  use insert ⟪⟪qqBall u p, e⟫, v⟫ W;
  and_intros;
  · have hmQ : IsMapping (insert ⟪⟪qqBall u p, e⟫, v⟫ W) := hmW.insert hnotin;
    have hsW : W ⊆ insert ⟪⟪qqBall u p, e⟫, v⟫ W := susbset_insert _ _;
    have hroot : ∀ w : V, ⟪⟪qqBall u p, e⟫, w⟫ ∈ insert ⟪⟪qqBall u p, e⟫, v⟫ W ↔ w = v := by
      intro w;
      constructor;
      · intro h;
        rcases (by simpa using h : ⟪⟪qqBall u p, e⟫, w⟫ = ⟪⟪qqBall u p, e⟫, v⟫ ∨ ⟪⟪qqBall u p, e⟫,
          w⟫ ∈ W) with h | h;
        · exact (pair_ext_iff.mp h).2;
        · exact absurd (mem_domain_of_pair_mem h) hnotin;
      · rintro rfl; simp;
    constructor;
    · exact hmQ;
    · simp;
    · intro z' e' hn;
      rcases (by simpa using hn : ⟪z', e'⟫ = ⟪qqBall u p, e⟫ ∨ ⟪z', e'⟫ ∈ domain W) with h | h;
      · obtain ⟨rfl, rfl⟩ := pair_ext_iff.mp h;
        disj 9;
        use u, p;
        and_intros;
        · exact hu;
        · rfl;
        · exact fun x hx ↦ domain_subset_domain_of_subset hsW (hchild x hx);
        · rw [hroot 1];
          exact (eq_comm.trans hv1).trans (forall_congr' fun x ↦ imp_congr_right fun hx ↦
            (val_iff_of_subset hmQ hsW (hchild x hx)).symm);
        · rw [hroot 0];
          exact (eq_comm.trans hv0).trans (exists_congr fun x ↦ and_congr_right fun hx ↦
            (val_iff_of_subset hmQ hsW (hchild x hx)).symm);
      · obtain ⟨x, -, r, hr, hrsub, hnd⟩ := hWdom _ h;
        exact (hr.spec' hnd).mono hmQ (subset_trans hrsub hsW) hnd;
    · intro n hn;
      rcases (by simpa using hn : n = ⟪qqBall u p, e⟫ ∨ n ∈ domain W) with h | h;
      · left; exact h;
      · obtain ⟨x, hx, r, hr, hrsub, hnd⟩ := hWdom _ h;
        rcases hr.minimal' hnd with rfl | hm;
        · disj 4; exact ⟨u, p, e, by simp, x, hx, rfl⟩;
        · right; exact hm.mono
            (fun m hm ↦ domain_subset_domain_of_subset (subset_trans hrsub hsW) hm);
  · intro w hw;
    rcases (by simpa using hw : w = ⟪⟪qqBall u p, e⟫, v⟫ ∨ w ∈ W) with rfl | h;
    · rcases hv with rfl | rfl;
      · exact hr0;
      · exact hr1;
    · exact hWN _ h;

lemma of_bex {N : V} (hu : ∃ t, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) (hp : p < qqBex u p)
    (hr1 : ⟪⟪qqBex u p, e⟫, 1⟫ < N) (hr0 : ⟪⟪qqBex u p, e⟫, 0⟫ < N)
    (H : ∀ x < termVal (0 ∷ e) u, ∃ q, BoundedSatisfactionTable q p (x ∷ e) ∧ ∀ w ∈ q, w < N) :
    ∃ Q, BoundedSatisfactionTable Q (qqBex u p) e ∧ ∀ w ∈ Q, w < N := by
  obtain ⟨W, hmW, hWN, hWdom, hWfam⟩ := exists_family_union H;
  have hchild : ∀ x < termVal (0 ∷ e) u, ⟪p, x ∷ e⟫ ∈ domain W := by
    intro x hx;
    obtain ⟨r, hr, hrsub⟩ := hWfam x hx;
    exact domain_subset_domain_of_subset hrsub hr.mem_dom_root;
  have hval : ∀ x < termVal (0 ∷ e) u, ⟪⟪p, x ∷ e⟫, 1⟫ ∈ W ∨ ⟪⟪p, x ∷ e⟫, 0⟫ ∈ W := by
    intro x hx;
    obtain ⟨r, hr, hrsub⟩ := hWfam x hx;
    rcases hr.val_zero_or_one p (x ∷ e) hr.mem_dom_root with h | h;
    · left; exact hrsub h;
    · right; exact hrsub h;
  have hnotin : ⟪qqBex u p, e⟫ ∉ domain W := by
    intro hc;
    obtain ⟨x, -, r, hr, -, hn⟩ := hWdom _ hc;
    exact hr.root_not_mem_domain hp hn;
  obtain ⟨v, hv, hv1, hv0⟩ : ∃ v : V, (v = 0 ∨ v = 1) ∧
    (v = 1 ↔ ∃ x < termVal (0 ∷ e) u, ⟪⟪p, x ∷ e⟫, 1⟫ ∈ W) ∧
      (v = 0 ↔ ∀ x < termVal (0 ∷ e) u, ⟪⟪p, x ∷ e⟫, 0⟫ ∈ W) := by
    by_cases h : ∃ x < termVal (0 ∷ e) u, ⟪⟪p, x ∷ e⟫, 1⟫ ∈ W;
    · use 1;
      and_intros;
      · simp;
      · exact iff_of_true rfl h;
      · apply iff_of_false (by simp);
        intro hall;
        obtain ⟨x, hx, h1⟩ := h;
        exact absurd (hmW.uniq h1 (hall x hx)) (by simp);
    · use 0;
      and_intros;
      · simp;
      · exact iff_of_false (by simp) h;
      · apply iff_of_true rfl;
        intro x hx;
        rcases hval x hx with hc | hc;
        · exact absurd ⟨x, hx, hc⟩ h;
        · exact hc;
  use insert ⟪⟪qqBex u p, e⟫, v⟫ W;
  and_intros;
  · have hmQ : IsMapping (insert ⟪⟪qqBex u p, e⟫, v⟫ W) := hmW.insert hnotin;
    have hsW : W ⊆ insert ⟪⟪qqBex u p, e⟫, v⟫ W := susbset_insert _ _;
    have hroot : ∀ w : V, ⟪⟪qqBex u p, e⟫, w⟫ ∈ insert ⟪⟪qqBex u p, e⟫, v⟫ W ↔ w = v := by
      intro w;
      constructor;
      · intro h;
        rcases (by simpa using h : ⟪⟪qqBex u p, e⟫, w⟫ = ⟪⟪qqBex u p, e⟫, v⟫ ∨ ⟪⟪qqBex u p, e⟫, w⟫ ∈
          W) with h | h;
        · exact (pair_ext_iff.mp h).2;
        · exact absurd (mem_domain_of_pair_mem h) hnotin;
      · rintro rfl; simp;
    constructor;
    · exact hmQ;
    · simp;
    · intro z' e' hn;
      rcases (by simpa using hn : ⟪z', e'⟫ = ⟪qqBex u p, e⟫ ∨ ⟪z', e'⟫ ∈ domain W) with h | h;
      · obtain ⟨rfl, rfl⟩ := pair_ext_iff.mp h;
        disj 10;
        use u, p;
        and_intros;
        · exact hu;
        · rfl;
        · exact fun x hx ↦ domain_subset_domain_of_subset hsW (hchild x hx);
        · rw [hroot 1];
          exact (eq_comm.trans hv1).trans (exists_congr fun x ↦ and_congr_right fun hx ↦
            (val_iff_of_subset hmQ hsW (hchild x hx)).symm);
        · rw [hroot 0];
          exact (eq_comm.trans hv0).trans (forall_congr' fun x ↦ imp_congr_right fun hx ↦
            (val_iff_of_subset hmQ hsW (hchild x hx)).symm);
      · obtain ⟨x, -, r, hr, hrsub, hnd⟩ := hWdom _ h;
        exact (hr.spec' hnd).mono hmQ (subset_trans hrsub hsW) hnd;
    · intro n hn;
      rcases (by simpa using hn : n = ⟪qqBex u p, e⟫ ∨ n ∈ domain W) with h | h;
      · left; exact h;
      · obtain ⟨x, hx, r, hr, hrsub, hnd⟩ := hWdom _ h;
        rcases hr.minimal' hnd with rfl | hm;
        · disj 5; exact ⟨u, p, e, by simp, x, hx, rfl⟩;
        · right; exact hm.mono
            (fun m hm ↦ domain_subset_domain_of_subset (subset_trans hrsub hsW) hm);
  · intro w hw;
    rcases (by simpa using hw : w = ⟪⟪qqBex u p, e⟫, v⟫ ∨ w ∈ W) with rfl | h;
    · rcases hv with rfl | rfl;
      · exact hr0;
      · exact hr1;
    · exact hWN _ h;

/-! ### Bound bookkeeping -/

lemma singleton_le_tableBound {z e v : V} (hv : v ≤ 1) :
    ({⟪⟪z, e⟫, v⟫} : V) ≤ tableBound z e := by
  rw [singleton_def];
  calc Exp.exp ⟪⟪z, e⟫, v⟫ ≤ Exp.exp (iterExp (tableExp z e) 2) :=
         exp_monotone_le.mpr (node_le_iterExp hv)
    _ = iterExp (tableExp z e) 3 := by rw [show (3 : V) = 2 + 1 from by ring, iterExp_succ]
    _ ≤ tableBound z e := by
        rw [tableBound, show 8 * z + 24 = 3 + (8 * z + 21) from by ring, iterExp_add];
        exact le_iterExp _ _;

lemma node_lt_step {z e v : V} (hv : v ≤ 1) :
    ⟪⟪z, e⟫, v⟫ < iterExp (tableExp z e) (8 * z + 21) := by
  calc ⟪⟪z, e⟫, v⟫ ≤ iterExp (tableExp z e) 2 := node_le_iterExp hv
    _ < iterExp (tableExp z e) 3 := iterExp_lt_of_lt _ (by
        rw [show (3 : V) = 2 + 1 from by ring]; simp)
    _ ≤ iterExp (tableExp z e) (8 * z + 21) := by
        rw [show 8 * z + 21 = 3 + (8 * z + 18) from by ring, iterExp_add];
        exact le_iterExp _ _;

lemma exp_step_le_tableBound (z e : V) :
    Exp.exp (iterExp (tableExp z e) (8 * z + 21)) ≤ tableBound z e :=
  calc Exp.exp (iterExp (tableExp z e) (8 * z + 21))
      = iterExp (tableExp z e) (8 * z + 21 + 1) := (iterExp_succ _ _).symm
    _ ≤ iterExp (tableExp z e) (8 * z + 24) := iterExp_le_iterExp_right _ (by
        calc 8 * z + 21 + 1 = 8 * z + 22 := by ring
          _ ≤ 8 * z + 22 + 2 := le_self_add
          _ = 8 * z + 24 := by ring)
    _ = tableBound z e := rfl

lemma tableBound_le_step {p z e : V} (h : p < z) :
    tableBound p e ≤ iterExp (tableExp z e) (8 * z + 21) := by
  have h1 : p + 1 ≤ z := lt_iff_succ_le.mp h;
  calc tableBound p e = iterExp (tableExp p e) (8 * p + 24) := rfl
    _ ≤ iterExp (tableExp z e) (8 * p + 24) :=
      iterExp_le_iterExp_left (tableExp_mono (le_of_lt h)) _
    _ ≤ iterExp (tableExp z e) (8 * z + 21) := by
        apply iterExp_le_iterExp_right _;
        calc 8 * p + 24 = 8 * (p + 1) + 16 := by ring
          _ ≤ 8 * z + 16 := add_le_add (mul_le_mul le_rfl h1 (by simp) (by simp)) le_rfl
          _ ≤ 8 * z + 16 + 5 := le_self_add
          _ = 8 * z + 21 := by ring;

lemma tableBound_le_step_quant {p z u x e : V} (hp : p < z) (hu : u < z)
    (hx : x < termVal (0 ∷ e) u) :
    tableBound p (x ∷ e) ≤ iterExp (tableExp z e) (8 * z + 21) := by
  have h1 : p + 1 ≤ z := lt_iff_succ_le.mp hp;
  calc tableBound p (x ∷ e) = iterExp (tableExp p (x ∷ e)) (8 * p + 24) := rfl
    _ ≤ iterExp (iterExp (tableExp z e) 4) (8 * p + 24) :=
      iterExp_le_iterExp_left (tableExp_step hp hu hx) _
    _ = iterExp (tableExp z e) (4 + (8 * p + 24)) := (iterExp_add _ _ _).symm
    _ ≤ iterExp (tableExp z e) (8 * z + 21) := by
        apply iterExp_le_iterExp_right _;
        calc 4 + (8 * p + 24) = 8 * (p + 1) + 20 := by ring
          _ ≤ 8 * z + 20 := add_le_add (mul_le_mul le_rfl h1 (by simp) (by simp)) le_rfl
          _ ≤ 8 * z + 20 + 1 := le_self_add
          _ = 8 * z + 21 := by ring;

/-! ### The atomic cases -/

lemma exists_atom_table {z e : V} (hz' : IsUFormula ℒₒᵣ z)
    (h : z = ^⊤ ∨ z = ^⊥ ∨ (∃ k r w, z = ^rel k r w) ∨ (∃ k r w, z = ^nrel k r w)) :
    ∃ v : V, v ≤ 1 ∧ BoundedSatisfactionTable ({⟪⟪z, e⟫, v⟫} : V) z e := by
  rcases h with rfl | rfl | ⟨k, r, w, rfl⟩ | ⟨k, r, w, rfl⟩;
  · exact ⟨1, le_rfl, of_atom (by disj 1; exact ⟨rfl, by simp⟩)⟩;
  · exact ⟨0, by simp, of_atom (by disj 2; exact ⟨rfl, by simp⟩)⟩;
  · rcases rel_cases hz' with ⟨t, u, ht, hu, hzz⟩ | ⟨t, u, ht, hu, hzz⟩;
    · rw [hzz];
      by_cases hc : termVal e t = termVal e u;
      · exact ⟨1, le_rfl, of_atom (by disj 3; exact ⟨t, u, ht, hu, rfl, by simp [hc],
          by simp [hc]⟩)⟩;
      · exact ⟨0, by simp, of_atom (by disj 3; exact ⟨t, u, ht, hu, rfl, by simp [hc],
          by simp [hc]⟩)⟩;
    · rw [hzz];
      by_cases hc : termVal e t < termVal e u;
      · exact ⟨1, le_rfl, of_atom (by disj 5; exact ⟨t, u, ht, hu, rfl, by simp [hc],
          by simp [hc]⟩)⟩;
      · exact ⟨0, by simp, of_atom (by disj 5; exact ⟨t, u, ht, hu, rfl, by simp [hc],
          by simp [hc]⟩)⟩;
  · rcases nrel_cases hz' with ⟨t, u, ht, hu, hzz⟩ | ⟨t, u, ht, hu, hzz⟩;
    · rw [hzz];
      by_cases hc : termVal e t = termVal e u;
      · exact ⟨0, by simp, of_atom (by disj 4; exact ⟨t, u, ht, hu, rfl, by simp [hc],
          by simp [hc]⟩)⟩;
      · exact ⟨1, le_rfl, of_atom (by disj 4; exact ⟨t, u, ht, hu, rfl, by simp [hc],
          by simp [hc]⟩)⟩;
    · rw [hzz];
      by_cases hc : termVal e t < termVal e u;
      · exact ⟨0, by simp, of_atom (by disj 6; exact ⟨t, u, ht, hu, rfl, by simp [hc],
          by simp [hc]⟩)⟩;
      · exact ⟨1, le_rfl, of_atom (by disj 6; exact ⟨t, u, ht, hu, rfl, by simp [hc],
          by simp [hc]⟩)⟩;

end BoundedSatisfactionTable

/-! ### Existence -/

theorem BoundedSatisfactionTable.exists {z e : V} (hz : IsBounded z) (hz' : IsUFormula ℒₒᵣ z) :
    ∃ q, BoundedSatisfactionTable q z e := by
  suffices H : ∀ z, IsBounded z →
      ∀ e b, b = tableBound z e → IsUFormula ℒₒᵣ z → ∃ q ≤ b, BoundedSatisfactionTable q z e by
    obtain ⟨q, -, hq⟩ := H z hz e (tableBound z e) rfl hz';
    exact ⟨q, hq⟩;
  apply IsBounded.induction 𝚷
    (P := fun z ↦ ∀ e b, b = tableBound z e → IsUFormula ℒₒᵣ z →
      ∃ q ≤ b, BoundedSatisfactionTable q z e)
    (by simp only [tableBound, tableExp]; definability);
  · intro e b hb hu;
    subst hb;
    obtain ⟨v, hv, hq⟩ := exists_atom_table (e := e) hu (by disj 1; exact rfl);
    exact ⟨_, singleton_le_tableBound hv, hq⟩;
  · intro e b hb hu;
    subst hb;
    obtain ⟨v, hv, hq⟩ := exists_atom_table (e := e) hu (by disj 2; exact rfl);
    exact ⟨_, singleton_le_tableBound hv, hq⟩;
  · intro k r w e b hb hu;
    subst hb;
    obtain ⟨v, hv, hq⟩ := exists_atom_table (e := e) hu (by disj 3; exact ⟨k, r, w, rfl⟩);
    exact ⟨_, singleton_le_tableBound hv, hq⟩;
  · intro k r w e b hb hu;
    subst hb;
    obtain ⟨v, hv, hq⟩ := exists_atom_table (e := e) hu (by disj 4; exact ⟨k, r, w, rfl⟩);
    exact ⟨_, singleton_le_tableBound hv, hq⟩;
  · intro p₁ p₂ hp₁ hp₂ ih₁ ih₂ e b hb hu;
    subst hb;
    obtain ⟨hu₁, hu₂⟩ : IsUFormula ℒₒᵣ p₁ ∧ IsUFormula ℒₒᵣ p₂ := by simpa using hu;
    obtain ⟨q₁, hb₁, hq₁⟩ := ih₁ e _ rfl hu₁;
    obtain ⟨q₂, hb₂, hq₂⟩ := ih₂ e _ rfl hu₂;
    obtain ⟨Q, hQ, hQN⟩ := hq₁.of_and hq₂
      (fun w hw ↦ lt_of_lt_of_le (lt_of_mem hw)
        (le_trans hb₁ (tableBound_le_step (by simp))))
      (fun w hw ↦ lt_of_lt_of_le (lt_of_mem hw)
        (le_trans hb₂ (tableBound_le_step (by simp))))
      (node_lt_step le_rfl) (node_lt_step (by simp));
    use Q;
    and_intros;
    · calc Q ≤ Exp.exp (iterExp (tableExp (p₁ ^⋏ p₂) e) (8 * (p₁ ^⋏ p₂) + 21)) :=
             le_of_lt (lt_exp_iff.mpr hQN)
        _ ≤ tableBound (p₁ ^⋏ p₂) e := exp_step_le_tableBound _ _;
    · exact hQ;
  · intro p₁ p₂ hp₁ hp₂ ih₁ ih₂ e b hb hu;
    subst hb;
    obtain ⟨hu₁, hu₂⟩ : IsUFormula ℒₒᵣ p₁ ∧ IsUFormula ℒₒᵣ p₂ := by simpa using hu;
    obtain ⟨q₁, hb₁, hq₁⟩ := ih₁ e _ rfl hu₁;
    obtain ⟨q₂, hb₂, hq₂⟩ := ih₂ e _ rfl hu₂;
    obtain ⟨Q, hQ, hQN⟩ := hq₁.of_or hq₂
      (fun w hw ↦ lt_of_lt_of_le (lt_of_mem hw)
        (le_trans hb₁ (tableBound_le_step (by simp))))
      (fun w hw ↦ lt_of_lt_of_le (lt_of_mem hw)
        (le_trans hb₂ (tableBound_le_step (by simp))))
      (node_lt_step le_rfl) (node_lt_step (by simp));
    use Q;
    and_intros;
    · calc Q ≤ Exp.exp (iterExp (tableExp (p₁ ^⋎ p₂) e) (8 * (p₁ ^⋎ p₂) + 21)) :=
             le_of_lt (lt_exp_iff.mpr hQN)
        _ ≤ tableBound (p₁ ^⋎ p₂) e := exp_step_le_tableBound _ _;
    · exact hQ;
  · intro t p ht hp ih e b hb hu;
    subst hb;
    have hup : IsUFormula ℒₒᵣ p := (IsUFormula.or.mp (IsUFormula.all.mp hu)).2;
    obtain ⟨Q, hQ, hQN⟩ := of_ball (e := e) ⟨t, ht, rfl⟩ (by simp)
      (node_lt_step le_rfl) (node_lt_step (by simp)) (fun x hx ↦ by
        obtain ⟨q, hqb, hq⟩ := ih (x ∷ e) _ rfl hup;
        exact ⟨q, hq, fun w hw ↦ lt_of_lt_of_le (lt_of_mem hw)
          (le_trans hqb (tableBound_le_step_quant (by simp) (by simp) hx))⟩);
    use Q;
    and_intros;
    · calc Q ≤ Exp.exp (iterExp (tableExp (qqBall (termBShift ℒₒᵣ t) p) e)
                (8 * qqBall (termBShift ℒₒᵣ t) p + 21)) := le_of_lt (lt_exp_iff.mpr hQN)
        _ ≤ tableBound (qqBall (termBShift ℒₒᵣ t) p) e := exp_step_le_tableBound _ _;
    · exact hQ;
  · intro t p ht hp ih e b hb hu;
    subst hb;
    have hup : IsUFormula ℒₒᵣ p := (IsUFormula.and.mp (IsUFormula.ex.mp hu)).2;
    obtain ⟨Q, hQ, hQN⟩ := of_bex (e := e) ⟨t, ht, rfl⟩ (by simp)
      (node_lt_step le_rfl) (node_lt_step (by simp)) <| by
        intro x hx;
        obtain ⟨q, hqb, hq⟩ := ih (x ∷ e) _ rfl hup;
        exact ⟨q, hq, fun w hw ↦ lt_of_lt_of_le (lt_of_mem hw)
          (le_trans hqb (tableBound_le_step_quant (by simp) (by simp) hx))⟩;
    use Q;
    and_intros;
    · calc Q ≤ Exp.exp (iterExp (tableExp (qqBex (termBShift ℒₒᵣ t) p) e)
                (8 * qqBex (termBShift ℒₒᵣ t) p + 21)) := le_of_lt (lt_exp_iff.mpr hQN)
        _ ≤ tableBound (qqBex (termBShift ℒₒᵣ t) p) e := exp_step_le_tableBound _ _;
    · exact hQ;

@[simp] lemma isRel_two_zero : (ℒₒᵣ).IsRel (2 : V) 0 := by
  simpa using Arithmetic.LOR_rel_eqIndex (V := V);

@[simp] lemma isRel_two_one : (ℒₒᵣ).IsRel (2 : V) 1 := by
  simpa using Arithmetic.LOR_rel_ltIndex (V := V);

lemma IsBounded.of_qqBex {u p : V} (h : IsBounded (qqBex u p)) : IsBounded p := by
  obtain ⟨u', q', -, hq', heq⟩ := IsBounded.of_ex (p := (Arithmetic.qqLT (qqBvar 0) u) ^⋏ p) h;
  obtain ⟨-, rfl⟩ := (qqAnd_inj _ _ _ _).mp heq;
  exact hq';

end existence

/-! ## Satisfaction -/

section satisfaction

/-! ### Substitution and the coded quantifiers -/

lemma isSemiterm_of_termBShift {n t : V} (ht : IsUTerm ℒₒᵣ t)
    (h : IsSemiterm ℒₒᵣ (n + 1) (termBShift ℒₒᵣ t)) : IsSemiterm ℒₒᵣ n t :=
  (IsSemiterm.def (L := ℒₒᵣ)).mpr
    ⟨ht, (termBV_termBShift_le (L := ℒₒᵣ) ht n).mp ((IsSemiterm.def (L := ℒₒᵣ)).mp h).2⟩

lemma isSemiformula_qqBall {n t p : V} (ht : IsUTerm ℒₒᵣ t)
    (h : IsSemiformula ℒₒᵣ n (qqBall (termBShift ℒₒᵣ t) p)) :
    IsSemiterm ℒₒᵣ n t ∧ IsSemiformula ℒₒᵣ (n + 1) p := by
  have h' : IsSemiterm ℒₒᵣ (n + 1) (termBShift ℒₒᵣ t) ∧ IsSemiformula ℒₒᵣ (n + 1) p := by
    simpa [qqBall, Arithmetic.qqNLT] using h;
  exact ⟨isSemiterm_of_termBShift ht h'.1, h'.2⟩;

lemma isSemiformula_qqBex {n t p : V} (ht : IsUTerm ℒₒᵣ t)
    (h : IsSemiformula ℒₒᵣ n (qqBex (termBShift ℒₒᵣ t) p)) :
    IsSemiterm ℒₒᵣ n t ∧ IsSemiformula ℒₒᵣ (n + 1) p := by
  have h' : IsSemiterm ℒₒᵣ (n + 1) (termBShift ℒₒᵣ t) ∧ IsSemiformula ℒₒᵣ (n + 1) p := by
    simpa [qqBex, Arithmetic.qqLT] using h;
  exact ⟨isSemiterm_of_termBShift ht h'.1, h'.2⟩;

lemma substs_qqEQ {w t u : V} (ht : IsUTerm ℒₒᵣ t) (hu : IsUTerm ℒₒᵣ u) :
    Bootstrapping.subst ℒₒᵣ w (t ^= u)
      = (termSubst ℒₒᵣ w t) ^= (termSubst ℒₒᵣ w u) := by
  simp [Arithmetic.qqEQ, ht, hu];

lemma substs_qqNEQ {w t u : V} (ht : IsUTerm ℒₒᵣ t) (hu : IsUTerm ℒₒᵣ u) :
    Bootstrapping.subst ℒₒᵣ w (t ^≠ u)
      = (termSubst ℒₒᵣ w t) ^≠ (termSubst ℒₒᵣ w u) := by
  simp [Arithmetic.qqNEQ, ht, hu];

lemma substs_qqLT {w t u : V} (ht : IsUTerm ℒₒᵣ t) (hu : IsUTerm ℒₒᵣ u) :
    Bootstrapping.subst ℒₒᵣ w (t ^< u)
      = (termSubst ℒₒᵣ w t) ^< (termSubst ℒₒᵣ w u) := by
  simp [Arithmetic.qqLT, ht, hu];

lemma substs_qqNLT {w t u : V} (ht : IsUTerm ℒₒᵣ t) (hu : IsUTerm ℒₒᵣ u) :
    Bootstrapping.subst ℒₒᵣ w (t ^≮ u)
      = (termSubst ℒₒᵣ w t) ^≮ (termSubst ℒₒᵣ w u) := by
  simp [Arithmetic.qqNLT, ht, hu];

lemma substs_qqBall {n m w t p : V} (hw : IsSemitermVec ℒₒᵣ n m w) (ht : IsSemiterm ℒₒᵣ n t)
    (hp : IsUFormula ℒₒᵣ p) :
    Bootstrapping.subst ℒₒᵣ w (qqBall (termBShift ℒₒᵣ t) p)
      = qqBall (termBShift ℒₒᵣ (termSubst ℒₒᵣ w t)) (Bootstrapping.subst ℒₒᵣ (qVec ℒₒᵣ w) p) := by
  have hbt : IsUTerm ℒₒᵣ (termBShift ℒₒᵣ t) := ht.isUTerm.termBShift;
  have hlt : IsUFormula ℒₒᵣ ((qqBvar 0 : V) ^≮ termBShift ℒₒᵣ t) := by
    simp [Arithmetic.qqNLT, hbt];
  rw [show qqBall (termBShift ℒₒᵣ t) p = ^∀ (((qqBvar 0 : V) ^≮ termBShift ℒₒᵣ t) ^⋎ p) from rfl,
    substs_all (by simp [hlt, hp]), substs_or hlt hp, substs_qqNLT (by simp) hbt,
    substs_qVec_bShift ht hw];
  simp [qVec, qqBall];

lemma substs_qqBex {n m w t p : V} (hw : IsSemitermVec ℒₒᵣ n m w) (ht : IsSemiterm ℒₒᵣ n t)
    (hp : IsUFormula ℒₒᵣ p) :
    Bootstrapping.subst ℒₒᵣ w (qqBex (termBShift ℒₒᵣ t) p)
      = qqBex (termBShift ℒₒᵣ (termSubst ℒₒᵣ w t)) (Bootstrapping.subst ℒₒᵣ (qVec ℒₒᵣ w) p) := by
  have hbt : IsUTerm ℒₒᵣ (termBShift ℒₒᵣ t) := ht.isUTerm.termBShift;
  have hlt : IsUFormula ℒₒᵣ ((qqBvar 0 : V) ^< termBShift ℒₒᵣ t) := by
    simp [Arithmetic.qqLT, hbt];
  rw [show qqBex (termBShift ℒₒᵣ t) p = ^∃ (((qqBvar 0 : V) ^< termBShift ℒₒᵣ t) ^⋏ p) from rfl,
    substs_ex (by simp [hlt, hp]), substs_and hlt hp, substs_qqLT (by simp) hbt,
    substs_qVec_bShift ht hw];
  simp [qVec, qqBex];

lemma termValVec_qVec {n m w e x : V} (hw : IsSemitermVec ℒₒᵣ n m w) :
    termValVec (x ∷ e) (n + 1) (qVec ℒₒᵣ w) = x ∷ termValVec e n w := by
  have hq : IsUTermVec ℒₒᵣ (n + 1) (qVec ℒₒᵣ w) := hw.qVec.isUTerm;
  apply nth_ext' (n + 1) (by simp [hq]) (by simp [len_termValVec hw.isUTerm]);
  intro i hi;
  rw [nth_termValVec hq hi];
  rcases zero_or_succ i with rfl | ⟨j, rfl⟩;
  · simp [qVec];
  · have hj : j < n := by simpa using hi;
    have hnth : (qVec ℒₒᵣ w).[j + 1] = termBShift ℒₒᵣ w.[j] := by
      rw [qVec, hw.lh];
      simp [nth_termBShiftVec hw.isUTerm hj];
    rw [hnth, termVal_termBShift (hw.isUTerm.nth hj) x e];
    simp [nth_termValVec hw.isUTerm hj];

lemma IsBounded.subst {n m w p : V} (hw : IsSemitermVec ℒₒᵣ n m w)
    (hp : IsSemiformula ℒₒᵣ n p) (h : IsBounded p) :
    IsBounded (Bootstrapping.subst ℒₒᵣ w p) := by
  have H : ∀ p : V, IsBounded p → ∀ n m w, IsSemitermVec ℒₒᵣ n m w → IsSemiformula ℒₒᵣ n p →
      IsBounded (Bootstrapping.subst ℒₒᵣ w p) := by
    apply IsBounded.induction 𝚷
      (P := fun p ↦ ∀ n m w, IsSemitermVec ℒₒᵣ n m w → IsSemiformula ℒₒᵣ n p →
        IsBounded (Bootstrapping.subst ℒₒᵣ w p));
    · definability;
    · intro n m w _ _; simp;
    · intro n m w _ _; simp;
    · intro k r v n m w _ hp;
      obtain ⟨hr, hv⟩ := IsUFormula.rel.mp hp.isUFormula;
      simp [hr, hv];
    · intro k r v n m w _ hp;
      obtain ⟨hr, hv⟩ := IsUFormula.nrel.mp hp.isUFormula;
      simp [hr, hv];
    · intro p q _ _ ihp ihq n m w hw hpq;
      obtain ⟨hp, hq⟩ := IsSemiformula.and.mp hpq;
      rw [substs_and hp.isUFormula hq.isUFormula];
      exact IsBounded.and_iff.mpr ⟨ihp n m w hw hp, ihq n m w hw hq⟩;
    · intro p q _ _ ihp ihq n m w hw hpq;
      obtain ⟨hp, hq⟩ := IsSemiformula.or.mp hpq;
      rw [substs_or hp.isUFormula hq.isUFormula];
      exact IsBounded.or_iff.mpr ⟨ihp n m w hw hp, ihq n m w hw hq⟩;
    · intro t q ht _ ih n m w hw hpq;
      obtain ⟨ht', hq⟩ := isSemiformula_qqBall ht hpq;
      rw [substs_qqBall hw ht' hq.isUFormula];
      exact IsBounded.ball (hw.termSubst ht').isUTerm
        (ih (n + 1) (m + 1) (qVec ℒₒᵣ w) hw.qVec hq);
    · intro t q ht _ ih n m w hw hpq;
      obtain ⟨ht', hq⟩ := isSemiformula_qqBex ht hpq;
      rw [substs_qqBex hw ht' hq.isUFormula];
      exact IsBounded.bex (hw.termSubst ht').isUTerm
        (ih (n + 1) (m + 1) (qVec ℒₒᵣ w) hw.qVec hq);
  exact H p h n m w hw hp;

structure BoundedSatisfaction (z e : V) : Prop where
  isBounded : IsBounded z
  isUFormula : IsUFormula ℒₒᵣ z
  exists_table : ∃ q, BoundedSatisfactionTable q z e ∧ ⟪⟪z, e⟫, 1⟫ ∈ q

namespace BoundedSatisfaction

variable {z e : V}

/-! ### Reading satisfaction off a table -/

lemma iff_mem {r z e p e' : V} (hr : BoundedSatisfactionTable r z e) (hn : ⟪p, e'⟫ ∈ domain r)
    (hp : IsBounded p) (hp' : IsUFormula ℒₒᵣ p) :
    BoundedSatisfaction p e' ↔ ⟪⟪p, e'⟫, 1⟫ ∈ r := by
  constructor;
  · rintro ⟨-, -, s, hs, h1⟩;
    exact (hs.agree hr p e' hs.mem_dom_root hn).1.mp h1;
  · intro h1;
    obtain ⟨s, hs⟩ := BoundedSatisfactionTable.exists hp hp';
    exact ⟨hp, hp', s, hs, (hr.agree hs p e' hn hs.mem_dom_root).1.mp h1⟩;

lemma iff_val {r : V} (hz : IsBounded z) (hz' : IsUFormula ℒₒᵣ z)
    (hr : BoundedSatisfactionTable r z e) :
    BoundedSatisfaction z e ↔ ⟪⟪z, e⟫, 1⟫ ∈ r := iff_mem hr hr.mem_dom_root hz hz'

lemma exists_iff_forall (hz : IsBounded z) (hz' : IsUFormula ℒₒᵣ z) :
    (∃ r, BoundedSatisfactionTable r z e ∧ ⟪⟪z, e⟫, 1⟫ ∈ r) ↔ ∀ r, BoundedSatisfactionTable r z e →
      ⟪⟪z, e⟫, 1⟫ ∈ r := by
  constructor;
  · rintro ⟨s, hs, h1⟩ r hr;
    exact (hs.agree hr z e hs.mem_dom_root hr.mem_dom_root).1.mp h1;
  · intro h;
    obtain ⟨r, hr⟩ := BoundedSatisfactionTable.exists hz hz';
    exact ⟨r, hr, h r hr⟩;

lemma iff_forall {z e : V} :
    BoundedSatisfaction z e ↔
      (IsBounded z ∧ IsUFormula ℒₒᵣ z) ∧ ∀ r, BoundedSatisfactionTable r z e → ⟪⟪z, e⟫, 1⟫ ∈ r := by
  constructor;
  · rintro ⟨hz, hz', h⟩;
    exact ⟨⟨hz, hz'⟩, (exists_iff_forall hz hz').mp h⟩;
  · rintro ⟨⟨hz, hz'⟩, h⟩;
    exact ⟨hz, hz', (exists_iff_forall hz hz').mpr h⟩;

lemma iff_exists {z e : V} :
    BoundedSatisfaction z e ↔
      (IsBounded z ∧ IsUFormula ℒₒᵣ z) ∧ ∃ r, BoundedSatisfactionTable r z e ∧ ⟪⟪z, e⟫, 1⟫ ∈ r :=
  ⟨fun h ↦ ⟨⟨h.isBounded, h.isUFormula⟩, h.exists_table⟩, fun ⟨⟨hz, hz'⟩, h⟩ ↦ ⟨hz, hz', h⟩⟩

end BoundedSatisfaction

noncomputable def boundedSatisfaction : 𝚫ᴬ₁.Semisentence 2 := .mkDelta
  (.mkSigma “z e. (!isBounded.sigma z ∧ !(isUFormula ℒₒᵣ).sigma z) ∧
    ∃ q, !boundedSatisfactionTable.sigma q z e ∧ !BoundedSatisfactionTableF.nodeValDef q z e 1”)
  (.mkPi “z e. (!isBounded.pi z ∧ !(isUFormula ℒₒᵣ).pi z) ∧
    ∀ q, !boundedSatisfactionTable.sigma q z e → !BoundedSatisfactionTableF.nodeValDef q z e 1”)

instance BoundedSatisfaction.defined :
    𝚫ᴬ₁-Relation (BoundedSatisfaction : V → V → Prop) via boundedSatisfaction := .mk <| by
  constructor;
  · intro v;
    suffices IsBounded (v 0) → IsUFormula ℒₒᵣ (v 0) →
        ((∃ r, BoundedSatisfactionTable r (v 0) (v 1) ∧ ⟪⟪v 0, v 1⟫, 1⟫ ∈ r) ↔
          ∀ r, BoundedSatisfactionTable r (v 0) (v 1) → ⟪⟪v 0, v 1⟫, 1⟫ ∈ r) by
      simpa [boundedSatisfaction, HierarchySymbol.Semiformula.val_sigma,
        (IsBounded.defined (V := V)).df, (IsUFormula.defined (V := V) (L := ℒₒᵣ)).df,
        (BoundedSatisfactionTable.defined (V := V)).df,
          BoundedSatisfactionTableF.nodeVal_defined.df] using this;
    exact fun hz hz' ↦ exists_iff_forall hz hz';
  · intro v;
    simp [boundedSatisfaction, HierarchySymbol.Semiformula.val_sigma,
      iff_exists,
      (IsBounded.defined (V := V)).df, (IsUFormula.defined (V := V) (L := ℒₒᵣ)).df,
      (BoundedSatisfactionTable.defined (V := V)).df, BoundedSatisfactionTableF.nodeVal_defined.df];

instance BoundedSatisfaction.definable : 𝚫ᴬ₁-Relation (BoundedSatisfaction : V → V → Prop) :=
  BoundedSatisfaction.defined.to_definable

/-! ### Tarski conditions -/

namespace BoundedSatisfaction

lemma dom {z e : V} (h : BoundedSatisfaction z e) : IsBounded z ∧ IsUFormula ℒₒᵣ z :=
  ⟨h.isBounded, h.isUFormula⟩

@[simp] lemma verum (e : V) : BoundedSatisfaction (^⊤ : V) e := by
  obtain ⟨r, hr⟩ := BoundedSatisfactionTable.exists (z := (^⊤ : V)) (e := e) (by simp) (by simp);
  exact ⟨by simp, by simp, r, hr, hr.val_verum hr.mem_dom_root⟩;

@[simp] lemma falsum (e : V) : ¬BoundedSatisfaction (^⊥ : V) e := by
  rintro ⟨-, -, r, hr, h1⟩;
  exact hr.val_one_ne_zero h1 (hr.val_falsum hr.mem_dom_root);

section
variable {t u e : V} (ht : IsUTerm ℒₒᵣ t) (hu : IsUTerm ℒₒᵣ u)
include ht hu

@[simp] lemma eq_iff : BoundedSatisfaction (t ^= u) e ↔ termVal e t = termVal e u := by
  have hd : IsBounded (t ^= u) := by simp [Arithmetic.qqEQ];
  have hf : IsUFormula ℒₒᵣ (t ^= u) := by simp [Arithmetic.qqEQ, ht, hu];
  obtain ⟨r, hr⟩ := BoundedSatisfactionTable.exists hd hf;
  rw [iff_val hd hf hr];
  exact hr.val_eq hr.mem_dom_root;

@[simp] lemma neq_iff : BoundedSatisfaction (t ^≠ u) e ↔ termVal e t ≠ termVal e u := by
  have hd : IsBounded (t ^≠ u) := by simp [Arithmetic.qqNEQ];
  have hf : IsUFormula ℒₒᵣ (t ^≠ u) := by simp [Arithmetic.qqNEQ, ht, hu];
  obtain ⟨r, hr⟩ := BoundedSatisfactionTable.exists hd hf;
  rw [iff_val hd hf hr];
  exact hr.val_neq hr.mem_dom_root;

@[simp] lemma lt_iff : BoundedSatisfaction (t ^< u) e ↔ termVal e t < termVal e u := by
  have hd : IsBounded (t ^< u) := by simp [Arithmetic.qqLT];
  have hf : IsUFormula ℒₒᵣ (t ^< u) := by simp [Arithmetic.qqLT, ht, hu];
  obtain ⟨r, hr⟩ := BoundedSatisfactionTable.exists hd hf;
  rw [iff_val hd hf hr];
  exact hr.val_lt hr.mem_dom_root;

@[simp] lemma nlt_iff : BoundedSatisfaction (t ^≮ u) e ↔ ¬(termVal e t < termVal e u) := by
  have hd : IsBounded (t ^≮ u : V) := by simp [Arithmetic.qqNLT];
  have hf : IsUFormula ℒₒᵣ (t ^≮ u : V) := by simp [Arithmetic.qqNLT, ht, hu];
  obtain ⟨r, hr⟩ := BoundedSatisfactionTable.exists hd hf;
  rw [iff_val hd hf hr];
  exact hr.val_nlt hr.mem_dom_root;

end

@[simp] lemma and_iff {p q e : V} :
    BoundedSatisfaction (p ^⋏ q) e ↔ BoundedSatisfaction p e ∧ BoundedSatisfaction q e := by
  constructor;
  · rintro ⟨hd, hf, r, hr, h1⟩;
    obtain ⟨hdp, hdq⟩ := IsBounded.and_iff.mp hd;
    obtain ⟨hfp, hfq⟩ := IsUFormula.and.mp hf;
    obtain ⟨hn₁, hn₂⟩ := hr.mem_dom_and hr.mem_dom_root;
    obtain ⟨v₁, v₂⟩ := (hr.val_and hr.mem_dom_root).mp h1;
    exact ⟨(iff_mem hr hn₁ hdp hfp).mpr v₁, (iff_mem hr hn₂ hdq hfq).mpr v₂⟩;
  · rintro ⟨h₁, h₂⟩;
    obtain ⟨hdp, hfp⟩ := h₁.dom;
    obtain ⟨hdq, hfq⟩ := h₂.dom;
    have hd : IsBounded (p ^⋏ q) := IsBounded.and_iff.mpr ⟨hdp, hdq⟩;
    have hf : IsUFormula ℒₒᵣ (p ^⋏ q) := by simp [hfp, hfq];
    obtain ⟨r, hr⟩ := BoundedSatisfactionTable.exists hd hf;
    obtain ⟨hn₁, hn₂⟩ := hr.mem_dom_and hr.mem_dom_root;
    exact (iff_val hd hf hr).mpr ((hr.val_and hr.mem_dom_root).mpr
      ⟨(iff_mem hr hn₁ hdp hfp).mp h₁, (iff_mem hr hn₂ hdq hfq).mp h₂⟩);

@[simp] lemma or_iff {p q e : V} (hdp : IsBounded p) (hfp : IsUFormula ℒₒᵣ p)
    (hdq : IsBounded q) (hfq : IsUFormula ℒₒᵣ q) :
    BoundedSatisfaction (p ^⋎ q) e ↔ BoundedSatisfaction p e ∨ BoundedSatisfaction q e := by
  constructor;
  · rintro ⟨-, -, r, hr, h1⟩;
    obtain ⟨hn₁, hn₂⟩ := hr.mem_dom_or hr.mem_dom_root;
    rcases (hr.val_or hr.mem_dom_root).mp h1 with v | v;
    · left; exact (iff_mem hr hn₁ hdp hfp).mpr v;
    · right; exact (iff_mem hr hn₂ hdq hfq).mpr v;
  · intro h;
    have hd : IsBounded (p ^⋎ q) := IsBounded.or_iff.mpr ⟨hdp, hdq⟩;
    have hf : IsUFormula ℒₒᵣ (p ^⋎ q) := by simp [hfp, hfq];
    obtain ⟨r, hr⟩ := BoundedSatisfactionTable.exists hd hf;
    obtain ⟨hn₁, hn₂⟩ := hr.mem_dom_or hr.mem_dom_root;
    apply (iff_val hd hf hr).mpr;
    apply (hr.val_or hr.mem_dom_root).mpr;
    rcases h with h | h;
    · left; exact (iff_mem hr hn₁ hdp hfp).mp h;
    · right; exact (iff_mem hr hn₂ hdq hfq).mp h;

section
variable {t q e : V} (ht : IsUTerm ℒₒᵣ t)
include ht

@[simp] lemma ball_iff (hq : IsBounded q) (hq' : IsUFormula ℒₒᵣ q) :
    BoundedSatisfaction (qqBall (termBShift ℒₒᵣ t) q) e ↔
      ∀ x < termVal e t, BoundedSatisfaction q (x ∷ e) := by
  have hd : IsBounded (qqBall (termBShift ℒₒᵣ t) q) := IsBounded.ball ht hq;
  have hf : IsUFormula ℒₒᵣ (qqBall (termBShift ℒₒᵣ t) q) := by
    simp [qqBall, Arithmetic.qqNLT, ht.termBShift, hq'];
  obtain ⟨r, hr⟩ := BoundedSatisfactionTable.exists hd hf;
  rw [iff_val hd hf hr, hr.val_ball ht hr.mem_dom_root];
  exact forall_congr' fun x ↦ imp_congr_right fun hx ↦
    (iff_mem hr (hr.mem_dom_ball ht hr.mem_dom_root hx) hq hq').symm;

@[simp] lemma bex_iff :
    BoundedSatisfaction (qqBex (termBShift ℒₒᵣ t) q) e ↔
      ∃ x < termVal e t, BoundedSatisfaction q (x ∷ e) := by
  constructor;
  · rintro ⟨hd, hf, r, hr, h1⟩;
    have hq : IsBounded q := hd.of_qqBex;
    have hq' : IsUFormula ℒₒᵣ q := by
      simpa [qqBex, Arithmetic.qqLT, ht.termBShift] using hf;
    obtain ⟨x, hx, v⟩ := (hr.val_bex ht hr.mem_dom_root).mp h1;
    exact ⟨x, hx, (iff_mem hr (hr.mem_dom_bex ht hr.mem_dom_root hx) hq hq').mpr v⟩;
  · rintro ⟨x, hx, hsat⟩;
    obtain ⟨hq, hq'⟩ := hsat.dom;
    have hd : IsBounded (qqBex (termBShift ℒₒᵣ t) q) := IsBounded.bex ht hq;
    have hf : IsUFormula ℒₒᵣ (qqBex (termBShift ℒₒᵣ t) q) := by
      simp [qqBex, Arithmetic.qqLT, ht.termBShift, hq'];
    obtain ⟨r, hr⟩ := BoundedSatisfactionTable.exists hd hf;
    exact (iff_val hd hf hr).mpr
      ((hr.val_bex ht hr.mem_dom_root).mpr
        ⟨x, hx, (iff_mem hr (hr.mem_dom_bex ht hr.mem_dom_root hx) hq hq').mp hsat⟩);

end

lemma neg_iff {p e : V} (hp : IsBounded p) (hp' : IsUFormula ℒₒᵣ p) :
    BoundedSatisfaction (neg ℒₒᵣ p) e ↔ ¬BoundedSatisfaction p e := by
  have H : ∀ p : V, IsBounded p → IsUFormula ℒₒᵣ p →
      ∀ e, (BoundedSatisfaction (neg ℒₒᵣ p) e ↔ ¬BoundedSatisfaction p e) := by
    apply IsBounded.induction 𝚷
      (P := fun p ↦ IsUFormula ℒₒᵣ p →
        ∀ e, (BoundedSatisfaction (neg ℒₒᵣ p) e ↔ ¬BoundedSatisfaction p e));
    · definability;
    · intro _ e; simp;
    · intro _ e; simp;
    · intro k r v h e;
      rcases rel_cases h with ⟨t, u, ht, hu, heq⟩ | ⟨t, u, ht, hu, heq⟩;
      · rw [heq, Arithmetic.neg_eq ht hu, neq_iff ht hu, eq_iff ht hu];
      · rw [heq, Arithmetic.neg_lt ht hu, nlt_iff ht hu, lt_iff ht hu];
    · intro k r v h e;
      rcases nrel_cases h with ⟨t, u, ht, hu, heq⟩ | ⟨t, u, ht, hu, heq⟩;
      · rw [heq, Arithmetic.neg_neq ht hu, eq_iff ht hu, neq_iff ht hu]; simp;
      · rw [heq, Arithmetic.neg_nlt ht hu, lt_iff ht hu, nlt_iff ht hu]; simp;
    · intro p q hdp hdq ihp ihq h e;
      obtain ⟨hfp, hfq⟩ := IsUFormula.and.mp h;
      rw [neg_and hfp hfq, or_iff (IsBounded.neg hfp hdp) hfp.neg (IsBounded.neg hfq hdq) hfq.neg,
        ihp hfp e, ihq hfq e, and_iff];
      tauto;
    · intro p q hdp hdq ihp ihq h e;
      obtain ⟨hfp, hfq⟩ := IsUFormula.or.mp h;
      rw [neg_or hfp hfq, and_iff, ihp hfp e, ihq hfq e, or_iff hdp hfp hdq hfq];
      tauto;
    · intro t q ht hdq ih h e;
      obtain ⟨-, hfq⟩ : IsUTerm ℒₒᵣ (termBShift ℒₒᵣ t) ∧ IsUFormula ℒₒᵣ q := by
        simpa [qqBall, Arithmetic.qqNLT] using h;
      rw [neg_qqBall ht.termBShift hfq, bex_iff ht, ball_iff ht hdq hfq];
      constructor;
      · rintro ⟨x, hx, hnx⟩ hall;
        exact (ih hfq (x ∷ e)).mp hnx (hall x hx);
      · intro hn;
        by_contra hc;
        exact hn fun x hx ↦ by
          by_contra hnx;
          exact hc ⟨x, hx, (ih hfq (x ∷ e)).mpr hnx⟩;
    · intro t q ht hdq ih h e;
      obtain ⟨-, hfq⟩ : IsUTerm ℒₒᵣ (termBShift ℒₒᵣ t) ∧ IsUFormula ℒₒᵣ q := by
        simpa [qqBex, Arithmetic.qqLT] using h;
      rw [neg_qqBex ht.termBShift hfq, ball_iff ht (IsBounded.neg hfq hdq) hfq.neg, bex_iff ht];
      constructor;
      · rintro hall ⟨x, hx, hx'⟩;
        exact (ih hfq (x ∷ e)).mp (hall x hx) hx';
      · intro hn x hx;
        exact (ih hfq (x ∷ e)).mpr fun hc ↦ hn ⟨x, hx, hc⟩;
  exact H p hp hp' e;

lemma subst {n m w p e : V} (hw : IsSemitermVec ℒₒᵣ n m w)
    (hp : IsSemiformula ℒₒᵣ n p) (hp' : IsBounded p) :
    BoundedSatisfaction (Bootstrapping.subst ℒₒᵣ w p) e ↔
      BoundedSatisfaction p (termValVec e n w) := by
  have H : ∀ p : V, IsBounded p → ∀ n m w e, IsSemitermVec ℒₒᵣ n m w → IsSemiformula ℒₒᵣ n p →
      (BoundedSatisfaction (Bootstrapping.subst ℒₒᵣ w p) e ↔
        BoundedSatisfaction p (termValVec e n w)) := by
    apply IsBounded.induction 𝚷
      (P := fun p ↦ ∀ n m w e, IsSemitermVec ℒₒᵣ n m w → IsSemiformula ℒₒᵣ n p →
        (BoundedSatisfaction (Bootstrapping.subst ℒₒᵣ w p) e ↔
          BoundedSatisfaction p (termValVec e n w)));
    · definability;
    · intro n m w e _ _; simp;
    · intro n m w e _ _; simp;
    · intro k r v n m w e hw hp;
      rcases rel_cases hp.isUFormula with ⟨t, u, ht, hu, heq⟩ | ⟨t, u, ht, hu, heq⟩;
      · rw [heq] at hp ⊢;
        obtain ⟨hts, hus⟩ : IsSemiterm ℒₒᵣ n t ∧ IsSemiterm ℒₒᵣ n u := by
          simpa [Arithmetic.qqEQ] using hp;
        rw [substs_qqEQ ht hu, eq_iff (hw.termSubst hts).isUTerm (hw.termSubst hus).isUTerm,
          eq_iff ht hu,
          termVal_termSubst hw hts, termVal_termSubst hw hus];
      · rw [heq] at hp ⊢;
        obtain ⟨hts, hus⟩ : IsSemiterm ℒₒᵣ n t ∧ IsSemiterm ℒₒᵣ n u := by
          simpa [Arithmetic.qqLT] using hp;
        rw [substs_qqLT ht hu, lt_iff (hw.termSubst hts).isUTerm (hw.termSubst hus).isUTerm,
          lt_iff ht hu,
          termVal_termSubst hw hts, termVal_termSubst hw hus];
    · intro k r v n m w e hw hp;
      rcases nrel_cases hp.isUFormula with ⟨t, u, ht, hu, heq⟩ | ⟨t, u, ht, hu, heq⟩;
      · rw [heq] at hp ⊢;
        obtain ⟨hts, hus⟩ : IsSemiterm ℒₒᵣ n t ∧ IsSemiterm ℒₒᵣ n u := by
          simpa [Arithmetic.qqNEQ] using hp;
        rw [substs_qqNEQ ht hu, neq_iff (hw.termSubst hts).isUTerm (hw.termSubst hus).isUTerm,
          neq_iff ht hu,
          termVal_termSubst hw hts, termVal_termSubst hw hus];
      · rw [heq] at hp ⊢;
        obtain ⟨hts, hus⟩ : IsSemiterm ℒₒᵣ n t ∧ IsSemiterm ℒₒᵣ n u := by
          simpa [Arithmetic.qqNLT] using hp;
        rw [substs_qqNLT ht hu, nlt_iff (hw.termSubst hts).isUTerm (hw.termSubst hus).isUTerm,
          nlt_iff ht hu,
          termVal_termSubst hw hts, termVal_termSubst hw hus];
    · intro p q _ _ ihp ihq n m w e hw hpq;
      obtain ⟨hp, hq⟩ := IsSemiformula.and.mp hpq;
      rw [substs_and hp.isUFormula hq.isUFormula, and_iff, and_iff, ihp n m w e hw hp,
        ihq n m w e hw hq];
    · intro p q hdp hdq ihp ihq n m w e hw hpq;
      obtain ⟨hp, hq⟩ := IsSemiformula.or.mp hpq;
      rw [substs_or hp.isUFormula hq.isUFormula,
        or_iff (IsBounded.subst hw hp hdp) (hp.subst hw).isUFormula
          (IsBounded.subst hw hq hdq) (hq.subst hw).isUFormula,
        or_iff hdp hp.isUFormula hdq hq.isUFormula,
        ihp n m w e hw hp, ihq n m w e hw hq];
    · intro t q ht hdq ih n m w e hw hpq;
      obtain ⟨hts, hq⟩ := isSemiformula_qqBall ht hpq;
      rw [substs_qqBall hw hts hq.isUFormula,
        ball_iff (hw.termSubst hts).isUTerm (IsBounded.subst hw.qVec hq hdq)
          (hq.subst hw.qVec).isUFormula,
        ball_iff ht hdq hq.isUFormula, termVal_termSubst hw hts];
      apply forall₂_congr;
      intro x _;
      rw [ih (n + 1) (m + 1) (qVec ℒₒᵣ w) (x ∷ e) hw.qVec hq, termValVec_qVec hw];
    · intro t q ht hdq ih n m w e hw hpq;
      obtain ⟨hts, hq⟩ := isSemiformula_qqBex ht hpq;
      rw [substs_qqBex hw hts hq.isUFormula, bex_iff (hw.termSubst hts).isUTerm, bex_iff ht,
        termVal_termSubst hw hts];
      apply exists_congr;
      intro x;
      apply and_congr_right;
      intro _;
      rw [ih (n + 1) (m + 1) (qVec ℒₒᵣ w) (x ∷ e) hw.qVec hq, termValVec_qVec hw];
  exact H p hp' n m w e hw hp;

end BoundedSatisfaction

end satisfaction

end FFL.FirstOrder.Arithmetic.Bootstrapping
