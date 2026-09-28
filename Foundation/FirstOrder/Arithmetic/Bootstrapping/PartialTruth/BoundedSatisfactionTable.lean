module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Formula.Bounded
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.PartialTruth.TermVal

/-!
# Satisfaction tables for $\Delta_0$ formulas

`BoundedSatisfactionTable q z e` says that `q` is a finite satisfaction table for the coded
$\Delta_0$ formula `z` under the assignment `e`: a finite mapping from nodes `⟪p, e'⟫` to values
`0`, `1` that obeys a Tarski clause at every node of its domain and whose nodes all descend from
the root `⟪z, e⟫`. Two tables agree on every node common to their domains, a table for a fixed root
is unique, and the relation is $\Delta_1$-definable.

## References

- [HP98, Definition I.1.71(1), Lemma I.1.72(1), Lemma I.1.72(2)]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL.FirstOrder.Bounding (HierarchySymbol)

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## The satisfaction table -/

section table

open Arithmetic (qqEQ qqNEQ qqLT qqNLT qqEQ_defined qqNEQ_defined qqLT_defined qqNLT_defined)

/-! ### Bounds on the nodes of a finite mapping -/

lemma lt_of_mem_domain {n q : V} (h : n ∈ domain q) : n < q := by
  obtain ⟨y, hy⟩ := mem_domain_iff.mp h;
  exact lt_of_mem_dom hy;

lemma fst_lt_of_mem_domain {p e q : V} (h : ⟪p, e⟫ ∈ domain q) : p < q :=
  lt_of_le_of_lt (le_pair_left p e) (lt_of_mem_domain h)

lemma snd_lt_of_mem_domain {p e q : V} (h : ⟪p, e⟫ ∈ domain q) : e < q :=
  lt_of_le_of_lt (le_pair_right p e) (lt_of_mem_domain h)

section coding

-- Unfolding these coding operations to their underlying pairs, together with the default simp
-- set (numeral facts, `pair_ext_iff`), is exactly what is needed to tell two differently-shaped
-- coded formulas apart when reading `spec` off at a node. Scoped to this section, since
-- unconditionally unfolding these constructors defeats the ordinary simp set on coded formulas.
attribute [local simp] qqAnd qqOr qqVerum qqFalsum qqRel qqNRel qqBall qqAll qqBex qqExs
  qqEQ qqNEQ qqLT qqNLT

/-! ### Coding injectivity facts for the bounded quantifiers -/

@[simp] lemma qqBall_inj {u₁ q₁ u₂ q₂ : V} : qqBall u₁ q₁ = qqBall u₂ q₂ ↔ u₁ = u₂ ∧ q₁ = q₂ := by
  simp [qqBall, qqNLT, qqNRel, adjoin_inj];

@[simp] lemma qqBex_inj {u₁ q₁ u₂ q₂ : V} : qqBex u₁ q₁ = qqBex u₂ q₂ ↔ u₁ = u₂ ∧ q₁ = q₂ := by
  simp [qqBex, qqLT, qqRel, adjoin_inj];

@[simp] lemma qqEQ_inj {t₁ u₁ t₂ u₂ : V} : t₁ ^= u₁ = t₂ ^= u₂ ↔ t₁ = t₂ ∧ u₁ = u₂ := by
  simp [qqEQ, qqRel, adjoin_inj];

@[simp] lemma qqNEQ_inj {t₁ u₁ t₂ u₂ : V} : t₁ ^≠ u₁ = t₂ ^≠ u₂ ↔ t₁ = t₂ ∧ u₁ = u₂ := by
  simp [qqNEQ, qqNRel, adjoin_inj];

@[simp] lemma qqLT_inj {t₁ u₁ t₂ u₂ : V} : t₁ ^< u₁ = t₂ ^< u₂ ↔ t₁ = t₂ ∧ u₁ = u₂ := by
  simp [qqLT, qqRel, adjoin_inj];

@[simp] lemma qqNLT_inj {t₁ u₁ t₂ u₂ : V} : t₁ ^≮ u₁ = t₂ ^≮ u₂ ↔ t₁ = t₂ ∧ u₁ = u₂ := by
  simp [qqNLT, qqNRel, adjoin_inj];

@[simp] lemma coe_eqIndex_eq : (Arithmetic.eqIndex : V) = 0 := rfl

@[simp] lemma coe_ltIndex_eq : (Arithmetic.ltIndex : V) = 1 := by simp [Arithmetic.ltIndex]; rfl

lemma eqIndex_ne_ltIndex : (Arithmetic.eqIndex : V) ≠ (Arithmetic.ltIndex : V) := by simp

/-! ### The partial satisfaction table -/

structure BoundedSatisfactionTable (q z e : V) : Prop where
  isMapping : IsMapping q
  mem_dom_root : ⟪z, e⟫ ∈ domain q
  spec : ∀ z' e', ⟪z', e'⟫ ∈ domain q → (z' = ^⊤ ∧ ⟪⟪z', e'⟫, 1⟫ ∈ q) ∨
    (z' = ^⊥ ∧ ⟪⟪z', e'⟫, 0⟫ ∈ q) ∨
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
  minimal : ∀ n ∈ domain q, n = ⟪z, e⟫ ∨
    (∃ p₁ p₂ e', ⟪p₁ ^⋏ p₂, e'⟫ ∈ domain q ∧ (n = ⟪p₁, e'⟫ ∨ n = ⟪p₂, e'⟫)) ∨
    (∃ p₁ p₂ e', ⟪p₁ ^⋎ p₂, e'⟫ ∈ domain q ∧ (n = ⟪p₁, e'⟫ ∨ n = ⟪p₂, e'⟫)) ∨
    (∃ u p e', ⟪qqBall u p, e'⟫ ∈ domain q ∧ ∃ x < termVal (0 ∷ e') u, n = ⟪p, x ∷ e'⟫) ∨
    (∃ u p e', ⟪qqBex u p, e'⟫ ∈ domain q ∧ ∃ x < termVal (0 ∷ e') u, n = ⟪p, x ∷ e'⟫)

namespace BoundedSatisfactionTable

variable {q z e z' e' t u p p₁ p₂ : V}

/-! ### Reading `spec` off at a node of known shape -/

lemma val_verum (h : BoundedSatisfactionTable q z e) (hn : ⟪(^⊤ : V), e'⟫ ∈ domain q) :
    ⟪⟪(^⊤ : V), e'⟫, 1⟫ ∈ q := by
  simpa using h.spec _ e' hn;

lemma val_falsum (h : BoundedSatisfactionTable q z e) (hn : ⟪(^⊥ : V), e'⟫ ∈ domain q) :
    ⟪⟪(^⊥ : V), e'⟫, 0⟫ ∈ q := by
  simpa using h.spec _ e' hn;

lemma spec_eq (h : BoundedSatisfactionTable q z e) (hn : ⟪t ^= u, e'⟫ ∈ domain q) :
    (⟪⟪t ^= u, e'⟫, 1⟫ ∈ q ↔ termVal e' t = termVal e' u) ∧
    (⟪⟪t ^= u, e'⟫, 0⟫ ∈ q ↔ termVal e' t ≠ termVal e' u) := by
  have h₁ := h.spec _ e' hn;
  simp_all;

lemma spec_neq (h : BoundedSatisfactionTable q z e) (hn : ⟪t ^≠ u, e'⟫ ∈ domain q) :
    (⟪⟪t ^≠ u, e'⟫, 1⟫ ∈ q ↔ termVal e' t ≠ termVal e' u) ∧
    (⟪⟪t ^≠ u, e'⟫, 0⟫ ∈ q ↔ termVal e' t = termVal e' u) := by
  have h₁ := h.spec _ e' hn;
  simp_all;

lemma spec_lt (h : BoundedSatisfactionTable q z e) (hn : ⟪t ^< u, e'⟫ ∈ domain q) :
    (⟪⟪t ^< u, e'⟫, 1⟫ ∈ q ↔ termVal e' t < termVal e' u) ∧
    (⟪⟪t ^< u, e'⟫, 0⟫ ∈ q ↔ ¬termVal e' t < termVal e' u) := by
  have h₁ := h.spec _ e' hn;
  simp_all;

lemma spec_nlt (h : BoundedSatisfactionTable q z e) (hn : ⟪t ^≮ u, e'⟫ ∈ domain q) :
    (⟪⟪t ^≮ u, e'⟫, 1⟫ ∈ q ↔ ¬termVal e' t < termVal e' u) ∧
    (⟪⟪t ^≮ u, e'⟫, 0⟫ ∈ q ↔ termVal e' t < termVal e' u) := by
  have h₁ := h.spec _ e' hn;
  simp_all;

lemma spec_and (h : BoundedSatisfactionTable q z e) (hn : ⟪p₁ ^⋏ p₂, e'⟫ ∈ domain q) :
    ⟪p₁, e'⟫ ∈ domain q ∧ ⟪p₂, e'⟫ ∈ domain q ∧
    (⟪⟪p₁ ^⋏ p₂, e'⟫, 1⟫ ∈ q ↔ ⟪⟪p₁, e'⟫, 1⟫ ∈ q ∧ ⟪⟪p₂, e'⟫, 1⟫ ∈ q) ∧
    (⟪⟪p₁ ^⋏ p₂, e'⟫, 0⟫ ∈ q ↔ ⟪⟪p₁, e'⟫, 0⟫ ∈ q ∨ ⟪⟪p₂, e'⟫, 0⟫ ∈ q) := by
  simpa using h.spec _ e' hn;

lemma spec_or (h : BoundedSatisfactionTable q z e) (hn : ⟪p₁ ^⋎ p₂, e'⟫ ∈ domain q) :
    ⟪p₁, e'⟫ ∈ domain q ∧ ⟪p₂, e'⟫ ∈ domain q ∧
    (⟪⟪p₁ ^⋎ p₂, e'⟫, 1⟫ ∈ q ↔ ⟪⟪p₁, e'⟫, 1⟫ ∈ q ∨ ⟪⟪p₂, e'⟫, 1⟫ ∈ q) ∧
    (⟪⟪p₁ ^⋎ p₂, e'⟫, 0⟫ ∈ q ↔ ⟪⟪p₁, e'⟫, 0⟫ ∈ q ∧ ⟪⟪p₂, e'⟫, 0⟫ ∈ q) := by
  simpa using h.spec _ e' hn;

lemma spec_ball (h : BoundedSatisfactionTable q z e) (hn : ⟪qqBall u p, e'⟫ ∈ domain q) :
    (∃ t, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧
    (∀ x < termVal (0 ∷ e') u, ⟪p, x ∷ e'⟫ ∈ domain q) ∧
    (⟪⟪qqBall u p, e'⟫, 1⟫ ∈ q ↔ ∀ x < termVal (0 ∷ e') u, ⟪⟪p, x ∷ e'⟫, 1⟫ ∈ q) ∧
    (⟪⟪qqBall u p, e'⟫, 0⟫ ∈ q ↔ ∃ x < termVal (0 ∷ e') u, ⟪⟪p, x ∷ e'⟫, 0⟫ ∈ q) := by
  obtain ⟨t, ht, rfl, hd, hA, hB⟩ :
      ∃ t, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t ∧
        (∀ x < termVal (0 ∷ e') (termBShift ℒₒᵣ t), ⟪p, x ∷ e'⟫ ∈ domain q) ∧
        (⟪⟪qqBall u p, e'⟫, 1⟫ ∈ q ↔
          ∀ x < termVal (0 ∷ e') (termBShift ℒₒᵣ t), ⟪⟪p, x ∷ e'⟫, 1⟫ ∈ q) ∧
        (⟪⟪qqBall u p, e'⟫, 0⟫ ∈ q ↔
          ∃ x < termVal (0 ∷ e') (termBShift ℒₒᵣ t), ⟪⟪p, x ∷ e'⟫, 0⟫ ∈ q) := by
    simpa using h.spec _ e' hn;
  exact ⟨⟨t, ht, rfl⟩, hd, hA, hB⟩;

lemma spec_bex (h : BoundedSatisfactionTable q z e) (hn : ⟪qqBex u p, e'⟫ ∈ domain q) :
    (∃ t, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧
    (∀ x < termVal (0 ∷ e') u, ⟪p, x ∷ e'⟫ ∈ domain q) ∧
    (⟪⟪qqBex u p, e'⟫, 1⟫ ∈ q ↔ ∃ x < termVal (0 ∷ e') u, ⟪⟪p, x ∷ e'⟫, 1⟫ ∈ q) ∧
    (⟪⟪qqBex u p, e'⟫, 0⟫ ∈ q ↔ ∀ x < termVal (0 ∷ e') u, ⟪⟪p, x ∷ e'⟫, 0⟫ ∈ q) := by
  obtain ⟨t, ht, rfl, hd, hA, hB⟩ :
      ∃ t, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t ∧
        (∀ x < termVal (0 ∷ e') (termBShift ℒₒᵣ t), ⟪p, x ∷ e'⟫ ∈ domain q) ∧
        (⟪⟪qqBex u p, e'⟫, 1⟫ ∈ q ↔
          ∃ x < termVal (0 ∷ e') (termBShift ℒₒᵣ t), ⟪⟪p, x ∷ e'⟫, 1⟫ ∈ q) ∧
        (⟪⟪qqBex u p, e'⟫, 0⟫ ∈ q ↔
          ∀ x < termVal (0 ∷ e') (termBShift ℒₒᵣ t), ⟪⟪p, x ∷ e'⟫, 0⟫ ∈ q) := by
    simpa using h.spec _ e' hn;
  exact ⟨⟨t, ht, rfl⟩, hd, hA, hB⟩;

/-! ### The Tarski clauses in the form the satisfaction predicate uses -/

lemma val_eq (h : BoundedSatisfactionTable q z e) (hn : ⟪t ^= u, e'⟫ ∈ domain q) :
    ⟪⟪t ^= u, e'⟫, 1⟫ ∈ q ↔ termVal e' t = termVal e' u := (h.spec_eq hn).1

lemma val_neq (h : BoundedSatisfactionTable q z e) (hn : ⟪t ^≠ u, e'⟫ ∈ domain q) :
    ⟪⟪t ^≠ u, e'⟫, 1⟫ ∈ q ↔ termVal e' t ≠ termVal e' u := (h.spec_neq hn).1

lemma val_lt (h : BoundedSatisfactionTable q z e) (hn : ⟪t ^< u, e'⟫ ∈ domain q) :
    ⟪⟪t ^< u, e'⟫, 1⟫ ∈ q ↔ termVal e' t < termVal e' u := (h.spec_lt hn).1

lemma val_nlt (h : BoundedSatisfactionTable q z e) (hn : ⟪t ^≮ u, e'⟫ ∈ domain q) :
    ⟪⟪t ^≮ u, e'⟫, 1⟫ ∈ q ↔ ¬termVal e' t < termVal e' u := (h.spec_nlt hn).1

lemma mem_dom_and (h : BoundedSatisfactionTable q z e) (hn : ⟪p₁ ^⋏ p₂, e'⟫ ∈ domain q) :
    ⟪p₁, e'⟫ ∈ domain q ∧ ⟪p₂, e'⟫ ∈ domain q :=
  ⟨(h.spec_and hn).1, (h.spec_and hn).2.1⟩

lemma val_and (h : BoundedSatisfactionTable q z e) (hn : ⟪p₁ ^⋏ p₂, e'⟫ ∈ domain q) :
    ⟪⟪p₁ ^⋏ p₂, e'⟫, 1⟫ ∈ q ↔ ⟪⟪p₁, e'⟫, 1⟫ ∈ q ∧ ⟪⟪p₂, e'⟫, 1⟫ ∈ q := (h.spec_and hn).2.2.1

lemma mem_dom_or (h : BoundedSatisfactionTable q z e) (hn : ⟪p₁ ^⋎ p₂, e'⟫ ∈ domain q) :
    ⟪p₁, e'⟫ ∈ domain q ∧ ⟪p₂, e'⟫ ∈ domain q :=
  ⟨(h.spec_or hn).1, (h.spec_or hn).2.1⟩

lemma val_or (h : BoundedSatisfactionTable q z e) (hn : ⟪p₁ ^⋎ p₂, e'⟫ ∈ domain q) :
    ⟪⟪p₁ ^⋎ p₂, e'⟫, 1⟫ ∈ q ↔ ⟪⟪p₁, e'⟫, 1⟫ ∈ q ∨ ⟪⟪p₂, e'⟫, 1⟫ ∈ q := (h.spec_or hn).2.2.1

lemma mem_dom_ball (h : BoundedSatisfactionTable q z e) (ht : IsUTerm ℒₒᵣ t)
    (hn : ⟪qqBall (termBShift ℒₒᵣ t) p, e'⟫ ∈ domain q) {x : V} (hx : x < termVal e' t) :
    ⟪p, x ∷ e'⟫ ∈ domain q :=
  (h.spec_ball hn).2.1 x (by rwa [termVal_termBShift ht])

lemma val_ball (h : BoundedSatisfactionTable q z e) (ht : IsUTerm ℒₒᵣ t)
    (hn : ⟪qqBall (termBShift ℒₒᵣ t) p, e'⟫ ∈ domain q) :
    ⟪⟪qqBall (termBShift ℒₒᵣ t) p, e'⟫, 1⟫ ∈ q ↔ ∀ x < termVal e' t, ⟪⟪p, x ∷ e'⟫, 1⟫ ∈ q := by
  have := (h.spec_ball hn).2.2.1;
  rwa [termVal_termBShift ht] at this;

lemma mem_dom_bex (h : BoundedSatisfactionTable q z e) (ht : IsUTerm ℒₒᵣ t)
    (hn : ⟪qqBex (termBShift ℒₒᵣ t) p, e'⟫ ∈ domain q) {x : V} (hx : x < termVal e' t) :
    ⟪p, x ∷ e'⟫ ∈ domain q :=
  (h.spec_bex hn).2.1 x (by rwa [termVal_termBShift ht])

lemma val_bex (h : BoundedSatisfactionTable q z e) (ht : IsUTerm ℒₒᵣ t)
    (hn : ⟪qqBex (termBShift ℒₒᵣ t) p, e'⟫ ∈ domain q) :
    ⟪⟪qqBex (termBShift ℒₒᵣ t) p, e'⟫, 1⟫ ∈ q ↔ ∃ x < termVal e' t, ⟪⟪p, x ∷ e'⟫, 1⟫ ∈ q := by
  have := (h.spec_bex hn).2.2.1;
  rwa [termVal_termBShift ht] at this;

end BoundedSatisfactionTable

end coding

namespace BoundedSatisfactionTable

variable {q q₁ q₂ z z₁ z₂ e e₁ e₂ p : V}

/-! ### Uniqueness -/

lemma val_one_ne_zero (h : BoundedSatisfactionTable q z e) {n : V} (h1 : ⟪n, 1⟫ ∈ q)
    (h0 : ⟪n, 0⟫ ∈ q) : False := by
  simpa using h.isMapping.uniq h1 h0;

lemma val_zero_or_one (h : BoundedSatisfactionTable q z e) :
    ∀ p e', ⟪p, e'⟫ ∈ domain q → ⟪⟪p, e'⟫, 1⟫ ∈ q ∨ ⟪⟪p, e'⟫, 0⟫ ∈ q := by
  apply ISigma1.pi1_order_induction
    (P := fun p ↦ ∀ e', ⟪p, e'⟫ ∈ domain q → ⟪⟪p, e'⟫, 1⟫ ∈ q ∨ ⟪⟪p, e'⟫, 0⟫ ∈ q)
    (by definability);
  intro p ih e' hn;
  rcases h.spec _ e' hn with
    ⟨he, hv⟩ | ⟨he, hv⟩ |
    ⟨a, b, ha, hb, he, hA, hB⟩ | ⟨a, b, ha, hb, he, hA, hB⟩ |
    ⟨a, b, ha, hb, he, hA, hB⟩ | ⟨a, b, ha, hb, he, hA, hB⟩ |
    ⟨a, b, he, hd, hd', hA, hB⟩ | ⟨a, b, he, hd, hd', hA, hB⟩ |
    ⟨a, b, ht, he, hd, hA, hB⟩ | ⟨a, b, ht, he, hd, hA, hB⟩;
  · left; exact hv;
  · right; exact hv;
  · by_cases h' : termVal e' a = termVal e' b;
    · left; exact hA.mpr h';
    · right; exact hB.mpr h';
  · by_cases h' : termVal e' a = termVal e' b;
    · right; exact hB.mpr h';
    · left; exact hA.mpr h';
  · by_cases h' : termVal e' a < termVal e' b;
    · left; exact hA.mpr h';
    · right; exact hB.mpr h';
  · by_cases h' : termVal e' a < termVal e' b;
    · right; exact hB.mpr h';
    · left; exact hA.mpr h';
  · subst he;
    rcases ih a (by simp) e' hd with h1 | h1;
    · rcases ih b (by simp) e' hd' with h2 | h2;
      · left; exact hA.mpr ⟨h1, h2⟩;
      · right; apply hB.mpr; right; exact h2;
    · right; apply hB.mpr; left; exact h1;
  · subst he;
    rcases ih a (by simp) e' hd with h1 | h1;
    · left; apply hA.mpr; left; exact h1;
    · rcases ih b (by simp) e' hd' with h2 | h2;
      · left; apply hA.mpr; right; exact h2;
      · right; exact hB.mpr ⟨h1, h2⟩;
  · subst he;
    by_cases hall : ∀ x < termVal (0 ∷ e') a, ⟪⟪b, x ∷ e'⟫, 1⟫ ∈ q;
    · left; exact hA.mpr hall;
    · push Not at hall;
      obtain ⟨x, hx, hx1⟩ := hall;
      rcases ih b (by simp) (x ∷ e') (hd x hx) with h' | h';
      · exact absurd h' hx1;
      · right; exact hB.mpr ⟨x, hx, h'⟩;
  · subst he;
    by_cases hall : ∀ x < termVal (0 ∷ e') a, ⟪⟪b, x ∷ e'⟫, 0⟫ ∈ q;
    · right; exact hB.mpr hall;
    · push Not at hall;
      obtain ⟨x, hx, hx0⟩ := hall;
      rcases ih b (by simp) (x ∷ e') (hd x hx) with h' | h';
      · left; exact hA.mpr ⟨x, hx, h'⟩;
      · exact absurd h' hx0;

lemma agree (h₁ : BoundedSatisfactionTable q₁ z₁ e₁) (h₂ : BoundedSatisfactionTable q₂ z₂ e₂) :
    ∀ p e', ⟪p, e'⟫ ∈ domain q₁ → ⟪p, e'⟫ ∈ domain q₂ → (⟪⟪p, e'⟫, 1⟫ ∈ q₁ ↔ ⟪⟪p, e'⟫, 1⟫ ∈ q₂) ∧
      (⟪⟪p, e'⟫, 0⟫ ∈ q₁ ↔ ⟪⟪p, e'⟫, 0⟫ ∈ q₂) := by
  apply ISigma1.pi1_order_induction
    (P := fun p ↦ ∀ e', ⟪p, e'⟫ ∈ domain q₁ → ⟪p, e'⟫ ∈ domain q₂ →
      (⟪⟪p, e'⟫, 1⟫ ∈ q₁ ↔ ⟪⟪p, e'⟫, 1⟫ ∈ q₂) ∧
      (⟪⟪p, e'⟫, 0⟫ ∈ q₁ ↔ ⟪⟪p, e'⟫, 0⟫ ∈ q₂))
    (by definability);
  intro p ih e' hn₁ hn₂;
  rcases h₁.spec _ e' hn₁ with
    ⟨he, hv⟩ | ⟨he, hv⟩ |
    ⟨a, b, ha, hb, he, hA, hB⟩ | ⟨a, b, ha, hb, he, hA, hB⟩ |
    ⟨a, b, ha, hb, he, hA, hB⟩ | ⟨a, b, ha, hb, he, hA, hB⟩ |
    ⟨a, b, he, hd, hd', hA, hB⟩ | ⟨a, b, he, hd, hd', hA, hB⟩ |
    ⟨a, b, ht, he, hd, hA, hB⟩ | ⟨a, b, ht, he, hd, hA, hB⟩;
  · subst he;
    have hv₂ := h₂.val_verum hn₂;
    exact ⟨iff_of_true hv hv₂, iff_of_false (h₁.val_one_ne_zero hv) (h₂.val_one_ne_zero hv₂)⟩;
  · subst he;
    have hv₂ := h₂.val_falsum hn₂;
    exact ⟨iff_of_false (fun hc ↦ h₁.val_one_ne_zero hc hv) (fun hc ↦ h₂.val_one_ne_zero hc hv₂),
      iff_of_true hv hv₂⟩;
  · subst he;
    obtain ⟨hA₂, hB₂⟩ := h₂.spec_eq hn₂;
    exact ⟨hA.trans hA₂.symm, hB.trans hB₂.symm⟩;
  · subst he;
    obtain ⟨hA₂, hB₂⟩ := h₂.spec_neq hn₂;
    exact ⟨hA.trans hA₂.symm, hB.trans hB₂.symm⟩;
  · subst he;
    obtain ⟨hA₂, hB₂⟩ := h₂.spec_lt hn₂;
    exact ⟨hA.trans hA₂.symm, hB.trans hB₂.symm⟩;
  · subst he;
    obtain ⟨hA₂, hB₂⟩ := h₂.spec_nlt hn₂;
    exact ⟨hA.trans hA₂.symm, hB.trans hB₂.symm⟩;
  · subst he;
    obtain ⟨hd₂, hd₂', hA₂, hB₂⟩ := h₂.spec_and hn₂;
    obtain ⟨i1, i0⟩ := ih a (by simp) e' hd hd₂;
    obtain ⟨j1, j0⟩ := ih b (by simp) e' hd' hd₂';
    exact ⟨by rw [hA, hA₂, i1, j1], by rw [hB, hB₂, i0, j0]⟩;
  · subst he;
    obtain ⟨hd₂, hd₂', hA₂, hB₂⟩ := h₂.spec_or hn₂;
    obtain ⟨i1, i0⟩ := ih a (by simp) e' hd hd₂;
    obtain ⟨j1, j0⟩ := ih b (by simp) e' hd' hd₂';
    exact ⟨by rw [hA, hA₂, i1, j1], by rw [hB, hB₂, i0, j0]⟩;
  · subst he;
    obtain ⟨ht₂, hd₂, hA₂, hB₂⟩ := h₂.spec_ball hn₂;
    have key : ∀ x < termVal (0 ∷ e') a, (⟪⟪b, x ∷ e'⟫, 1⟫ ∈ q₁ ↔ ⟪⟪b, x ∷ e'⟫, 1⟫ ∈ q₂) ∧
        (⟪⟪b, x ∷ e'⟫, 0⟫ ∈ q₁ ↔ ⟪⟪b, x ∷ e'⟫, 0⟫ ∈ q₂) :=
      fun x hx ↦ ih b (by simp) (x ∷ e') (hd x hx) (hd₂ x hx);
    and_intros;
    · rw [hA, hA₂];
      exact forall_congr' fun x ↦ imp_congr_right fun hx ↦ (key x hx).1;
    · rw [hB, hB₂];
      exact exists_congr fun x ↦ and_congr_right fun hx ↦ (key x hx).2;
  · subst he;
    obtain ⟨ht₂, hd₂, hA₂, hB₂⟩ := h₂.spec_bex hn₂;
    have key : ∀ x < termVal (0 ∷ e') a, (⟪⟪b, x ∷ e'⟫, 1⟫ ∈ q₁ ↔ ⟪⟪b, x ∷ e'⟫, 1⟫ ∈ q₂) ∧
        (⟪⟪b, x ∷ e'⟫, 0⟫ ∈ q₁ ↔ ⟪⟪b, x ∷ e'⟫, 0⟫ ∈ q₂) :=
      fun x hx ↦ ih b (by simp) (x ∷ e') (hd x hx) (hd₂ x hx);
    and_intros;
    · rw [hA, hA₂];
      exact exists_congr fun x ↦ and_congr_right fun hx ↦ (key x hx).1;
    · rw [hB, hB₂];
      exact forall_congr' fun x ↦ imp_congr_right fun hx ↦ (key x hx).2;

lemma dom_subset (h₁ : BoundedSatisfactionTable q₁ z e) (h₂ : BoundedSatisfactionTable q₂ z e) :
    ∀ n ∈ domain q₁, n ∈ domain q₂ := by
  have key : ∀ k n, n ∈ domain q₁ → q₁ ≤ π₁ n + k → n ∈ domain q₂ := by
    apply ISigma1.pi1_succ_induction
      (P := fun k ↦ ∀ n, n ∈ domain q₁ → q₁ ≤ π₁ n + k → n ∈ domain q₂)
      (by definability);
    · intro n hn hle;
      exact absurd (by simpa using hle)
        (not_le.mpr (lt_of_le_of_lt (pi₁_le_self n) (lt_of_mem_domain hn)));
    · intro k IH n hn hle;
      have up : ∀ m, m ∈ domain q₁ → π₁ n < π₁ m → m ∈ domain q₂ := by
        intro m hm hlt;
        apply IH m hm;
        calc q₁ ≤ π₁ n + (k + 1) := hle
          _ = π₁ n + 1 + k := by simp [add_assoc, add_comm]
          _ ≤ π₁ m + k := add_le_add (lt_iff_succ_le.mp hlt) le_rfl;
      rcases h₁.minimal n hn with rfl | ⟨a, b, e'', hm, hc⟩ | ⟨a, b, e'', hm, hc⟩ |
        ⟨u, r, e'', hm, x, hx, rfl⟩ | ⟨u, r, e'', hm, x, hx, rfl⟩;
      · exact h₂.mem_dom_root;
      · rcases hc with rfl | rfl;
        · exact (h₂.spec_and (up _ hm (by simp))).1;
        · exact (h₂.spec_and (up _ hm (by simp))).2.1;
      · rcases hc with rfl | rfl;
        · exact (h₂.spec_or (up _ hm (by simp))).1;
        · exact (h₂.spec_or (up _ hm (by simp))).2.1;
      · exact (h₂.spec_ball (up _ hm (by simp))).2.1 x hx;
      · exact (h₂.spec_bex (up _ hm (by simp))).2.1 x hx;
  exact fun n hn ↦ key q₁ n hn le_add_self;

theorem uniq (h₁ : BoundedSatisfactionTable q₁ z e) (h₂ : BoundedSatisfactionTable q₂ z e) :
    q₁ = q₂ := by
  have sub : ∀ {r₁ r₂ : V}, BoundedSatisfactionTable r₁ z e → BoundedSatisfactionTable r₂ z e →
    ∀ x, x ∈ r₁ → x ∈ r₂ := by
    intro r₁ r₂ k₁ k₂ x hx;
    have hx' : ⟪π₁ x, π₂ x⟫ ∈ r₁ := by rwa [pair_unpair];
    have hn₁ : ⟪π₁ (π₁ x), π₂ (π₁ x)⟫ ∈ domain r₁ := by
      rw [pair_unpair]; exact mem_domain_of_pair_mem hx';
    have hn₂ : ⟪π₁ (π₁ x), π₂ (π₁ x)⟫ ∈ domain r₂ := by
      rw [pair_unpair]; exact k₁.dom_subset k₂ _ (mem_domain_of_pair_mem hx');
    obtain ⟨i1, i0⟩ := k₁.agree k₂ (π₁ (π₁ x)) (π₂ (π₁ x)) hn₁ hn₂;
    rw [pair_unpair] at i1 i0;
    rcases k₁.val_zero_or_one (π₁ (π₁ x)) (π₂ (π₁ x)) hn₁ with h' | h' <;> rw [pair_unpair] at h';
    · have hv : π₂ x = 1 := k₁.isMapping.uniq hx' h';
      have hxe : x = ⟪π₁ x, 1⟫ := by rw [← hv, pair_unpair];
      rw [hxe]; exact i1.mp h';
    · have hv : π₂ x = 0 := k₁.isMapping.uniq hx' h';
      have hxe : x = ⟪π₁ x, 0⟫ := by rw [← hv, pair_unpair];
      rw [hxe]; exact i0.mp h';
  exact mem_ext fun i ↦ ⟨sub h₁ h₂ i, sub h₂ h₁ i⟩;

end BoundedSatisfactionTable

/-! ### $\Delta_1$-definability

Each clause of `spec` and `minimal` gets a bounded `Prop` with a defining formula. Where a clause
mentions `termVal`, whose graph is $\Sigma_1$, the value is hoisted out by an existential on the
$\Sigma_1$ side and by a universal on the $\Pi_1$ side. -/

namespace BoundedSatisfactionTableF

/-! #### Nodes and values as $\Sigma_0$ relations -/

def inDomDef : 𝚺ᴬ₀.Semisentence 2 := .mkSigma “q n. ∃ v < q, :⟪n, v⟫:∈ q”

instance inDom_defined : 𝚺ᴬ₀-Relation (fun q n : V ↦ n ∈ domain q) via inDomDef := .mk fun v ↦ by
  suffices (∃ y < v 0, ⟪v 1, y⟫ ∈ v 0) ↔ v 1 ∈ domain (v 0) by simpa [inDomDef];
  rw [mem_domain_iff];
  exact ⟨fun ⟨y, _, h⟩ ↦ ⟨y, h⟩, fun ⟨y, h⟩ ↦ ⟨y, lt_of_mem_rng h, h⟩⟩;

def nodeValDef : 𝚺ᴬ₀.Semisentence 4 := .mkSigma
  “q p e v. ∃ n <⁺ (p + e + 1)², !pairDef n p e ∧ :⟪n, v⟫:∈ q”

instance nodeVal_defined :
    𝚺ᴬ₀-Relation₄ (fun q p e v : V ↦ ⟪⟪p, e⟫, v⟫ ∈ q) via nodeValDef := .mk fun v ↦ by
  simp [nodeValDef];

def nodeDomDef : 𝚺ᴬ₀.Semisentence 3 := .mkSigma “q p e. ∃ v < q, !nodeValDef q p e v”

instance nodeDom_defined :
    𝚺ᴬ₀-Relation₃ (fun q p e : V ↦ ⟪p, e⟫ ∈ domain q) via nodeDomDef := .mk fun v ↦ by
  suffices (∃ y < v 0, ⟪⟪v 1, v 2⟫, y⟫ ∈ v 0) ↔ ⟪v 1, v 2⟫ ∈ domain (v 0) by
    simpa [nodeDomDef, nodeVal_defined.df];
  rw [mem_domain_iff];
  exact ⟨fun ⟨y, _, h⟩ ↦ ⟨y, h⟩, fun ⟨y, h⟩ ↦ ⟨y, lt_of_mem_rng h, h⟩⟩;

def childValDef : 𝚺ᴬ₀.Semisentence 5 := .mkSigma
  “q p x e v. ∃ xe <⁺ (x + e + 1)² + 1, !adjoinDef xe x e ∧ !nodeValDef q p xe v”

instance childVal_defined :
    HierarchySymbol.Defined (fun v : Fin 5 → V ↦ ⟪⟪v 1, v 2 ∷ v 3⟫, v 4⟫ ∈ v 0) childValDef :=
  .mk fun v ↦ by simp [childValDef, nodeVal_defined.df, adjoin_def]

def childDomDef : 𝚺ᴬ₀.Semisentence 4 := .mkSigma
  “q p x e. ∃ xe <⁺ (x + e + 1)² + 1, !adjoinDef xe x e ∧ !nodeDomDef q p xe”

instance childDom_defined :
    𝚺ᴬ₀-Relation₄ (fun q p x e : V ↦ ⟪p, x ∷ e⟫ ∈ domain q) via childDomDef := .mk fun v ↦ by
  simp [childDomDef, nodeDom_defined.df, adjoin_def];

def childPairDef : 𝚺ᴬ₀.Semisentence 4 := .mkSigma
  “n p x e. ∃ xe <⁺ (x + e + 1)² + 1, !adjoinDef xe x e ∧ !pairDef n p xe”

instance childPair_defined :
    𝚺ᴬ₀-Relation₄ (fun n p x e : V ↦ n = ⟪p, x ∷ e⟫) via childPairDef := .mk fun v ↦ by
  simp [childPairDef, adjoin_def];

/-! #### The ten Tarski clauses -/

def SpecVerum (q z e : V) : Prop := z = ^⊤ ∧ ⟪⟪z, e⟫, 1⟫ ∈ q

def specVerumDef : 𝚺ᴬ₀.Semisentence 3 := .mkSigma “q z e. !qqVerumDef z ∧ !nodeValDef q z e 1”

instance specVerum_defined : 𝚺ᴬ₀-Relation₃ (SpecVerum : V → V → V → Prop) via specVerumDef :=
  .mk fun v ↦ by simp [specVerumDef, SpecVerum, nodeVal_defined.df]

def SpecFalsum (q z e : V) : Prop := z = ^⊥ ∧ ⟪⟪z, e⟫, 0⟫ ∈ q

def specFalsumDef : 𝚺ᴬ₀.Semisentence 3 := .mkSigma “q z e. !qqFalsumDef z ∧ !nodeValDef q z e 0”

instance specFalsum_defined : 𝚺ᴬ₀-Relation₃ (SpecFalsum : V → V → V → Prop) via specFalsumDef :=
  .mk fun v ↦ by simp [specFalsumDef, SpecFalsum, nodeVal_defined.df]

def SpecEq (q z e : V) : Prop := ∃ t < z, ∃ u < z, IsUTerm ℒₒᵣ t ∧ IsUTerm ℒₒᵣ u ∧ z = t ^= u ∧
    (⟪⟪z, e⟫, 1⟫ ∈ q ↔ termVal e t = termVal e u) ∧
    (⟪⟪z, e⟫, 0⟫ ∈ q ↔ termVal e t ≠ termVal e u)

def eqMatrixDef : 𝚺ᴬ₀.Semisentence 5 := .mkSigma
  “q z e a b. (!nodeValDef q z e 1 ↔ a = b) ∧ (!nodeValDef q z e 0 ↔ a ≠ b)”

instance eqMatrix_defined :
    HierarchySymbol.Defined (fun v : Fin 5 → V ↦
      (⟪⟪v 1, v 2⟫, 1⟫ ∈ v 0 ↔ v 3 = v 4) ∧ (⟪⟪v 1, v 2⟫, 0⟫ ∈ v 0 ↔ v 3 ≠ v 4)) eqMatrixDef :=
  .mk fun v ↦ by simp [eqMatrixDef, nodeVal_defined.df]

noncomputable def specEqDef : 𝚫ᴬ₁.Semisentence 3 := .mkDelta
  (.mkSigma “q z e. ∃ t < z, ∃ u < z, !(isUTerm ℒₒᵣ).sigma t ∧ !(isUTerm ℒₒᵣ).sigma u ∧
    !qqEQDef z t u ∧
    ∃ a, !termValGraph a e t ∧ ∃ b, !termValGraph b e u ∧ !eqMatrixDef q z e a b”)
  (.mkPi “q z e. ∃ t < z, ∃ u < z, !(isUTerm ℒₒᵣ).pi t ∧ !(isUTerm ℒₒᵣ).pi u ∧
    (∀ z', !qqEQDef z' t u → z = z') ∧
    ∀ a, !termValGraph a e t → ∀ b, !termValGraph b e u → !eqMatrixDef q z e a b”)

instance specEq_defined : 𝚫ᴬ₁-Relation₃ (SpecEq : V → V → V → Prop) via specEqDef := .mk <| by
  constructor;
  · intro v;
    simp [specEqDef, HierarchySymbol.Semiformula.val_sigma, (termVal.defined (V := V)).df,
      (qqEQ_defined (V := V)).df, eqMatrix_defined.df];
  · intro v;
    simp [specEqDef, HierarchySymbol.Semiformula.val_sigma, SpecEq, (termVal.defined (V := V)).df,
      (qqEQ_defined (V := V)).df, eqMatrix_defined.df];

def SpecNeq (q z e : V) : Prop := ∃ t < z, ∃ u < z, IsUTerm ℒₒᵣ t ∧ IsUTerm ℒₒᵣ u ∧ z = t ^≠ u ∧
    (⟪⟪z, e⟫, 1⟫ ∈ q ↔ termVal e t ≠ termVal e u) ∧
    (⟪⟪z, e⟫, 0⟫ ∈ q ↔ termVal e t = termVal e u)

def neqMatrixDef : 𝚺ᴬ₀.Semisentence 5 := .mkSigma
  “q z e a b. (!nodeValDef q z e 1 ↔ a ≠ b) ∧ (!nodeValDef q z e 0 ↔ a = b)”

instance neqMatrix_defined :
    HierarchySymbol.Defined (fun v : Fin 5 → V ↦
      (⟪⟪v 1, v 2⟫, 1⟫ ∈ v 0 ↔ v 3 ≠ v 4) ∧ (⟪⟪v 1, v 2⟫, 0⟫ ∈ v 0 ↔ v 3 = v 4)) neqMatrixDef :=
  .mk fun v ↦ by simp [neqMatrixDef, nodeVal_defined.df]

noncomputable def specNeqDef : 𝚫ᴬ₁.Semisentence 3 := .mkDelta
  (.mkSigma “q z e. ∃ t < z, ∃ u < z, !(isUTerm ℒₒᵣ).sigma t ∧ !(isUTerm ℒₒᵣ).sigma u ∧
    !qqNEQDef z t u ∧
    ∃ a, !termValGraph a e t ∧ ∃ b, !termValGraph b e u ∧ !neqMatrixDef q z e a b”)
  (.mkPi “q z e. ∃ t < z, ∃ u < z, !(isUTerm ℒₒᵣ).pi t ∧ !(isUTerm ℒₒᵣ).pi u ∧
    (∀ z', !qqNEQDef z' t u → z = z') ∧
    ∀ a, !termValGraph a e t → ∀ b, !termValGraph b e u → !neqMatrixDef q z e a b”)

instance specNeq_defined : 𝚫ᴬ₁-Relation₃ (SpecNeq : V → V → V → Prop) via specNeqDef := .mk <| by
  constructor;
  · intro v;
    simp [specNeqDef, HierarchySymbol.Semiformula.val_sigma, (termVal.defined (V := V)).df,
      (qqNEQ_defined (V := V)).df, neqMatrix_defined.df];
  · intro v;
    simp [specNeqDef, HierarchySymbol.Semiformula.val_sigma, SpecNeq, (termVal.defined (V := V)).df,
      (qqNEQ_defined (V := V)).df, neqMatrix_defined.df];

def SpecLt (q z e : V) : Prop := ∃ t < z, ∃ u < z, IsUTerm ℒₒᵣ t ∧ IsUTerm ℒₒᵣ u ∧ z = t ^< u ∧
    (⟪⟪z, e⟫, 1⟫ ∈ q ↔ termVal e t < termVal e u) ∧
    (⟪⟪z, e⟫, 0⟫ ∈ q ↔ ¬termVal e t < termVal e u)

def ltMatrixDef : 𝚺ᴬ₀.Semisentence 5 := .mkSigma
  “q z e a b. (!nodeValDef q z e 1 ↔ a < b) ∧ (!nodeValDef q z e 0 ↔ ¬a < b)”

instance ltMatrix_defined :
    HierarchySymbol.Defined (fun v : Fin 5 → V ↦
      (⟪⟪v 1, v 2⟫, 1⟫ ∈ v 0 ↔ v 3 < v 4) ∧ (⟪⟪v 1, v 2⟫, 0⟫ ∈ v 0 ↔ ¬v 3 < v 4)) ltMatrixDef :=
  .mk fun v ↦ by simp [ltMatrixDef, nodeVal_defined.df]

noncomputable def specLtDef : 𝚫ᴬ₁.Semisentence 3 := .mkDelta
  (.mkSigma “q z e. ∃ t < z, ∃ u < z, !(isUTerm ℒₒᵣ).sigma t ∧ !(isUTerm ℒₒᵣ).sigma u ∧
    !qqLTDef z t u ∧
    ∃ a, !termValGraph a e t ∧ ∃ b, !termValGraph b e u ∧ !ltMatrixDef q z e a b”)
  (.mkPi “q z e. ∃ t < z, ∃ u < z, !(isUTerm ℒₒᵣ).pi t ∧ !(isUTerm ℒₒᵣ).pi u ∧
    (∀ z', !qqLTDef z' t u → z = z') ∧
    ∀ a, !termValGraph a e t → ∀ b, !termValGraph b e u → !ltMatrixDef q z e a b”)

instance specLt_defined : 𝚫ᴬ₁-Relation₃ (SpecLt : V → V → V → Prop) via specLtDef := .mk <| by
  constructor;
  · intro v;
    simp [specLtDef, HierarchySymbol.Semiformula.val_sigma, (termVal.defined (V := V)).df,
      (qqLT_defined (V := V)).df, ltMatrix_defined.df];
  · intro v;
    simp [specLtDef, HierarchySymbol.Semiformula.val_sigma, SpecLt, (termVal.defined (V := V)).df,
      (qqLT_defined (V := V)).df, ltMatrix_defined.df];

def SpecNlt (q z e : V) : Prop := ∃ t < z, ∃ u < z, IsUTerm ℒₒᵣ t ∧ IsUTerm ℒₒᵣ u ∧ z = t ^≮ u ∧
    (⟪⟪z, e⟫, 1⟫ ∈ q ↔ ¬termVal e t < termVal e u) ∧
    (⟪⟪z, e⟫, 0⟫ ∈ q ↔ termVal e t < termVal e u)

def nltMatrixDef : 𝚺ᴬ₀.Semisentence 5 := .mkSigma
  “q z e a b. (!nodeValDef q z e 1 ↔ ¬a < b) ∧ (!nodeValDef q z e 0 ↔ a < b)”

instance nltMatrix_defined :
    HierarchySymbol.Defined (fun v : Fin 5 → V ↦
      (⟪⟪v 1, v 2⟫, 1⟫ ∈ v 0 ↔ ¬v 3 < v 4) ∧ (⟪⟪v 1, v 2⟫, 0⟫ ∈ v 0 ↔ v 3 < v 4)) nltMatrixDef :=
  .mk fun v ↦ by simp [nltMatrixDef, nodeVal_defined.df]

noncomputable def specNltDef : 𝚫ᴬ₁.Semisentence 3 := .mkDelta
  (.mkSigma “q z e. ∃ t < z, ∃ u < z, !(isUTerm ℒₒᵣ).sigma t ∧ !(isUTerm ℒₒᵣ).sigma u ∧
    !qqNLTDef z t u ∧
    ∃ a, !termValGraph a e t ∧ ∃ b, !termValGraph b e u ∧ !nltMatrixDef q z e a b”)
  (.mkPi “q z e. ∃ t < z, ∃ u < z, !(isUTerm ℒₒᵣ).pi t ∧ !(isUTerm ℒₒᵣ).pi u ∧
    (∀ z', !qqNLTDef z' t u → z = z') ∧
    ∀ a, !termValGraph a e t → ∀ b, !termValGraph b e u → !nltMatrixDef q z e a b”)

instance specNlt_defined : 𝚫ᴬ₁-Relation₃ (SpecNlt : V → V → V → Prop) via specNltDef := .mk <| by
  constructor;
  · intro v;
    simp [specNltDef, HierarchySymbol.Semiformula.val_sigma, (termVal.defined (V := V)).df,
      (qqNLT_defined (V := V)).df, nltMatrix_defined.df];
  · intro v;
    simp [specNltDef, HierarchySymbol.Semiformula.val_sigma, SpecNlt, (termVal.defined (V := V)).df,
      (qqNLT_defined (V := V)).df, nltMatrix_defined.df];

def SpecAnd (q z e : V) : Prop :=
  ∃ p₁ < z, ∃ p₂ < z, z = p₁ ^⋏ p₂ ∧ ⟪p₁, e⟫ ∈ domain q ∧ ⟪p₂, e⟫ ∈ domain q ∧
    (⟪⟪z, e⟫, 1⟫ ∈ q ↔ ⟪⟪p₁, e⟫, 1⟫ ∈ q ∧ ⟪⟪p₂, e⟫, 1⟫ ∈ q) ∧
    (⟪⟪z, e⟫, 0⟫ ∈ q ↔ ⟪⟪p₁, e⟫, 0⟫ ∈ q ∨ ⟪⟪p₂, e⟫, 0⟫ ∈ q)

def specAndDef : 𝚺ᴬ₀.Semisentence 3 := .mkSigma
  “q z e. ∃ p₁ < z, ∃ p₂ < z, !qqAndDef z p₁ p₂ ∧ !nodeDomDef q p₁ e ∧ !nodeDomDef q p₂ e ∧
    (!nodeValDef q z e 1 ↔ !nodeValDef q p₁ e 1 ∧ !nodeValDef q p₂ e 1) ∧
    (!nodeValDef q z e 0 ↔ !nodeValDef q p₁ e 0 ∨ !nodeValDef q p₂ e 0)”

instance specAnd_defined : 𝚺ᴬ₀-Relation₃ (SpecAnd : V → V → V → Prop) via specAndDef :=
  .mk fun v ↦ by simp [specAndDef, SpecAnd, nodeVal_defined.df, nodeDom_defined.df]

def SpecOr (q z e : V) : Prop :=
  ∃ p₁ < z, ∃ p₂ < z, z = p₁ ^⋎ p₂ ∧ ⟪p₁, e⟫ ∈ domain q ∧ ⟪p₂, e⟫ ∈ domain q ∧
    (⟪⟪z, e⟫, 1⟫ ∈ q ↔ ⟪⟪p₁, e⟫, 1⟫ ∈ q ∨ ⟪⟪p₂, e⟫, 1⟫ ∈ q) ∧
    (⟪⟪z, e⟫, 0⟫ ∈ q ↔ ⟪⟪p₁, e⟫, 0⟫ ∈ q ∧ ⟪⟪p₂, e⟫, 0⟫ ∈ q)

def specOrDef : 𝚺ᴬ₀.Semisentence 3 := .mkSigma
  “q z e. ∃ p₁ < z, ∃ p₂ < z, !qqOrDef z p₁ p₂ ∧ !nodeDomDef q p₁ e ∧ !nodeDomDef q p₂ e ∧
    (!nodeValDef q z e 1 ↔ !nodeValDef q p₁ e 1 ∨ !nodeValDef q p₂ e 1) ∧
    (!nodeValDef q z e 0 ↔ !nodeValDef q p₁ e 0 ∧ !nodeValDef q p₂ e 0)”

instance specOr_defined : 𝚺ᴬ₀-Relation₃ (SpecOr : V → V → V → Prop) via specOrDef :=
  .mk fun v ↦ by simp [specOrDef, SpecOr, nodeVal_defined.df, nodeDom_defined.df]

def SpecBall (q z e : V) : Prop :=
  ∃ u < z, ∃ p < z, (∃ t ≤ u, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧ z = qqBall u p ∧
    (∀ x < termVal (0 ∷ e) u, ⟪p, x ∷ e⟫ ∈ domain q) ∧
    (⟪⟪z, e⟫, 1⟫ ∈ q ↔ ∀ x < termVal (0 ∷ e) u, ⟪⟪p, x ∷ e⟫, 1⟫ ∈ q) ∧
    (⟪⟪z, e⟫, 0⟫ ∈ q ↔ ∃ x < termVal (0 ∷ e) u, ⟪⟪p, x ∷ e⟫, 0⟫ ∈ q)

def ballMatrixDef : 𝚺ᴬ₀.Semisentence 5 := .mkSigma
  “q z e p b. (∀ x < b, !childDomDef q p x e) ∧
    (!nodeValDef q z e 1 ↔ ∀ x < b, !childValDef q p x e 1) ∧
    (!nodeValDef q z e 0 ↔ ∃ x < b, !childValDef q p x e 0)”

instance ballMatrix_defined :
    HierarchySymbol.Defined (fun v : Fin 5 → V ↦ (∀ x < v 4, ⟪v 3, x ∷ v 2⟫ ∈ domain (v 0)) ∧
      (⟪⟪v 1, v 2⟫, 1⟫ ∈ v 0 ↔ ∀ x < v 4, ⟪⟪v 3, x ∷ v 2⟫, 1⟫ ∈ v 0) ∧
      (⟪⟪v 1, v 2⟫, 0⟫ ∈ v 0 ↔ ∃ x < v 4, ⟪⟪v 3, x ∷ v 2⟫, 0⟫ ∈ v 0)) ballMatrixDef :=
  .mk fun v ↦ by
    simp [ballMatrixDef, nodeVal_defined.df, childVal_defined.df, childDom_defined.df];

noncomputable def specBallDef : 𝚫ᴬ₁.Semisentence 3 := .mkDelta
  (.mkSigma “q z e. ∃ u < z, ∃ p < z,
    (∃ t <⁺ u, !(isUTerm ℒₒᵣ).sigma t ∧ !(termBShiftGraph ℒₒᵣ) u t) ∧ !qqBallDef z u p ∧
    ∃ e0, !adjoinDef e0 0 e ∧ ∃ b, !termValGraph b e0 u ∧ !ballMatrixDef q z e p b”)
  (.mkPi “q z e. ∃ u < z, ∃ p < z,
    (∃ t <⁺ u, !(isUTerm ℒₒᵣ).pi t ∧ ∀ u', !(termBShiftGraph ℒₒᵣ) u' t → u = u') ∧
    (∀ z', !qqBallDef z' u p → z = z') ∧
    ∀ e0, !adjoinDef e0 0 e → ∀ b, !termValGraph b e0 u → !ballMatrixDef q z e p b”)

instance specBall_defined : 𝚫ᴬ₁-Relation₃ (SpecBall : V → V → V → Prop) via specBallDef := .mk <| by
  constructor;
  · intro v;
    simp [specBallDef, HierarchySymbol.Semiformula.val_sigma, (termVal.defined (V := V)).df,
      (termBShift.defined (L := ℒₒᵣ) (V := V)).df, (qqBall_defined (V := V)).df,
      ballMatrix_defined.df, adjoin_def];
  · intro v;
    simp [specBallDef, HierarchySymbol.Semiformula.val_sigma, SpecBall,
      (termVal.defined (V := V)).df, (termBShift.defined (L := ℒₒᵣ) (V := V)).df,
      (qqBall_defined (V := V)).df, ballMatrix_defined.df, adjoin_def];

def SpecBex (q z e : V) : Prop :=
  ∃ u < z, ∃ p < z, (∃ t ≤ u, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧ z = qqBex u p ∧
    (∀ x < termVal (0 ∷ e) u, ⟪p, x ∷ e⟫ ∈ domain q) ∧
    (⟪⟪z, e⟫, 1⟫ ∈ q ↔ ∃ x < termVal (0 ∷ e) u, ⟪⟪p, x ∷ e⟫, 1⟫ ∈ q) ∧
    (⟪⟪z, e⟫, 0⟫ ∈ q ↔ ∀ x < termVal (0 ∷ e) u, ⟪⟪p, x ∷ e⟫, 0⟫ ∈ q)

def bexMatrixDef : 𝚺ᴬ₀.Semisentence 5 := .mkSigma
  “q z e p b. (∀ x < b, !childDomDef q p x e) ∧
    (!nodeValDef q z e 1 ↔ ∃ x < b, !childValDef q p x e 1) ∧
    (!nodeValDef q z e 0 ↔ ∀ x < b, !childValDef q p x e 0)”

instance bexMatrix_defined :
    HierarchySymbol.Defined (fun v : Fin 5 → V ↦ (∀ x < v 4, ⟪v 3, x ∷ v 2⟫ ∈ domain (v 0)) ∧
      (⟪⟪v 1, v 2⟫, 1⟫ ∈ v 0 ↔ ∃ x < v 4, ⟪⟪v 3, x ∷ v 2⟫, 1⟫ ∈ v 0) ∧
      (⟪⟪v 1, v 2⟫, 0⟫ ∈ v 0 ↔ ∀ x < v 4, ⟪⟪v 3, x ∷ v 2⟫, 0⟫ ∈ v 0)) bexMatrixDef :=
  .mk fun v ↦ by
    simp [bexMatrixDef, nodeVal_defined.df, childVal_defined.df, childDom_defined.df];

noncomputable def specBexDef : 𝚫ᴬ₁.Semisentence 3 := .mkDelta
  (.mkSigma “q z e. ∃ u < z, ∃ p < z,
    (∃ t <⁺ u, !(isUTerm ℒₒᵣ).sigma t ∧ !(termBShiftGraph ℒₒᵣ) u t) ∧ !qqBexDef z u p ∧
    ∃ e0, !adjoinDef e0 0 e ∧ ∃ b, !termValGraph b e0 u ∧ !bexMatrixDef q z e p b”)
  (.mkPi “q z e. ∃ u < z, ∃ p < z,
    (∃ t <⁺ u, !(isUTerm ℒₒᵣ).pi t ∧ ∀ u', !(termBShiftGraph ℒₒᵣ) u' t → u = u') ∧
    (∀ z', !qqBexDef z' u p → z = z') ∧
    ∀ e0, !adjoinDef e0 0 e → ∀ b, !termValGraph b e0 u → !bexMatrixDef q z e p b”)

instance specBex_defined : 𝚫ᴬ₁-Relation₃ (SpecBex : V → V → V → Prop) via specBexDef := .mk <| by
  constructor;
  · intro v;
    simp [specBexDef, HierarchySymbol.Semiformula.val_sigma, (termVal.defined (V := V)).df,
      (termBShift.defined (L := ℒₒᵣ) (V := V)).df, (qqBex_defined (V := V)).df,
      bexMatrix_defined.df, adjoin_def];
  · intro v;
    simp [specBexDef, HierarchySymbol.Semiformula.val_sigma, SpecBex,
      (termVal.defined (V := V)).df, (termBShift.defined (L := ℒₒᵣ) (V := V)).df,
      (qqBex_defined (V := V)).df, bexMatrix_defined.df, adjoin_def];

/-! #### The clause of `BoundedSatisfactionTable.spec`, assembled -/

def SpecAt (q z e : V) : Prop :=
  SpecVerum q z e ∨ SpecFalsum q z e ∨ SpecEq q z e ∨ SpecNeq q z e ∨ SpecLt q z e ∨
    SpecNlt q z e ∨ SpecAnd q z e ∨ SpecOr q z e ∨ SpecBall q z e ∨ SpecBex q z e

noncomputable def specDef : 𝚫ᴬ₁.Semisentence 3 := .mkDelta
  (.mkSigma “q z e. !specVerumDef q z e ∨ !specFalsumDef q z e ∨ !specEqDef.sigma q z e ∨
    !specNeqDef.sigma q z e ∨ !specLtDef.sigma q z e ∨ !specNltDef.sigma q z e ∨
    !specAndDef q z e ∨ !specOrDef q z e ∨ !specBallDef.sigma q z e ∨ !specBexDef.sigma q z e”)
  (.mkPi “q z e. !specVerumDef q z e ∨ !specFalsumDef q z e ∨ !specEqDef.pi q z e ∨
    !specNeqDef.pi q z e ∨ !specLtDef.pi q z e ∨ !specNltDef.pi q z e ∨
    !specAndDef q z e ∨ !specOrDef q z e ∨ !specBallDef.pi q z e ∨ !specBexDef.pi q z e”)

instance specAt_defined : 𝚫ᴬ₁-Relation₃ (SpecAt : V → V → V → Prop) via specDef := .mk <| by
  constructor;
  · intro v; simp [specDef, HierarchySymbol.Semiformula.val_sigma];
  · intro v; simp [specDef, HierarchySymbol.Semiformula.val_sigma, SpecAt];

/-! #### The clause of `BoundedSatisfactionTable.minimal` -/

def MinAnd (q n : V) : Prop :=
  ∃ c < q, ∃ p₁ < c, ∃ p₂ < c, ∃ e < q, c = p₁ ^⋏ p₂ ∧ ⟪c, e⟫ ∈ domain q ∧
    (n = ⟪p₁, e⟫ ∨ n = ⟪p₂, e⟫)

def minAndDef : 𝚺ᴬ₀.Semisentence 2 := .mkSigma
  “q n. ∃ c < q, ∃ p₁ < c, ∃ p₂ < c, ∃ e < q, !qqAndDef c p₁ p₂ ∧ !nodeDomDef q c e ∧
    (!pairDef n p₁ e ∨ !pairDef n p₂ e)”

instance minAnd_defined : 𝚺ᴬ₀-Relation (MinAnd : V → V → Prop) via minAndDef := .mk fun v ↦ by
  simp [minAndDef, MinAnd, nodeDom_defined.df];

def MinOr (q n : V) : Prop :=
  ∃ c < q, ∃ p₁ < c, ∃ p₂ < c, ∃ e < q, c = p₁ ^⋎ p₂ ∧ ⟪c, e⟫ ∈ domain q ∧
    (n = ⟪p₁, e⟫ ∨ n = ⟪p₂, e⟫)

def minOrDef : 𝚺ᴬ₀.Semisentence 2 := .mkSigma
  “q n. ∃ c < q, ∃ p₁ < c, ∃ p₂ < c, ∃ e < q, !qqOrDef c p₁ p₂ ∧ !nodeDomDef q c e ∧
    (!pairDef n p₁ e ∨ !pairDef n p₂ e)”

instance minOr_defined : 𝚺ᴬ₀-Relation (MinOr : V → V → Prop) via minOrDef := .mk fun v ↦ by
  simp [minOrDef, MinOr, nodeDom_defined.df];

def minChildDef : 𝚺ᴬ₀.Semisentence 4 := .mkSigma “n p e b. ∃ x < b, !childPairDef n p x e”

instance minChild_defined :
    𝚺ᴬ₀-Relation₄ (fun n p e b : V ↦ ∃ x < b, n = ⟪p, x ∷ e⟫) via minChildDef := .mk fun v ↦ by
  simp [minChildDef, childPair_defined.df];

def MinBall (q n : V) : Prop :=
  ∃ c < q, ∃ u < c, ∃ p < c, ∃ e < q, c = qqBall u p ∧ ⟪c, e⟫ ∈ domain q ∧
    ∃ x < termVal (0 ∷ e) u, n = ⟪p, x ∷ e⟫

noncomputable def minBallDef : 𝚫ᴬ₁.Semisentence 2 := .mkDelta
  (.mkSigma “q n. ∃ c < q, ∃ u < c, ∃ p < c, ∃ e < q, !qqBallDef c u p ∧ !nodeDomDef q c e ∧
    ∃ e0, !adjoinDef e0 0 e ∧ ∃ b, !termValGraph b e0 u ∧ !minChildDef n p e b”)
  (.mkPi “q n. ∃ c < q, ∃ u < c, ∃ p < c, ∃ e < q, (∀ c', !qqBallDef c' u p → c = c') ∧
    !nodeDomDef q c e ∧
    ∀ e0, !adjoinDef e0 0 e → ∀ b, !termValGraph b e0 u → !minChildDef n p e b”)

instance minBall_defined : 𝚫ᴬ₁-Relation (MinBall : V → V → Prop) via minBallDef := .mk <| by
  constructor;
  · intro v;
    simp [minBallDef, (termVal.defined (V := V)).df,
      (qqBall_defined (V := V)).df, nodeDom_defined.df, minChild_defined.df, adjoin_def];
  · intro v;
    simp [minBallDef, MinBall, (termVal.defined (V := V)).df, (qqBall_defined (V := V)).df,
      nodeDom_defined.df,
      minChild_defined.df, adjoin_def];

def MinBex (q n : V) : Prop :=
  ∃ c < q, ∃ u < c, ∃ p < c, ∃ e < q, c = qqBex u p ∧ ⟪c, e⟫ ∈ domain q ∧
    ∃ x < termVal (0 ∷ e) u, n = ⟪p, x ∷ e⟫

noncomputable def minBexDef : 𝚫ᴬ₁.Semisentence 2 := .mkDelta
  (.mkSigma “q n. ∃ c < q, ∃ u < c, ∃ p < c, ∃ e < q, !qqBexDef c u p ∧ !nodeDomDef q c e ∧
    ∃ e0, !adjoinDef e0 0 e ∧ ∃ b, !termValGraph b e0 u ∧ !minChildDef n p e b”)
  (.mkPi “q n. ∃ c < q, ∃ u < c, ∃ p < c, ∃ e < q, (∀ c', !qqBexDef c' u p → c = c') ∧
    !nodeDomDef q c e ∧
    ∀ e0, !adjoinDef e0 0 e → ∀ b, !termValGraph b e0 u → !minChildDef n p e b”)

instance minBex_defined : 𝚫ᴬ₁-Relation (MinBex : V → V → Prop) via minBexDef := .mk <| by
  constructor;
  · intro v;
    simp [minBexDef, (termVal.defined (V := V)).df,
      (qqBex_defined (V := V)).df, nodeDom_defined.df, minChild_defined.df, adjoin_def];
  · intro v;
    simp [minBexDef, MinBex, (termVal.defined (V := V)).df, (qqBex_defined (V := V)).df,
      nodeDom_defined.df,
      minChild_defined.df, adjoin_def];

def MinimalAt (q z e n : V) : Prop := n = ⟪z, e⟫ ∨ MinAnd q n ∨ MinOr q n ∨ MinBall q n ∨ MinBex q n

noncomputable def minimalDef : 𝚫ᴬ₁.Semisentence 4 := .mkDelta
  (.mkSigma “q z e n. !pairDef n z e ∨ !minAndDef q n ∨ !minOrDef q n ∨ !minBallDef.sigma q n ∨
    !minBexDef.sigma q n”)
  (.mkPi “q z e n. !pairDef n z e ∨ !minAndDef q n ∨ !minOrDef q n ∨ !minBallDef.pi q n ∨
    !minBexDef.pi q n”)

instance minimalAt_defined :
    𝚫ᴬ₁-Relation₄ (MinimalAt : V → V → V → V → Prop) via minimalDef := .mk <| by
  constructor;
  · intro v; simp [minimalDef, HierarchySymbol.Semiformula.val_sigma];
  · intro v; simp [minimalDef, HierarchySymbol.Semiformula.val_sigma, MinimalAt];

/-! #### Assembling the definition -/

lemma boundedSatisfactionTable_iff {q z e : V} : BoundedSatisfactionTable q z e ↔ IsMapping q ∧
    ⟪z, e⟫ ∈ domain q ∧
    (∀ z' < q, ∀ e' < q, ⟪z', e'⟫ ∈ domain q → SpecAt q z' e') ∧
    (∀ n < q, n ∈ domain q → MinimalAt q z e n) := by
  constructor;
  · rintro ⟨hm, hr, hs, hmin⟩;
    and_intros;
    · exact hm;
    · exact hr;
    · intro z' _ e' _ hd;
      rcases hs z' e' hd with
        h | h | ⟨t, u, ht, hu, rfl, h⟩ | ⟨t, u, ht, hu, rfl, h⟩ | ⟨t, u, ht, hu, rfl, h⟩ |
        ⟨t, u, ht, hu, rfl, h⟩ | ⟨p₁, p₂, rfl, h⟩ | ⟨p₁, p₂, rfl, h⟩ |
        ⟨u, p, ⟨t, ht, rfl⟩, rfl, h⟩ | ⟨u, p, ⟨t, ht, rfl⟩, rfl, h⟩;
      · disj 1; exact h;
      · disj 2; exact h;
      · disj 3; exact ⟨t, by simp, u, by simp, ht, hu, rfl, h⟩;
      · disj 4; exact ⟨t, by simp, u, by simp, ht, hu, rfl, h⟩;
      · disj 5; exact ⟨t, by simp, u, by simp, ht, hu, rfl, h⟩;
      · disj 6; exact ⟨t, by simp, u, by simp, ht, hu, rfl, h⟩;
      · disj 7; exact ⟨p₁, by simp, p₂, by simp, rfl, h⟩;
      · disj 8; exact ⟨p₁, by simp, p₂, by simp, rfl, h⟩;
      · disj 9;
        exact ⟨termBShift ℒₒᵣ t, by simp, p, by simp, ⟨t, le_termBShift ht, ht, rfl⟩, rfl, h⟩;
      · disj 10;
        exact ⟨termBShift ℒₒᵣ t, by simp, p, by simp, ⟨t, le_termBShift ht, ht, rfl⟩, rfl, h⟩;
    · intro n _ hn;
      rcases hmin n hn with h | ⟨p₁, p₂, e', hd, hc⟩ | ⟨p₁, p₂, e', hd, hc⟩ |
        ⟨u, p, e', hd, hx⟩ | ⟨u, p, e', hd, hx⟩;
      · disj 1; exact h;
      · disj 2;
        exact ⟨p₁ ^⋏ p₂, fst_lt_of_mem_domain hd, p₁, by simp, p₂, by simp, e',
          snd_lt_of_mem_domain hd, rfl, hd, hc⟩;
      · disj 3;
        exact ⟨p₁ ^⋎ p₂, fst_lt_of_mem_domain hd, p₁, by simp, p₂, by simp, e',
          snd_lt_of_mem_domain hd, rfl, hd, hc⟩;
      · disj 4;
        exact ⟨qqBall u p, fst_lt_of_mem_domain hd, u, by simp, p, by simp, e',
          snd_lt_of_mem_domain hd, rfl, hd, hx⟩;
      · disj 5;
        exact ⟨qqBex u p, fst_lt_of_mem_domain hd, u, by simp, p, by simp, e',
          snd_lt_of_mem_domain hd, rfl, hd, hx⟩;
  · rintro ⟨hm, hr, hs, hmin⟩;
    constructor;
    · exact hm;
    · exact hr;
    · intro z' e' hd;
      rcases hs z' (fst_lt_of_mem_domain hd) e' (snd_lt_of_mem_domain hd) hd with
          h
        | h
        | ⟨t, -, u, -, h⟩
        | ⟨t, -, u, -, h⟩
        | ⟨t, -, u, -, h⟩
        | ⟨t, -, u, -, h⟩
        | ⟨p₁, -, p₂, -, h⟩
        | ⟨p₁, -, p₂, -, h⟩
        | ⟨u, -, p, -, ⟨t, -, ht⟩, h⟩
        | ⟨u, -, p, -, ⟨t, -, ht⟩, h⟩;
      · disj 1; exact h;
      · disj 2; exact h;
      · disj 3; exact ⟨t, u, h⟩;
      · disj 4; exact ⟨t, u, h⟩;
      · disj 5; exact ⟨t, u, h⟩;
      · disj 6; exact ⟨t, u, h⟩;
      · disj 7; exact ⟨p₁, p₂, h⟩;
      · disj 8; exact ⟨p₁, p₂, h⟩;
      · disj 9; exact ⟨u, p, ⟨t, ht⟩, h⟩;
      · disj 10; exact ⟨u, p, ⟨t, ht⟩, h⟩;
    · intro n hn;
      rcases hmin n (lt_of_mem_domain hn) hn with
        h
        | ⟨c, -, p₁, -, p₂, -, e', -, rfl, hd, hc⟩
        | ⟨c, -, p₁, -, p₂, -, e', -, rfl, hd, hc⟩
        | ⟨c, -, u, -, p, -, e', -, rfl, hd, hx⟩
        | ⟨c, -, u, -, p, -, e', -, rfl, hd, hx⟩;
      · disj 1; exact h;
      · disj 2; exact ⟨p₁, p₂, e', hd, hc⟩;
      · disj 3; exact ⟨p₁, p₂, e', hd, hc⟩;
      · disj 4; exact ⟨u, p, e', hd, hx⟩;
      · disj 5; exact ⟨u, p, e', hd, hx⟩;

end BoundedSatisfactionTableF

section defining

open BoundedSatisfactionTableF

noncomputable def boundedSatisfactionTable : 𝚫ᴬ₁.Semisentence 3 := .mkDelta
  (.mkSigma “q z e. !isMappingDef q ∧ !nodeDomDef q z e ∧
    (∀ z' < q, ∀ e' < q, !nodeDomDef q z' e' → !specDef.sigma q z' e') ∧
    (∀ n < q, !inDomDef q n → !minimalDef.sigma q z e n)”)
  (.mkPi “q z e. !isMappingDef q ∧ !nodeDomDef q z e ∧
    (∀ z' < q, ∀ e' < q, !nodeDomDef q z' e' → !specDef.pi q z' e') ∧
    (∀ n < q, !inDomDef q n → !minimalDef.pi q z e n)”)

instance BoundedSatisfactionTable.defined :
    𝚫ᴬ₁-Relation₃ (BoundedSatisfactionTable : V → V → V → Prop) via boundedSatisfactionTable :=
  .mk <| by
    constructor;
    · intro v;
      simp [boundedSatisfactionTable, HierarchySymbol.Semiformula.val_sigma, nodeDom_defined.df,
        inDom_defined.df];
    · intro v;
      simp [boundedSatisfactionTable, HierarchySymbol.Semiformula.val_sigma,
        boundedSatisfactionTable_iff, nodeDom_defined.df, inDom_defined.df];

instance BoundedSatisfactionTable.definable :
    𝚫ᴬ₁-Relation₃ (BoundedSatisfactionTable : V → V → V → Prop) :=
  BoundedSatisfactionTable.defined.to_definable

end defining

end table

end FFL.FirstOrder.Arithmetic.Bootstrapping
