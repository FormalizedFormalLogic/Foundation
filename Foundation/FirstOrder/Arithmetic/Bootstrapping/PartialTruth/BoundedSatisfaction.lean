module

public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Formula.Bounded
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.PartialTruth.TermVal
public import Foundation.FirstOrder.Arithmetic.HFS.Superexp
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.Bound

/-!
# Satisfaction for $\Delta_0$ formulas

`BoundedSatisfactionTable q z e` says that `q` is a finite satisfaction table for the coded
$\Delta_0$ formula `z` under the assignment `e`: a finite mapping from nodes `⟪p, e'⟫` to values
`0`, `1` that obeys a Tarski clause at every node of its domain and whose nodes all descend from
the root `⟪z, e⟫`. Tables are $\Delta_1$-definable and unique, and every well-formed $\Delta_0$
code has one under every assignment.

`BoundedSatisfaction z e` says that some table rooted at `⟪z, e⟫` gives it the value `1`. It is
$\Delta_1$-definable, satisfies Tarski's conditions, and commutes with negation and with
substitution of coded terms.

## References

- [HP98, 1.64, Lemma I.1.68(2), Theorem I.1.70, Definition I.1.71, Lemma I.1.72, Lemma I.1.73]
-/

@[expose] public section

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL.FirstOrder.Bounding (HierarchySymbol)

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Bounds on pairs, towers of exponentials and finite mappings -/

section generic

variable {a b c v x y m n q Q : V}

@[bound] lemma adjoin_le_exp_exp (ha : a ≤ c) (hv : v ≤ c) : a ∷ v ≤ Exp.exp (Exp.exp c) :=
  calc a ∷ v ≤ c ∷ c := adjoin_le_adjoin ha hv
    _ = (c + 1) * (c + 1) := by simp [adjoin_def, pair]; ring
    _ ≤ Exp.exp c * Exp.exp c := by gcongr <;> exact succ_le_iff_lt.mpr (lt_exp c)
    _ ≤ Exp.exp (Exp.exp c) := by rw [← exp_add]; bound

@[bound] lemma pair_lt_exp_exp (ha : a ≤ c) (hb : b ≤ c) : ⟪a, b⟫ < Exp.exp (Exp.exp c) :=
  (lt_add_one _).trans_le (adjoin_le_exp_exp ha hb)

@[bound] lemma pair_le_exp_exp (ha : a ≤ c) (hb : b ≤ c) : ⟪a, b⟫ ≤ Exp.exp (Exp.exp c) :=
  (pair_lt_exp_exp ha hb).le

lemma listMax_le_self (v : V) : listMax v ≤ v := by
  apply adjoin_induction 𝚷 (P := fun v ↦ listMax v ≤ v) (by definability) (by simp);
  intro x v ih;
  simpa using ⟨(lt_adjoin x v).le, ih.trans (lt_adjoin' x v).le⟩;

@[bound] lemma listMax_le_of_le (h : v ≤ c) : listMax v ≤ c := (listMax_le_self v).trans h

lemma le_iterExp (x n : V) : x ≤ iterExp x n := by
  apply ISigma1.sigma1_succ_induction (P := fun n ↦ x ≤ iterExp x n) (by definability) (by simp);
  intro n ih;
  simpa using le_exp_of_le ih;

lemma iterExp_add (x m n : V) : iterExp x (m + n) = iterExp (iterExp x m) n := by
  apply ISigma1.sigma1_succ_induction (P := fun n ↦ iterExp x (m + n) = iterExp (iterExp x m) n)
    (by definability) (by simp);
  intro n ih;
  rw [← add_assoc, iterExp_succ, ih, iterExp_succ];

@[gcongr] lemma iterExp_le_iterExp (hxy : x ≤ y) (hmn : m ≤ n) : iterExp x m ≤ iterExp y n := by
  have : iterExp x m ≤ iterExp y m := by
    apply ISigma1.sigma1_succ_induction (P := fun m ↦ iterExp x m ≤ iterExp y m)
      (by definability) (by simpa using hxy);
    intro m ih;
    simpa using ih;
  obtain ⟨k, rfl⟩ := le_iff_exists_add.mp hmn;
  exact this.trans (by simpa [iterExp_add] using le_iterExp (iterExp y m) k);

lemma iterExp_natCast (x : V) (k : ℕ) : iterExp x k = Exp.exp^[k] x := by
  induction k with
  | zero => simp;
  | succ k ih => simp [Function.iterate_succ_apply', ih];

@[simp] lemma iterExp_ofNat (x : V) (k : ℕ) [k.AtLeastTwo] :
    iterExp x (no_index (OfNat.ofNat k : V)) = Exp.exp^[k] x :=
  iterExp_natCast x k

lemma lt_of_mem_domain (h : n ∈ domain q) : n < q := by
  obtain ⟨y, hy⟩ := mem_domain_iff.mp h;
  exact lt_of_mem_dom hy;

lemma fst_lt_of_mem_domain {p e : V} (h : ⟪p, e⟫ ∈ domain q) : p < q :=
  (le_pair_left p e).trans_lt (lt_of_mem_domain h)

lemma snd_lt_of_mem_domain {p e : V} (h : ⟪p, e⟫ ∈ domain q) : e < q :=
  (le_pair_right p e).trans_lt (lt_of_mem_domain h)

lemma val_iff_of_subset (hQ : IsMapping Q) (hsub : q ⊆ Q) (hn : n ∈ domain q) :
    ⟪n, v⟫ ∈ Q ↔ ⟪n, v⟫ ∈ q := by
  obtain ⟨w, hw⟩ := mem_domain_iff.mp hn;
  exact ⟨fun h ↦ hQ.uniq (hsub hw) h ▸ hw, fun h ↦ hsub h⟩;

lemma mem_insert_iff_of_not_mem_domain (hn : n ∉ domain q) :
    ⟪n, y⟫ ∈ insert ⟪n, v⟫ q ↔ y = v := by
  simpa using fun h ↦ absurd (mem_domain_of_pair_mem h) hn;

/-- Descending induction on the first components of the elements of a domain. -/
lemma forall_mem_domain_of_desc {P : V → Prop} (hP : 𝚷ᴬ₁.DefinablePred P)
    (H : ∀ n ∈ domain q, (∀ m ∈ domain q, π₁ n < π₁ m → P m) → P n) : ∀ n ∈ domain q, P n := by
  suffices ∀ k n, n ∈ domain q → q ≤ π₁ n + k → P n from fun n hn ↦ this q n hn le_add_self;
  apply ISigma1.pi1_succ_induction (P := fun k ↦ ∀ n, n ∈ domain q → q ≤ π₁ n + k → P n)
    (by definability);
  · intro n hn hle;
    exact absurd ((pi₁_le_self n).trans_lt (lt_of_mem_domain hn)) (by simpa using hle);
  · intro k IH n hn hle;
    exact H n hn fun m hm hlt ↦ IH m hm <|
      calc q ≤ π₁ n + (k + 1) := hle
        _ = π₁ n + 1 + k := by ring
        _ ≤ π₁ m + k := by gcongr; exact succ_le_iff_lt.mpr hlt

end generic

/-! ## Coded atomic and bounded formulas -/

section codedSyntax

open Arithmetic (qqEQ qqNEQ qqLT qqNLT)

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

lemma coe_quote_eq : (⌜(Language.Eq.eq : (ℒₒᵣ).Rel 2)⌝ : V) = 0 := coe_eqIndex_eq

lemma coe_quote_lt : (⌜(Language.LT.lt : (ℒₒᵣ).Rel 2)⌝ : V) = 1 := coe_ltIndex_eq

@[simp] lemma isRel_two_zero : (ℒₒᵣ).IsRel (2 : V) 0 := by
  simpa using Arithmetic.LOR_rel_eqIndex (V := V);

@[simp] lemma isRel_two_one : (ℒₒᵣ).IsRel (2 : V) 1 := by
  simpa using Arithmetic.LOR_rel_ltIndex (V := V);

lemma rel_cases {k r v : V} (h : IsUFormula ℒₒᵣ (^rel k r v)) :
    (∃ t u, IsUTerm ℒₒᵣ t ∧ IsUTerm ℒₒᵣ u ∧ ^rel k r v = t ^= u) ∨
    (∃ t u, IsUTerm ℒₒᵣ t ∧ IsUTerm ℒₒᵣ u ∧ ^rel k r v = t ^< u) := by
  obtain ⟨hr, hv⟩ := IsUFormula.rel.mp h;
  rcases Arithmetic.isRel_iff_LOR.mp hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    obtain ⟨a, b, ha, hb, rfl⟩ := IsUTermVec.two_iff.mp hv;
  · left;
    exact ⟨a, b, ha, hb, by rw [qqEQ, coe_quote_eq, coe_eqIndex_eq]⟩;
  · right;
    exact ⟨a, b, ha, hb, by rw [qqLT, coe_quote_lt, coe_ltIndex_eq]⟩;

lemma nrel_cases {k r v : V} (h : IsUFormula ℒₒᵣ (^nrel k r v)) :
    (∃ t u, IsUTerm ℒₒᵣ t ∧ IsUTerm ℒₒᵣ u ∧ ^nrel k r v = t ^≠ u) ∨
    (∃ t u, IsUTerm ℒₒᵣ t ∧ IsUTerm ℒₒᵣ u ∧ ^nrel k r v = t ^≮ u) := by
  obtain ⟨hr, hv⟩ := IsUFormula.nrel.mp h;
  rcases Arithmetic.isRel_iff_LOR.mp hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    obtain ⟨a, b, ha, hb, rfl⟩ := IsUTermVec.two_iff.mp hv;
  · left;
    exact ⟨a, b, ha, hb, by rw [qqNEQ, coe_quote_eq, coe_eqIndex_eq]⟩;
  · right;
    exact ⟨a, b, ha, hb, by rw [qqNLT, coe_quote_lt, coe_ltIndex_eq]⟩;

lemma IsBounded.of_qqBex {u p : V} (h : IsBounded (qqBex u p)) : IsBounded p := by
  obtain ⟨u', q', -, hq', heq⟩ := IsBounded.of_ex (p := (qqLT (qqBvar 0) u) ^⋏ p) h;
  obtain ⟨-, rfl⟩ := (qqAnd_inj _ _ _ _).mp heq;
  exact hq';

variable {n m w t u p : V}

lemma isSemiterm_of_termBShift (ht : IsUTerm ℒₒᵣ t)
    (h : IsSemiterm ℒₒᵣ (n + 1) (termBShift ℒₒᵣ t)) : IsSemiterm ℒₒᵣ n t :=
  IsSemiterm.def.mpr ⟨ht, (termBV_termBShift_le ht n).mp (IsSemiterm.def.mp h).2⟩

lemma isSemiformula_qqBall (ht : IsUTerm ℒₒᵣ t)
    (h : IsSemiformula ℒₒᵣ n (qqBall (termBShift ℒₒᵣ t) p)) :
    IsSemiterm ℒₒᵣ n t ∧ IsSemiformula ℒₒᵣ (n + 1) p := by
  obtain ⟨h₁, h₂⟩ : IsSemiterm ℒₒᵣ (n + 1) (termBShift ℒₒᵣ t) ∧ IsSemiformula ℒₒᵣ (n + 1) p := by
    simpa [qqBall, qqNLT] using h;
  exact ⟨isSemiterm_of_termBShift ht h₁, h₂⟩;

lemma isSemiformula_qqBex (ht : IsUTerm ℒₒᵣ t)
    (h : IsSemiformula ℒₒᵣ n (qqBex (termBShift ℒₒᵣ t) p)) :
    IsSemiterm ℒₒᵣ n t ∧ IsSemiformula ℒₒᵣ (n + 1) p := by
  obtain ⟨h₁, h₂⟩ : IsSemiterm ℒₒᵣ (n + 1) (termBShift ℒₒᵣ t) ∧ IsSemiformula ℒₒᵣ (n + 1) p := by
    simpa [qqBex, qqLT] using h;
  exact ⟨isSemiterm_of_termBShift ht h₁, h₂⟩;

section
variable (ht : IsUTerm ℒₒᵣ t) (hu : IsUTerm ℒₒᵣ u)
include ht hu

lemma substs_qqEQ :
    Bootstrapping.subst ℒₒᵣ w (t ^= u) = termSubst ℒₒᵣ w t ^= termSubst ℒₒᵣ w u := by
  simp [qqEQ, ht, hu];

lemma substs_qqNEQ :
    Bootstrapping.subst ℒₒᵣ w (t ^≠ u) = termSubst ℒₒᵣ w t ^≠ termSubst ℒₒᵣ w u := by
  simp [qqNEQ, ht, hu];

lemma substs_qqLT :
    Bootstrapping.subst ℒₒᵣ w (t ^< u) = termSubst ℒₒᵣ w t ^< termSubst ℒₒᵣ w u := by
  simp [qqLT, ht, hu];

lemma substs_qqNLT :
    Bootstrapping.subst ℒₒᵣ w (t ^≮ u) = termSubst ℒₒᵣ w t ^≮ termSubst ℒₒᵣ w u := by
  simp [qqNLT, ht, hu];

end

section
variable (hw : IsSemitermVec ℒₒᵣ n m w) (ht : IsSemiterm ℒₒᵣ n t) (hp : IsUFormula ℒₒᵣ p)
include hw ht hp

lemma substs_qqBall :
    Bootstrapping.subst ℒₒᵣ w (qqBall (termBShift ℒₒᵣ t) p) =
      qqBall (termBShift ℒₒᵣ (termSubst ℒₒᵣ w t)) (Bootstrapping.subst ℒₒᵣ (qVec ℒₒᵣ w) p) := by
  have hbt : IsUTerm ℒₒᵣ (termBShift ℒₒᵣ t) := ht.isUTerm.termBShift;
  have hlt : IsUFormula ℒₒᵣ ((qqBvar 0 : V) ^≮ termBShift ℒₒᵣ t) := by simp [qqNLT, hbt];
  rw [show qqBall (termBShift ℒₒᵣ t) p = ^∀ ((qqBvar 0 ^≮ termBShift ℒₒᵣ t) ^⋎ p) from rfl,
    substs_all (by simp [hlt, hp]), substs_or hlt hp, substs_qqNLT (by simp) hbt,
    substs_qVec_bShift ht hw];
  simp [qVec, qqBall];

lemma substs_qqBex :
    Bootstrapping.subst ℒₒᵣ w (qqBex (termBShift ℒₒᵣ t) p) =
      qqBex (termBShift ℒₒᵣ (termSubst ℒₒᵣ w t)) (Bootstrapping.subst ℒₒᵣ (qVec ℒₒᵣ w) p) := by
  have hbt : IsUTerm ℒₒᵣ (termBShift ℒₒᵣ t) := ht.isUTerm.termBShift;
  have hlt : IsUFormula ℒₒᵣ ((qqBvar 0 : V) ^< termBShift ℒₒᵣ t) := by simp [qqLT, hbt];
  rw [show qqBex (termBShift ℒₒᵣ t) p = ^∃ ((qqBvar 0 ^< termBShift ℒₒᵣ t) ^⋏ p) from rfl,
    substs_ex (by simp [hlt, hp]), substs_and hlt hp, substs_qqLT (by simp) hbt,
    substs_qVec_bShift ht hw];
  simp [qVec, qqBex];

end

lemma IsBounded.subst (hw : IsSemitermVec ℒₒᵣ n m w) (hp : IsSemiformula ℒₒᵣ n p)
    (h : IsBounded p) : IsBounded (Bootstrapping.subst ℒₒᵣ w p) := by
  revert n m w;
  apply IsBounded.induction 𝚷 (P := fun p ↦ ∀ n m w, IsSemitermVec ℒₒᵣ n m w →
    IsSemiformula ℒₒᵣ n p → IsBounded (Bootstrapping.subst ℒₒᵣ w p)) (by definability)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p h;
  · simp;
  · simp;
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
    exact IsBounded.ball (hw.termSubst ht').isUTerm (ih _ _ _ hw.qVec hq);
  · intro t q ht _ ih n m w hw hpq;
    obtain ⟨ht', hq⟩ := isSemiformula_qqBex ht hpq;
    rw [substs_qqBex hw ht' hq.isUFormula];
    exact IsBounded.bex (hw.termSubst ht').isUTerm (ih _ _ _ hw.qVec hq);

end codedSyntax

/-! ## Satisfaction tables -/

namespace BoundedSatisfactionTable

def Spec (q z e : V) : Prop := (z = ^⊤ ∧ ⟪⟪z, e⟫, 1⟫ ∈ q) ∨ (z = ^⊥ ∧ ⟪⟪z, e⟫, 0⟫ ∈ q) ∨
  (∃ t u, IsUTerm ℒₒᵣ t ∧ IsUTerm ℒₒᵣ u ∧ z = t ^= u ∧
    (⟪⟪z, e⟫, 1⟫ ∈ q ↔ termVal e t = termVal e u) ∧
    (⟪⟪z, e⟫, 0⟫ ∈ q ↔ termVal e t ≠ termVal e u)) ∨
  (∃ t u, IsUTerm ℒₒᵣ t ∧ IsUTerm ℒₒᵣ u ∧ z = t ^≠ u ∧
    (⟪⟪z, e⟫, 1⟫ ∈ q ↔ termVal e t ≠ termVal e u) ∧
    (⟪⟪z, e⟫, 0⟫ ∈ q ↔ termVal e t = termVal e u)) ∨
  (∃ t u, IsUTerm ℒₒᵣ t ∧ IsUTerm ℒₒᵣ u ∧ z = t ^< u ∧
    (⟪⟪z, e⟫, 1⟫ ∈ q ↔ termVal e t < termVal e u) ∧
    (⟪⟪z, e⟫, 0⟫ ∈ q ↔ ¬termVal e t < termVal e u)) ∨
  (∃ t u, IsUTerm ℒₒᵣ t ∧ IsUTerm ℒₒᵣ u ∧ z = t ^≮ u ∧
    (⟪⟪z, e⟫, 1⟫ ∈ q ↔ ¬termVal e t < termVal e u) ∧
    (⟪⟪z, e⟫, 0⟫ ∈ q ↔ termVal e t < termVal e u)) ∨
  (∃ p₁ p₂, z = p₁ ^⋏ p₂ ∧ ⟪p₁, e⟫ ∈ domain q ∧ ⟪p₂, e⟫ ∈ domain q ∧
    (⟪⟪z, e⟫, 1⟫ ∈ q ↔ ⟪⟪p₁, e⟫, 1⟫ ∈ q ∧ ⟪⟪p₂, e⟫, 1⟫ ∈ q) ∧
    (⟪⟪z, e⟫, 0⟫ ∈ q ↔ ⟪⟪p₁, e⟫, 0⟫ ∈ q ∨ ⟪⟪p₂, e⟫, 0⟫ ∈ q)) ∨
  (∃ p₁ p₂, z = p₁ ^⋎ p₂ ∧ ⟪p₁, e⟫ ∈ domain q ∧ ⟪p₂, e⟫ ∈ domain q ∧
    (⟪⟪z, e⟫, 1⟫ ∈ q ↔ ⟪⟪p₁, e⟫, 1⟫ ∈ q ∨ ⟪⟪p₂, e⟫, 1⟫ ∈ q) ∧
    (⟪⟪z, e⟫, 0⟫ ∈ q ↔ ⟪⟪p₁, e⟫, 0⟫ ∈ q ∧ ⟪⟪p₂, e⟫, 0⟫ ∈ q)) ∨
  (∃ u p, (∃ t, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧ z = qqBall u p ∧
    (∀ x < termVal (0 ∷ e) u, ⟪p, x ∷ e⟫ ∈ domain q) ∧
    (⟪⟪z, e⟫, 1⟫ ∈ q ↔ ∀ x < termVal (0 ∷ e) u, ⟪⟪p, x ∷ e⟫, 1⟫ ∈ q) ∧
    (⟪⟪z, e⟫, 0⟫ ∈ q ↔ ∃ x < termVal (0 ∷ e) u, ⟪⟪p, x ∷ e⟫, 0⟫ ∈ q)) ∨
  (∃ u p, (∃ t, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t) ∧ z = qqBex u p ∧
    (∀ x < termVal (0 ∷ e) u, ⟪p, x ∷ e⟫ ∈ domain q) ∧
    (⟪⟪z, e⟫, 1⟫ ∈ q ↔ ∃ x < termVal (0 ∷ e) u, ⟪⟪p, x ∷ e⟫, 1⟫ ∈ q) ∧
    (⟪⟪z, e⟫, 0⟫ ∈ q ↔ ∀ x < termVal (0 ∷ e) u, ⟪⟪p, x ∷ e⟫, 0⟫ ∈ q))

def MinChild (q n : V) : Prop :=
  (∃ p₁ p₂ e, ⟪p₁ ^⋏ p₂, e⟫ ∈ domain q ∧ (n = ⟪p₁, e⟫ ∨ n = ⟪p₂, e⟫)) ∨
  (∃ p₁ p₂ e, ⟪p₁ ^⋎ p₂, e⟫ ∈ domain q ∧ (n = ⟪p₁, e⟫ ∨ n = ⟪p₂, e⟫)) ∨
  (∃ u p e, ⟪qqBall u p, e⟫ ∈ domain q ∧ ∃ x < termVal (0 ∷ e) u, n = ⟪p, x ∷ e⟫) ∨
  (∃ u p e, ⟪qqBex u p, e⟫ ∈ domain q ∧ ∃ x < termVal (0 ∷ e) u, n = ⟪p, x ∷ e⟫)

end BoundedSatisfactionTable

open BoundedSatisfactionTable (Spec MinChild) in
structure BoundedSatisfactionTable (q z e : V) : Prop where
  isMapping : IsMapping q
  mem_dom_root : ⟪z, e⟫ ∈ domain q
  spec : ∀ z' e', ⟪z', e'⟫ ∈ domain q → Spec q z' e'
  minimal : ∀ n ∈ domain q, n = ⟪z, e⟫ ∨ MinChild q n

namespace BoundedSatisfactionTable

/-! ### Reading off the Tarski clause at a node of known shape -/

section reading

-- Unfolding the coding operations to their underlying pairs is what tells two differently-shaped
-- codes apart when `Spec` is read off at a node. Scoped to this section, since unconditionally
-- unfolding these constructors defeats the ordinary simp set on coded formulas.
attribute [local simp] qqAnd qqOr qqVerum qqFalsum qqRel qqNRel qqBall qqAll qqBex qqExs
  Arithmetic.qqEQ Arithmetic.qqNEQ Arithmetic.qqLT Arithmetic.qqNLT

variable {q z e e' t u p p₁ p₂ : V} (h : BoundedSatisfactionTable q z e)
include h

lemma val_verum (hn : ⟪(^⊤ : V), e'⟫ ∈ domain q) : ⟪⟪(^⊤ : V), e'⟫, 1⟫ ∈ q := by
  simpa [Spec] using h.spec _ e' hn;

lemma val_falsum (hn : ⟪(^⊥ : V), e'⟫ ∈ domain q) : ⟪⟪(^⊥ : V), e'⟫, 0⟫ ∈ q := by
  simpa [Spec] using h.spec _ e' hn;

lemma spec_eq (hn : ⟪t ^= u, e'⟫ ∈ domain q) :
    (⟪⟪t ^= u, e'⟫, 1⟫ ∈ q ↔ termVal e' t = termVal e' u) ∧
    (⟪⟪t ^= u, e'⟫, 0⟫ ∈ q ↔ termVal e' t ≠ termVal e' u) := by
  have := h.spec _ e' hn;
  simp_all [Spec];

lemma spec_neq (hn : ⟪t ^≠ u, e'⟫ ∈ domain q) :
    (⟪⟪t ^≠ u, e'⟫, 1⟫ ∈ q ↔ termVal e' t ≠ termVal e' u) ∧
    (⟪⟪t ^≠ u, e'⟫, 0⟫ ∈ q ↔ termVal e' t = termVal e' u) := by
  have := h.spec _ e' hn;
  simp_all [Spec];

lemma spec_lt (hn : ⟪t ^< u, e'⟫ ∈ domain q) :
    (⟪⟪t ^< u, e'⟫, 1⟫ ∈ q ↔ termVal e' t < termVal e' u) ∧
    (⟪⟪t ^< u, e'⟫, 0⟫ ∈ q ↔ ¬termVal e' t < termVal e' u) := by
  have := h.spec _ e' hn;
  simp_all [Spec];

lemma spec_nlt (hn : ⟪t ^≮ u, e'⟫ ∈ domain q) :
    (⟪⟪t ^≮ u, e'⟫, 1⟫ ∈ q ↔ ¬termVal e' t < termVal e' u) ∧
    (⟪⟪t ^≮ u, e'⟫, 0⟫ ∈ q ↔ termVal e' t < termVal e' u) := by
  have := h.spec _ e' hn;
  simp_all [Spec];

lemma spec_and (hn : ⟪p₁ ^⋏ p₂, e'⟫ ∈ domain q) :
    ⟪p₁, e'⟫ ∈ domain q ∧ ⟪p₂, e'⟫ ∈ domain q ∧
    (⟪⟪p₁ ^⋏ p₂, e'⟫, 1⟫ ∈ q ↔ ⟪⟪p₁, e'⟫, 1⟫ ∈ q ∧ ⟪⟪p₂, e'⟫, 1⟫ ∈ q) ∧
    (⟪⟪p₁ ^⋏ p₂, e'⟫, 0⟫ ∈ q ↔ ⟪⟪p₁, e'⟫, 0⟫ ∈ q ∨ ⟪⟪p₂, e'⟫, 0⟫ ∈ q) := by
  simpa [Spec] using h.spec _ e' hn;

lemma spec_or (hn : ⟪p₁ ^⋎ p₂, e'⟫ ∈ domain q) :
    ⟪p₁, e'⟫ ∈ domain q ∧ ⟪p₂, e'⟫ ∈ domain q ∧
    (⟪⟪p₁ ^⋎ p₂, e'⟫, 1⟫ ∈ q ↔ ⟪⟪p₁, e'⟫, 1⟫ ∈ q ∨ ⟪⟪p₂, e'⟫, 1⟫ ∈ q) ∧
    (⟪⟪p₁ ^⋎ p₂, e'⟫, 0⟫ ∈ q ↔ ⟪⟪p₁, e'⟫, 0⟫ ∈ q ∧ ⟪⟪p₂, e'⟫, 0⟫ ∈ q) := by
  simpa [Spec] using h.spec _ e' hn;

lemma spec_ball (hn : ⟪qqBall u p, e'⟫ ∈ domain q) :
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
    simpa [Spec] using h.spec _ e' hn;
  exact ⟨⟨t, ht, rfl⟩, hd, hA, hB⟩;

lemma spec_bex (hn : ⟪qqBex u p, e'⟫ ∈ domain q) :
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
    simpa [Spec] using h.spec _ e' hn;
  exact ⟨⟨t, ht, rfl⟩, hd, hA, hB⟩;

end reading

/-! ### The Tarski clauses in the form used by the satisfaction predicate -/

variable {q z e e' t u p p₁ p₂ : V} (h : BoundedSatisfactionTable q z e)
include h

lemma val_eq (hn : ⟪t ^= u, e'⟫ ∈ domain q) :
    ⟪⟪t ^= u, e'⟫, 1⟫ ∈ q ↔ termVal e' t = termVal e' u := (h.spec_eq hn).1

lemma val_neq (hn : ⟪t ^≠ u, e'⟫ ∈ domain q) :
    ⟪⟪t ^≠ u, e'⟫, 1⟫ ∈ q ↔ termVal e' t ≠ termVal e' u := (h.spec_neq hn).1

lemma val_lt (hn : ⟪t ^< u, e'⟫ ∈ domain q) :
    ⟪⟪t ^< u, e'⟫, 1⟫ ∈ q ↔ termVal e' t < termVal e' u := (h.spec_lt hn).1

lemma val_nlt (hn : ⟪t ^≮ u, e'⟫ ∈ domain q) :
    ⟪⟪t ^≮ u, e'⟫, 1⟫ ∈ q ↔ ¬termVal e' t < termVal e' u := (h.spec_nlt hn).1

lemma mem_dom_and (hn : ⟪p₁ ^⋏ p₂, e'⟫ ∈ domain q) :
    ⟪p₁, e'⟫ ∈ domain q ∧ ⟪p₂, e'⟫ ∈ domain q :=
  ⟨(h.spec_and hn).1, (h.spec_and hn).2.1⟩

lemma val_and (hn : ⟪p₁ ^⋏ p₂, e'⟫ ∈ domain q) :
    ⟪⟪p₁ ^⋏ p₂, e'⟫, 1⟫ ∈ q ↔ ⟪⟪p₁, e'⟫, 1⟫ ∈ q ∧ ⟪⟪p₂, e'⟫, 1⟫ ∈ q := (h.spec_and hn).2.2.1

lemma mem_dom_or (hn : ⟪p₁ ^⋎ p₂, e'⟫ ∈ domain q) :
    ⟪p₁, e'⟫ ∈ domain q ∧ ⟪p₂, e'⟫ ∈ domain q :=
  ⟨(h.spec_or hn).1, (h.spec_or hn).2.1⟩

lemma val_or (hn : ⟪p₁ ^⋎ p₂, e'⟫ ∈ domain q) :
    ⟪⟪p₁ ^⋎ p₂, e'⟫, 1⟫ ∈ q ↔ ⟪⟪p₁, e'⟫, 1⟫ ∈ q ∨ ⟪⟪p₂, e'⟫, 1⟫ ∈ q := (h.spec_or hn).2.2.1

section
variable (ht : IsUTerm ℒₒᵣ t)
include ht

lemma mem_dom_ball (hn : ⟪qqBall (termBShift ℒₒᵣ t) p, e'⟫ ∈ domain q) {x : V}
    (hx : x < termVal e' t) : ⟪p, x ∷ e'⟫ ∈ domain q :=
  (h.spec_ball hn).2.1 x (by rwa [termVal_termBShift ht])

lemma val_ball (hn : ⟪qqBall (termBShift ℒₒᵣ t) p, e'⟫ ∈ domain q) :
    ⟪⟪qqBall (termBShift ℒₒᵣ t) p, e'⟫, 1⟫ ∈ q ↔ ∀ x < termVal e' t, ⟪⟪p, x ∷ e'⟫, 1⟫ ∈ q := by
  simpa [termVal_termBShift ht] using (h.spec_ball hn).2.2.1;

lemma mem_dom_bex (hn : ⟪qqBex (termBShift ℒₒᵣ t) p, e'⟫ ∈ domain q) {x : V}
    (hx : x < termVal e' t) : ⟪p, x ∷ e'⟫ ∈ domain q :=
  (h.spec_bex hn).2.1 x (by rwa [termVal_termBShift ht])

lemma val_bex (hn : ⟪qqBex (termBShift ℒₒᵣ t) p, e'⟫ ∈ domain q) :
    ⟪⟪qqBex (termBShift ℒₒᵣ t) p, e'⟫, 1⟫ ∈ q ↔ ∃ x < termVal e' t, ⟪⟪p, x ∷ e'⟫, 1⟫ ∈ q := by
  simpa [termVal_termBShift ht] using (h.spec_bex hn).2.2.1;

end

end BoundedSatisfactionTable

/-! ## Definability of tables

Each clause of `spec` and `minimal` gets a bounded `Prop` with a defining formula. Where a clause
mentions `termVal`, whose graph is $\Sigma_1$, the value is hoisted out by an existential on the
$\Sigma_1$ side and by a universal on the $\Pi_1$ side. -/

namespace BoundedSatisfactionTableF

open Arithmetic (qqEQ_defined qqNEQ_defined qqLT_defined qqNLT_defined)

/-! ### Nodes and values as $\Sigma_0$ relations -/

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

/-! ### The ten Tarski clauses -/

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

/-! ### The clause of `BoundedSatisfactionTable.spec`, assembled -/

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

/-! ### The clause of `BoundedSatisfactionTable.minimal` -/

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

/-! ### Assembling the definition -/

open BoundedSatisfactionTable (Spec MinChild)

variable {q z e n : V}

lemma specAt_iff : SpecAt q z e ↔ Spec q z e := by
  unfold SpecAt Spec;
  constructor;
  · rintro (h | h | ⟨t, -, u, -, h⟩ | ⟨t, -, u, -, h⟩ | ⟨t, -, u, -, h⟩ | ⟨t, -, u, -, h⟩ |
      ⟨p₁, -, p₂, -, h⟩ | ⟨p₁, -, p₂, -, h⟩ | ⟨u, -, p, -, ⟨t, -, ht⟩, h⟩ |
      ⟨u, -, p, -, ⟨t, -, ht⟩, h⟩);
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
  · rintro (h | h | ⟨t, u, ht, hu, rfl, h⟩ | ⟨t, u, ht, hu, rfl, h⟩ | ⟨t, u, ht, hu, rfl, h⟩ |
      ⟨t, u, ht, hu, rfl, h⟩ | ⟨p₁, p₂, rfl, h⟩ | ⟨p₁, p₂, rfl, h⟩ | ⟨_, p, ⟨t, ht, rfl⟩, rfl, h⟩ |
      ⟨_, p, ⟨t, ht, rfl⟩, rfl, h⟩);
    · disj 1; exact h;
    · disj 2; exact h;
    · disj 3; exact ⟨t, by simp, u, by simp, ht, hu, rfl, h⟩;
    · disj 4; exact ⟨t, by simp, u, by simp, ht, hu, rfl, h⟩;
    · disj 5; exact ⟨t, by simp, u, by simp, ht, hu, rfl, h⟩;
    · disj 6; exact ⟨t, by simp, u, by simp, ht, hu, rfl, h⟩;
    · disj 7; exact ⟨p₁, by simp, p₂, by simp, rfl, h⟩;
    · disj 8; exact ⟨p₁, by simp, p₂, by simp, rfl, h⟩;
    · disj 9; exact ⟨_, by simp, p, by simp, ⟨t, le_termBShift ht, ht, rfl⟩, rfl, h⟩;
    · disj 10; exact ⟨_, by simp, p, by simp, ⟨t, le_termBShift ht, ht, rfl⟩, rfl, h⟩;

lemma minimalAt_iff : MinimalAt q z e n ↔ n = ⟪z, e⟫ ∨ MinChild q n := by
  unfold MinimalAt MinChild;
  constructor;
  · rintro (h | ⟨_, -, p₁, -, p₂, -, e', -, rfl, h⟩ | ⟨_, -, p₁, -, p₂, -, e', -, rfl, h⟩ |
      ⟨_, -, u, -, p, -, e', -, rfl, h⟩ | ⟨_, -, u, -, p, -, e', -, rfl, h⟩);
    · disj 1; exact h;
    · disj 2; exact ⟨p₁, p₂, e', h⟩;
    · disj 3; exact ⟨p₁, p₂, e', h⟩;
    · disj 4; exact ⟨u, p, e', h⟩;
    · disj 5; exact ⟨u, p, e', h⟩;
  · rintro (h | ⟨p₁, p₂, e', hd, h⟩ | ⟨p₁, p₂, e', hd, h⟩ | ⟨u, p, e', hd, h⟩ | ⟨u, p, e', hd, h⟩);
    · disj 1; exact h;
    · disj 2;
      exact ⟨_, fst_lt_of_mem_domain hd, p₁, by simp, p₂, by simp, e', snd_lt_of_mem_domain hd,
        rfl, hd, h⟩;
    · disj 3;
      exact ⟨_, fst_lt_of_mem_domain hd, p₁, by simp, p₂, by simp, e', snd_lt_of_mem_domain hd,
        rfl, hd, h⟩;
    · disj 4;
      exact ⟨_, fst_lt_of_mem_domain hd, u, by simp, p, by simp, e', snd_lt_of_mem_domain hd,
        rfl, hd, h⟩;
    · disj 5;
      exact ⟨_, fst_lt_of_mem_domain hd, u, by simp, p, by simp, e', snd_lt_of_mem_domain hd,
        rfl, hd, h⟩;

lemma boundedSatisfactionTable_iff : BoundedSatisfactionTable q z e ↔ IsMapping q ∧
    ⟪z, e⟫ ∈ domain q ∧
    (∀ z' < q, ∀ e' < q, ⟪z', e'⟫ ∈ domain q → SpecAt q z' e') ∧
    (∀ n < q, n ∈ domain q → MinimalAt q z e n) := by
  constructor;
  · rintro ⟨hm, hr, hs, hmin⟩;
    exact ⟨hm, hr, fun z' _ e' _ hd ↦ specAt_iff.mpr (hs z' e' hd),
      fun n _ hn ↦ minimalAt_iff.mpr (hmin n hn)⟩;
  · rintro ⟨hm, hr, hs, hmin⟩;
    exact ⟨hm, hr,
      fun z' e' hd ↦
        specAt_iff.mp (hs z' (fst_lt_of_mem_domain hd) e' (snd_lt_of_mem_domain hd) hd),
      fun n hn ↦ minimalAt_iff.mp (hmin n (lt_of_mem_domain hn) hn)⟩;

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
  .mk ⟨fun v ↦ by
      simp [boundedSatisfactionTable, HierarchySymbol.Semiformula.val_sigma, nodeDom_defined.df,
        inDom_defined.df],
    fun v ↦ by
      simp [boundedSatisfactionTable, HierarchySymbol.Semiformula.val_sigma,
        boundedSatisfactionTable_iff, nodeDom_defined.df, inDom_defined.df]⟩

instance BoundedSatisfactionTable.definable :
    𝚫ᴬ₁-Relation₃ (BoundedSatisfactionTable : V → V → V → Prop) :=
  BoundedSatisfactionTable.defined.to_definable

end defining

/-! ## Uniqueness and existence of tables -/

namespace BoundedSatisfactionTable

variable {q q₁ q₂ r z z₁ z₂ e e₁ e₂ e' n p p₁ p₂ u : V}

/-! ### Values and uniqueness -/

lemma val_one_ne_zero (h : BoundedSatisfactionTable q z e) (h1 : ⟪n, 1⟫ ∈ q) (h0 : ⟪n, 0⟫ ∈ q) :
    False := by
  simpa using h.isMapping.uniq h1 h0;

lemma val_zero_or_one (h : BoundedSatisfactionTable q z e) :
    ∀ p e', ⟪p, e'⟫ ∈ domain q → ⟪⟪p, e'⟫, 1⟫ ∈ q ∨ ⟪⟪p, e'⟫, 0⟫ ∈ q := by
  apply ISigma1.pi1_order_induction
    (P := fun p ↦ ∀ e', ⟪p, e'⟫ ∈ domain q → ⟪⟪p, e'⟫, 1⟫ ∈ q ∨ ⟪⟪p, e'⟫, 0⟫ ∈ q)
    (by definability);
  intro p ih e' hn;
  rcases h.spec _ e' hn with ⟨-, hv⟩ | ⟨-, hv⟩ | ⟨a, b, -, -, -, hA, hB⟩ | ⟨a, b, -, -, -, hA, hB⟩ |
    ⟨a, b, -, -, -, hA, hB⟩ | ⟨a, b, -, -, -, hA, hB⟩ | ⟨a, b, rfl, hd, hd', hA, hB⟩ |
    ⟨a, b, rfl, hd, hd', hA, hB⟩ | ⟨a, b, -, rfl, hd, hA, hB⟩ | ⟨a, b, -, rfl, hd, hA, hB⟩;
  · left; exact hv;
  · right; exact hv;
  · tauto;
  · tauto;
  · tauto;
  · tauto;
  · have := ih a (by simp) e' hd;
    have := ih b (by simp) e' hd';
    tauto;
  · have := ih a (by simp) e' hd;
    have := ih b (by simp) e' hd';
    tauto;
  · have hc := fun x hx ↦ ih b (by simp) (x ∷ e') (hd x hx);
    rw [hA, hB];
    by_contra! H;
    obtain ⟨x, hx, h1⟩ := H.1;
    exact (hc x hx).elim h1 (H.2 x hx);
  · have hc := fun x hx ↦ ih b (by simp) (x ∷ e') (hd x hx);
    rw [hA, hB];
    by_contra! H;
    obtain ⟨x, hx, h0⟩ := H.2;
    exact (hc x hx).elim (H.1 x hx) h0;

lemma val_zero_iff (h : BoundedSatisfactionTable q z e) (hn : ⟪p, e'⟫ ∈ domain q) :
    ⟪⟪p, e'⟫, 0⟫ ∈ q ↔ ⟪⟪p, e'⟫, 1⟫ ∉ q :=
  ⟨fun h0 h1 ↦ h.val_one_ne_zero h1 h0, (h.val_zero_or_one p e' hn).resolve_left⟩

lemma agree (h₁ : BoundedSatisfactionTable q₁ z₁ e₁) (h₂ : BoundedSatisfactionTable q₂ z₂ e₂) :
    ∀ p e', ⟪p, e'⟫ ∈ domain q₁ → ⟪p, e'⟫ ∈ domain q₂ → (⟪⟪p, e'⟫, 1⟫ ∈ q₁ ↔ ⟪⟪p, e'⟫, 1⟫ ∈ q₂) ∧
      (⟪⟪p, e'⟫, 0⟫ ∈ q₁ ↔ ⟪⟪p, e'⟫, 0⟫ ∈ q₂) := by
  apply ISigma1.pi1_order_induction
    (P := fun p ↦ ∀ e', ⟪p, e'⟫ ∈ domain q₁ → ⟪p, e'⟫ ∈ domain q₂ →
      (⟪⟪p, e'⟫, 1⟫ ∈ q₁ ↔ ⟪⟪p, e'⟫, 1⟫ ∈ q₂) ∧ (⟪⟪p, e'⟫, 0⟫ ∈ q₁ ↔ ⟪⟪p, e'⟫, 0⟫ ∈ q₂))
    (by definability);
  intro p ih e' hn₁ hn₂;
  rcases h₁.spec _ e' hn₁ with ⟨rfl, hv⟩ | ⟨rfl, hv⟩ | ⟨a, b, -, -, rfl, hA, hB⟩ |
    ⟨a, b, -, -, rfl, hA, hB⟩ | ⟨a, b, -, -, rfl, hA, hB⟩ | ⟨a, b, -, -, rfl, hA, hB⟩ |
    ⟨a, b, rfl, hd, hd', hA, hB⟩ | ⟨a, b, rfl, hd, hd', hA, hB⟩ | ⟨a, b, -, rfl, hd, hA, hB⟩ |
    ⟨a, b, -, rfl, hd, hA, hB⟩;
  · have hv₂ := h₂.val_verum hn₂;
    exact ⟨iff_of_true hv hv₂, iff_of_false (h₁.val_one_ne_zero hv) (h₂.val_one_ne_zero hv₂)⟩;
  · have hv₂ := h₂.val_falsum hn₂;
    exact ⟨iff_of_false (h₁.val_one_ne_zero · hv) (h₂.val_one_ne_zero · hv₂), iff_of_true hv hv₂⟩;
  · simp [hA, hB, h₂.spec_eq hn₂];
  · simp [hA, hB, h₂.spec_neq hn₂];
  · simp [hA, hB, h₂.spec_lt hn₂];
  · simp [hA, hB, h₂.spec_nlt hn₂];
  · obtain ⟨hd₂, hd₂', hA₂, hB₂⟩ := h₂.spec_and hn₂;
    obtain ⟨i1, i0⟩ := ih a (by simp) e' hd hd₂;
    obtain ⟨j1, j0⟩ := ih b (by simp) e' hd' hd₂';
    exact ⟨by rw [hA, hA₂, i1, j1], by rw [hB, hB₂, i0, j0]⟩;
  · obtain ⟨hd₂, hd₂', hA₂, hB₂⟩ := h₂.spec_or hn₂;
    obtain ⟨i1, i0⟩ := ih a (by simp) e' hd hd₂;
    obtain ⟨j1, j0⟩ := ih b (by simp) e' hd' hd₂';
    exact ⟨by rw [hA, hA₂, i1, j1], by rw [hB, hB₂, i0, j0]⟩;
  · obtain ⟨-, hd₂, hA₂, hB₂⟩ := h₂.spec_ball hn₂;
    have hc := fun x hx ↦ ih b (by simp) (x ∷ e') (hd x hx) (hd₂ x hx);
    rw [hA, hA₂, hB, hB₂];
    exact ⟨forall₂_congr fun x hx ↦ (hc x hx).1,
      exists_congr fun x ↦ and_congr_right fun hx ↦ (hc x hx).2⟩;
  · obtain ⟨-, hd₂, hA₂, hB₂⟩ := h₂.spec_bex hn₂;
    have hc := fun x hx ↦ ih b (by simp) (x ∷ e') (hd x hx) (hd₂ x hx);
    rw [hA, hA₂, hB, hB₂];
    exact ⟨exists_congr fun x ↦ and_congr_right fun hx ↦ (hc x hx).1,
      forall₂_congr fun x hx ↦ (hc x hx).2⟩;

lemma val_agree (h₁ : BoundedSatisfactionTable q₁ z₁ e₁) (h₂ : BoundedSatisfactionTable q₂ z₂ e₂)
    {y₁ y₂ : V} (hn₁ : ⟪n, y₁⟫ ∈ q₁) (hn₂ : ⟪n, y₂⟫ ∈ q₂) : y₁ = y₂ := by
  obtain ⟨p, e', rfl⟩ : ∃ p e', n = ⟪p, e'⟫ := ⟨π₁ n, π₂ n, by simp⟩;
  have hd₁ := mem_domain_of_pair_mem hn₁;
  obtain ⟨i1, i0⟩ := h₁.agree h₂ p e' hd₁ (mem_domain_of_pair_mem hn₂);
  rcases h₁.val_zero_or_one p e' hd₁ with h | h;
  · rw [h₁.isMapping.uniq hn₁ h, h₂.isMapping.uniq hn₂ (i1.mp h)];
  · rw [h₁.isMapping.uniq hn₁ h, h₂.isMapping.uniq hn₂ (i0.mp h)];

lemma dom_subset (h₁ : BoundedSatisfactionTable q₁ z e) (h₂ : BoundedSatisfactionTable q₂ z e) :
    ∀ n ∈ domain q₁, n ∈ domain q₂ := by
  apply forall_mem_domain_of_desc (P := fun n ↦ n ∈ domain q₂) (by definability);
  intro n hn IH;
  rcases h₁.minimal n hn with rfl | ⟨a, b, e', hm, rfl | rfl⟩ | ⟨a, b, e', hm, rfl | rfl⟩ |
    ⟨u, r, e', hm, x, hx, rfl⟩ | ⟨u, r, e', hm, x, hx, rfl⟩;
  · exact h₂.mem_dom_root;
  · exact (h₂.mem_dom_and (IH _ hm (by simp))).1;
  · exact (h₂.mem_dom_and (IH _ hm (by simp))).2;
  · exact (h₂.mem_dom_or (IH _ hm (by simp))).1;
  · exact (h₂.mem_dom_or (IH _ hm (by simp))).2;
  · exact (h₂.spec_ball (IH _ hm (by simp))).2.1 x hx;
  · exact (h₂.spec_bex (IH _ hm (by simp))).2.1 x hx;

theorem uniq (h₁ : BoundedSatisfactionTable q₁ z e) (h₂ : BoundedSatisfactionTable q₂ z e) :
    q₁ = q₂ := by
  have sub : ∀ {r₁ r₂ : V}, BoundedSatisfactionTable r₁ z e → BoundedSatisfactionTable r₂ z e →
      ∀ x ∈ r₁, x ∈ r₂ := by
    intro r₁ r₂ k₁ k₂ x hx;
    obtain ⟨n, y, rfl⟩ : ∃ n y, x = ⟪n, y⟫ := ⟨π₁ x, π₂ x, by simp⟩;
    obtain ⟨y', hy'⟩ := mem_domain_iff.mp (k₁.dom_subset k₂ _ (mem_domain_of_pair_mem hx));
    rwa [k₁.val_agree k₂ hx hy'];
  exact mem_ext fun x ↦ ⟨sub h₁ h₂ x, sub h₂ h₁ x⟩;

/-! ### Gluing tables together -/

lemma isMapping_union (h₁ : BoundedSatisfactionTable q₁ z₁ e₁)
    (h₂ : BoundedSatisfactionTable q₂ z₂ e₂) : IsMapping (q₁ ∪ q₂) := by
  intro x hx;
  obtain ⟨y, hy⟩ := mem_domain_iff.mp hx;
  use y;
  and_intros;
  · exact hy;
  · intro y' hy';
    rcases mem_cup_iff.mp hy with h | h <;> rcases mem_cup_iff.mp hy' with h' | h';
    · exact h₁.val_agree h₁ h' h;
    · exact h₂.val_agree h₁ h' h;
    · exact h₁.val_agree h₂ h' h;
    · exact h₂.val_agree h₂ h' h;

lemma fst_le_of_mem_domain (h : BoundedSatisfactionTable q z e) : ∀ n ∈ domain q, π₁ n ≤ z := by
  apply forall_mem_domain_of_desc (P := fun n ↦ π₁ n ≤ z) (by definability);
  intro n hn IH;
  rcases h.minimal n hn with rfl | hc;
  · simp;
  · rcases hc with ⟨a, b, e', hm, rfl | rfl⟩ | ⟨a, b, e', hm, rfl | rfl⟩ |
      ⟨w, r, e', hm, x, hx, rfl⟩ | ⟨w, r, e', hm, x, hx, rfl⟩ <;>
    exact (le_of_lt (by simp)).trans (IH _ hm (by simp));

lemma root_not_mem_domain (h : BoundedSatisfactionTable q p e₁) (hlt : p < z) :
    ⟪z, e⟫ ∉ domain q :=
  fun hc ↦ not_le_of_gt hlt (by simpa using h.fst_le_of_mem_domain _ hc)

lemma MinChild.mono {Q : V} (hsub : ∀ m ∈ domain q, m ∈ domain Q) (h : MinChild q n) :
    MinChild Q n := by
  rcases h with ⟨a, b, e', hd, hc⟩ | ⟨a, b, e', hd, hc⟩ | ⟨a, b, e', hd, hx⟩ | ⟨a, b, e', hd, hx⟩;
  · disj 1; exact ⟨a, b, e', hsub _ hd, hc⟩;
  · disj 2; exact ⟨a, b, e', hsub _ hd, hc⟩;
  · disj 3; exact ⟨a, b, e', hsub _ hd, hx⟩;
  · disj 4; exact ⟨a, b, e', hsub _ hd, hx⟩;

lemma Spec.mono {Q : V} (hQ : IsMapping Q) (hsub : q ⊆ Q) (hd : ⟪z, e⟫ ∈ domain q)
    (h : Spec q z e) : Spec Q z e := by
  have dom : ∀ m ∈ domain q, m ∈ domain Q := fun m hm ↦ domain_subset_domain_of_subset hsub hm;
  have val : ∀ {m w : V}, m ∈ domain q → (⟪m, w⟫ ∈ Q ↔ ⟪m, w⟫ ∈ q) :=
    fun hm ↦ val_iff_of_subset hQ hsub hm;
  rcases h with ⟨he, hv⟩ | ⟨he, hv⟩ | ⟨a, b, ha, hb, he, hA, hB⟩ | ⟨a, b, ha, hb, he, hA, hB⟩ |
    ⟨a, b, ha, hb, he, hA, hB⟩ | ⟨a, b, ha, hb, he, hA, hB⟩ | ⟨a, b, he, hc, hc', hA, hB⟩ |
    ⟨a, b, he, hc, hc', hA, hB⟩ | ⟨a, b, ht, he, hc, hA, hB⟩ | ⟨a, b, ht, he, hc, hA, hB⟩;
  · disj 1; exact ⟨he, hsub hv⟩;
  · disj 2; exact ⟨he, hsub hv⟩;
  · disj 3; exact ⟨a, b, ha, hb, he, (val hd).trans hA, (val hd).trans hB⟩;
  · disj 4; exact ⟨a, b, ha, hb, he, (val hd).trans hA, (val hd).trans hB⟩;
  · disj 5; exact ⟨a, b, ha, hb, he, (val hd).trans hA, (val hd).trans hB⟩;
  · disj 6; exact ⟨a, b, ha, hb, he, (val hd).trans hA, (val hd).trans hB⟩;
  · disj 7;
    exact ⟨a, b, he, dom _ hc, dom _ hc', by rw [val hd, hA, val hc, val hc'],
      by rw [val hd, hB, val hc, val hc']⟩;
  · disj 8;
    exact ⟨a, b, he, dom _ hc, dom _ hc', by rw [val hd, hA, val hc, val hc'],
      by rw [val hd, hB, val hc, val hc']⟩;
  · disj 9;
    exact ⟨a, b, ht, he, fun x hx ↦ dom _ (hc x hx),
      (val hd).trans <| hA.trans <| forall₂_congr fun x hx ↦ (val (hc x hx)).symm,
      (val hd).trans <| hB.trans <| exists_congr fun x ↦ and_congr_right fun hx ↦
        (val (hc x hx)).symm⟩;
  · disj 10;
    exact ⟨a, b, ht, he, fun x hx ↦ dom _ (hc x hx),
      (val hd).trans <| hA.trans <| exists_congr fun x ↦ and_congr_right fun hx ↦
        (val (hc x hx)).symm,
      (val hd).trans <| hB.trans <| forall₂_congr fun x hx ↦ (val (hc x hx)).symm⟩;

/-! ### Building tables -/

lemma of_insert {W v : V} (hW : IsMapping W) (hz : ⟪z, e⟫ ∉ domain W)
    (hsub : ∀ n ∈ domain W, ∃ r p e', BoundedSatisfactionTable r p e' ∧ r ⊆ W ∧ n ∈ domain r ∧
      MinChild (insert ⟪⟪z, e⟫, v⟫ W) ⟪p, e'⟫)
    (hroot : Spec (insert ⟪⟪z, e⟫, v⟫ W) z e) :
    BoundedSatisfactionTable (insert ⟪⟪z, e⟫, v⟫ W) z e := by
  have hWQ : W ⊆ insert ⟪⟪z, e⟫, v⟫ W := susbset_insert _ _;
  constructor;
  · exact hW.insert hz;
  · simp;
  · intro z' e' hn;
    rcases (by simpa using hn : z' = z ∧ e' = e ∨ ⟪z', e'⟫ ∈ domain W) with ⟨rfl, rfl⟩ | h;
    · exact hroot;
    · obtain ⟨r, p', e'', hr, hrW, hn, -⟩ := hsub _ h;
      exact (hr.spec _ _ hn).mono (hW.insert hz) (subset_trans hrW hWQ) hn;
  · intro n hn;
    rcases (by simpa using hn : n = ⟪z, e⟫ ∨ n ∈ domain W) with h | h;
    · left;
      exact h;
    · right;
      obtain ⟨r, p', e'', hr, hrW, hn, hc⟩ := hsub _ h;
      rcases hr.minimal n hn with rfl | hm;
      · exact hc;
      · exact hm.mono fun m hm ↦ domain_subset_domain_of_subset (subset_trans hrW hWQ) hm;

lemma of_atom {v : V} (h : Spec ({⟪⟪z, e⟫, v⟫} : V) z e) :
    BoundedSatisfactionTable ({⟪⟪z, e⟫, v⟫} : V) z e where
  isMapping := IsMapping.singleton _ _
  mem_dom_root := by simp
  spec z' e' hn := by
    obtain ⟨rfl, rfl⟩ : z' = z ∧ e' = e := by simpa using hn;
    exact h;
  minimal n hn := by
    left;
    simpa using hn;

lemma exists_val (P : Prop) : ∃ v : V, v ≤ 1 ∧ (1 = v ↔ P) ∧ (0 = v ↔ ¬P) := by
  by_cases hP : P;
  · exact ⟨1, le_rfl, by simp [hP], by simp [hP]⟩;
  · exact ⟨0, by simp, by simp [hP], by simp [hP]⟩;

section
variable {N : V} (h₁ : BoundedSatisfactionTable q₁ p₁ e) (h₂ : BoundedSatisfactionTable q₂ p₂ e)
  (hn₁ : ∀ w ∈ q₁, w < N) (hn₂ : ∀ w ∈ q₂, w < N)
include h₁ h₂ hn₁ hn₂

lemma of_and (hr : ∀ v ≤ 1, ⟪⟪p₁ ^⋏ p₂, e⟫, v⟫ < N) :
    ∃ Q, BoundedSatisfactionTable Q (p₁ ^⋏ p₂) e ∧ ∀ w ∈ Q, w < N := by
  have hz : ⟪p₁ ^⋏ p₂, e⟫ ∉ domain (q₁ ∪ q₂) := by
    simpa using ⟨h₁.root_not_mem_domain (by simp), h₂.root_not_mem_domain (by simp)⟩;
  obtain ⟨v, hv, hv1, hv0⟩ := exists_val (V := V) (⟪⟪p₁, e⟫, 1⟫ ∈ q₁ ∧ ⟪⟪p₂, e⟫, 1⟫ ∈ q₂);
  have hQ : IsMapping (insert ⟪⟪p₁ ^⋏ p₂, e⟫, v⟫ (q₁ ∪ q₂)) := (h₁.isMapping_union h₂).insert hz;
  have hs₁ : q₁ ⊆ insert ⟪⟪p₁ ^⋏ p₂, e⟫, v⟫ (q₁ ∪ q₂) :=
    subset_trans (union_succ_union_left _ _) (susbset_insert _ _);
  have hs₂ : q₂ ⊆ insert ⟪⟪p₁ ^⋏ p₂, e⟫, v⟫ (q₁ ∪ q₂) :=
    subset_trans (union_succ_union_right _ _) (susbset_insert _ _);
  use insert ⟪⟪p₁ ^⋏ p₂, e⟫, v⟫ (q₁ ∪ q₂);
  and_intros;
  · apply of_insert (h₁.isMapping_union h₂) hz;
    · intro n hn;
      rcases (by simpa using hn : n ∈ domain q₁ ∨ n ∈ domain q₂) with h | h;
      · exact ⟨q₁, p₁, e, h₁, by simp, h, by disj 1; exact ⟨p₁, p₂, e, by simp, by simp⟩⟩;
      · exact ⟨q₂, p₂, e, h₂, by simp, h, by disj 1; exact ⟨p₁, p₂, e, by simp, by simp⟩⟩;
    · disj 7;
      use p₁, p₂;
      and_intros;
      · rfl;
      · exact domain_subset_domain_of_subset hs₁ h₁.mem_dom_root;
      · exact domain_subset_domain_of_subset hs₂ h₂.mem_dom_root;
      · rw [mem_insert_iff_of_not_mem_domain hz, hv1, val_iff_of_subset hQ hs₁ h₁.mem_dom_root,
          val_iff_of_subset hQ hs₂ h₂.mem_dom_root];
      · rw [mem_insert_iff_of_not_mem_domain hz, hv0, val_iff_of_subset hQ hs₁ h₁.mem_dom_root,
          val_iff_of_subset hQ hs₂ h₂.mem_dom_root, h₁.val_zero_iff h₁.mem_dom_root,
          h₂.val_zero_iff h₂.mem_dom_root, not_and_or];
  · intro w hw;
    rcases (by simpa using hw : w = ⟪⟪p₁ ^⋏ p₂, e⟫, v⟫ ∨ w ∈ q₁ ∨ w ∈ q₂) with rfl | h | h;
    · exact hr v hv;
    · exact hn₁ w h;
    · exact hn₂ w h;

lemma of_or (hr : ∀ v ≤ 1, ⟪⟪p₁ ^⋎ p₂, e⟫, v⟫ < N) :
    ∃ Q, BoundedSatisfactionTable Q (p₁ ^⋎ p₂) e ∧ ∀ w ∈ Q, w < N := by
  have hz : ⟪p₁ ^⋎ p₂, e⟫ ∉ domain (q₁ ∪ q₂) := by
    simpa using ⟨h₁.root_not_mem_domain (by simp), h₂.root_not_mem_domain (by simp)⟩;
  obtain ⟨v, hv, hv1, hv0⟩ := exists_val (V := V) (⟪⟪p₁, e⟫, 1⟫ ∈ q₁ ∨ ⟪⟪p₂, e⟫, 1⟫ ∈ q₂);
  have hQ : IsMapping (insert ⟪⟪p₁ ^⋎ p₂, e⟫, v⟫ (q₁ ∪ q₂)) := (h₁.isMapping_union h₂).insert hz;
  have hs₁ : q₁ ⊆ insert ⟪⟪p₁ ^⋎ p₂, e⟫, v⟫ (q₁ ∪ q₂) :=
    subset_trans (union_succ_union_left _ _) (susbset_insert _ _);
  have hs₂ : q₂ ⊆ insert ⟪⟪p₁ ^⋎ p₂, e⟫, v⟫ (q₁ ∪ q₂) :=
    subset_trans (union_succ_union_right _ _) (susbset_insert _ _);
  use insert ⟪⟪p₁ ^⋎ p₂, e⟫, v⟫ (q₁ ∪ q₂);
  and_intros;
  · apply of_insert (h₁.isMapping_union h₂) hz;
    · intro n hn;
      rcases (by simpa using hn : n ∈ domain q₁ ∨ n ∈ domain q₂) with h | h;
      · exact ⟨q₁, p₁, e, h₁, by simp, h, by disj 2; exact ⟨p₁, p₂, e, by simp, by simp⟩⟩;
      · exact ⟨q₂, p₂, e, h₂, by simp, h, by disj 2; exact ⟨p₁, p₂, e, by simp, by simp⟩⟩;
    · disj 8;
      use p₁, p₂;
      and_intros;
      · rfl;
      · exact domain_subset_domain_of_subset hs₁ h₁.mem_dom_root;
      · exact domain_subset_domain_of_subset hs₂ h₂.mem_dom_root;
      · rw [mem_insert_iff_of_not_mem_domain hz, hv1, val_iff_of_subset hQ hs₁ h₁.mem_dom_root,
          val_iff_of_subset hQ hs₂ h₂.mem_dom_root];
      · rw [mem_insert_iff_of_not_mem_domain hz, hv0, val_iff_of_subset hQ hs₁ h₁.mem_dom_root,
          val_iff_of_subset hQ hs₂ h₂.mem_dom_root, h₁.val_zero_iff h₁.mem_dom_root,
          h₂.val_zero_iff h₂.mem_dom_root, not_or];
  · intro w hw;
    rcases (by simpa using hw : w = ⟪⟪p₁ ^⋎ p₂, e⟫, v⟫ ∨ w ∈ q₁ ∨ w ∈ q₂) with rfl | h | h;
    · exact hr v hv;
    · exact hn₁ w h;
    · exact hn₂ w h;

end

lemma exists_family_union {X N : V}
    (H : ∀ x < X, ∃ q, BoundedSatisfactionTable q p (x ∷ e) ∧ ∀ w ∈ q, w < N) :
    ∃ W : V, IsMapping W ∧ (∀ w ∈ W, w < N) ∧
      (∀ n ∈ domain W, ∃ x < X, ∃ r, BoundedSatisfactionTable r p (x ∷ e) ∧ r ⊆ W ∧ n ∈ domain r) ∧
      (∀ x < X, ∃ r, BoundedSatisfactionTable r p (x ∷ e) ∧ r ⊆ W) := by
  obtain ⟨f, -, hfd, hfr⟩ :
      ∃ f, IsMapping f ∧ domain f = under X ∧
        ∀ x r : V, ⟪x, r⟫ ∈ f → BoundedSatisfactionTable r p (x ∷ e) ∧ ∀ w ∈ r, w < N :=
    sigmaOne_skolem (R := fun x r : V ↦ BoundedSatisfactionTable r p (x ∷ e) ∧ ∀ w ∈ r, w < N)
      (by definability) (fun x hx ↦ H x (by simpa using hx));
  obtain ⟨W, hW⟩ : ∃ W : V, ∀ w : V, w ∈ W ↔ ∃ x < f, ∃ r < f, ⟪x, r⟫ ∈ f ∧ w ∈ r :=
    (finite_comprehension₁! (Γ := 𝚺) (by definability)
      ⟨f, by rintro i ⟨x, -, r, hrf, -, hir⟩; exact (lt_of_mem hir).trans hrf⟩).exists;
  have hsub : ∀ x r : V, ⟪x, r⟫ ∈ f → r ⊆ W := fun x r hxr w hw ↦
    (hW w).mpr ⟨x, (le_pair_left x r).trans_lt (lt_of_mem hxr), r,
      (le_pair_right x r).trans_lt (lt_of_mem hxr), hxr, hw⟩;
  have hmem : ∀ w ∈ W, ∃ x r : V, ⟪x, r⟫ ∈ f ∧ w ∈ r := fun w hw ↦ by
    obtain ⟨x, -, r, -, hxr, hwr⟩ := (hW w).mp hw;
    exact ⟨x, r, hxr, hwr⟩;
  have hdom : ∀ x, x ∈ domain f ↔ x < X := by simp [hfd];
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
    exact ⟨x, (hdom x).mp (mem_domain_of_pair_mem hxr), r, (hfr x r hxr).1, hsub x r hxr,
      mem_domain_of_pair_mem hyr⟩;
  · intro x hx;
    obtain ⟨r, hr⟩ := mem_domain_iff.mp ((hdom x).mpr hx);
    exact ⟨r, (hfr x r hr).1, hsub x r hr⟩;

section
variable {N : V} (hu : ∃ t, IsUTerm ℒₒᵣ t ∧ u = termBShift ℒₒᵣ t)
  (H : ∀ x < termVal (0 ∷ e) u, ∃ q, BoundedSatisfactionTable q p (x ∷ e) ∧ ∀ w ∈ q, w < N)
include hu H

lemma of_ball (hp : p < qqBall u p) (hr : ∀ v ≤ 1, ⟪⟪qqBall u p, e⟫, v⟫ < N) :
    ∃ Q, BoundedSatisfactionTable Q (qqBall u p) e ∧ ∀ w ∈ Q, w < N := by
  obtain ⟨W, hW, hWN, hWdom, hWfam⟩ := exists_family_union H;
  have hz : ⟪qqBall u p, e⟫ ∉ domain W := fun hc ↦ by
    obtain ⟨x, -, r, hr, -, hn⟩ := hWdom _ hc;
    exact hr.root_not_mem_domain hp hn;
  obtain ⟨v, hv, hv1, hv0⟩ :=
    exists_val (V := V) (∀ x < termVal (0 ∷ e) u, ⟪⟪p, x ∷ e⟫, 1⟫ ∈ W);
  have hQ : IsMapping (insert ⟪⟪qqBall u p, e⟫, v⟫ W) := hW.insert hz;
  have hWQ : W ⊆ insert ⟪⟪qqBall u p, e⟫, v⟫ W := susbset_insert _ _;
  have child : ∀ x < termVal (0 ∷ e) u, ⟪p, x ∷ e⟫ ∈ domain W ∧
      (⟪⟪p, x ∷ e⟫, 0⟫ ∈ W ↔ ⟪⟪p, x ∷ e⟫, 1⟫ ∉ W) := fun x hx ↦ by
    obtain ⟨r, hr, hrW⟩ := hWfam x hx;
    have hd := hr.mem_dom_root;
    exact ⟨domain_subset_domain_of_subset hrW hd, by
      rw [val_iff_of_subset hW hrW hd, val_iff_of_subset hW hrW hd, hr.val_zero_iff hd]⟩;
  use insert ⟪⟪qqBall u p, e⟫, v⟫ W;
  and_intros;
  · apply of_insert hW hz;
    · intro n hn;
      obtain ⟨x, hx, r, hr, hrW, hn⟩ := hWdom n hn;
      exact ⟨r, p, x ∷ e, hr, hrW, hn, by disj 3; exact ⟨u, p, e, by simp, x, hx, rfl⟩⟩;
    · disj 9;
      use u, p;
      and_intros;
      · exact hu;
      · rfl;
      · exact fun x hx ↦ domain_subset_domain_of_subset hWQ (child x hx).1;
      · rw [mem_insert_iff_of_not_mem_domain hz, hv1];
        exact forall₂_congr fun x hx ↦ (val_iff_of_subset hQ hWQ (child x hx).1).symm;
      · rw [mem_insert_iff_of_not_mem_domain hz, hv0];
        push Not;
        exact exists_congr fun x ↦ and_congr_right fun hx ↦ by
          rw [val_iff_of_subset hQ hWQ (child x hx).1, (child x hx).2];
  · intro w hw;
    rcases (by simpa using hw : w = ⟪⟪qqBall u p, e⟫, v⟫ ∨ w ∈ W) with rfl | h;
    · exact hr v hv;
    · exact hWN w h;

lemma of_bex (hp : p < qqBex u p) (hr : ∀ v ≤ 1, ⟪⟪qqBex u p, e⟫, v⟫ < N) :
    ∃ Q, BoundedSatisfactionTable Q (qqBex u p) e ∧ ∀ w ∈ Q, w < N := by
  obtain ⟨W, hW, hWN, hWdom, hWfam⟩ := exists_family_union H;
  have hz : ⟪qqBex u p, e⟫ ∉ domain W := fun hc ↦ by
    obtain ⟨x, -, r, hr, -, hn⟩ := hWdom _ hc;
    exact hr.root_not_mem_domain hp hn;
  obtain ⟨v, hv, hv1, hv0⟩ :=
    exists_val (V := V) (∃ x < termVal (0 ∷ e) u, ⟪⟪p, x ∷ e⟫, 1⟫ ∈ W);
  have hQ : IsMapping (insert ⟪⟪qqBex u p, e⟫, v⟫ W) := hW.insert hz;
  have hWQ : W ⊆ insert ⟪⟪qqBex u p, e⟫, v⟫ W := susbset_insert _ _;
  have child : ∀ x < termVal (0 ∷ e) u, ⟪p, x ∷ e⟫ ∈ domain W ∧
      (⟪⟪p, x ∷ e⟫, 0⟫ ∈ W ↔ ⟪⟪p, x ∷ e⟫, 1⟫ ∉ W) := fun x hx ↦ by
    obtain ⟨r, hr, hrW⟩ := hWfam x hx;
    have hd := hr.mem_dom_root;
    exact ⟨domain_subset_domain_of_subset hrW hd, by
      rw [val_iff_of_subset hW hrW hd, val_iff_of_subset hW hrW hd, hr.val_zero_iff hd]⟩;
  use insert ⟪⟪qqBex u p, e⟫, v⟫ W;
  and_intros;
  · apply of_insert hW hz;
    · intro n hn;
      obtain ⟨x, hx, r, hr, hrW, hn⟩ := hWdom n hn;
      exact ⟨r, p, x ∷ e, hr, hrW, hn, by disj 4; exact ⟨u, p, e, by simp, x, hx, rfl⟩⟩;
    · disj 10;
      use u, p;
      and_intros;
      · exact hu;
      · rfl;
      · exact fun x hx ↦ domain_subset_domain_of_subset hWQ (child x hx).1;
      · rw [mem_insert_iff_of_not_mem_domain hz, hv1];
        exact exists_congr fun x ↦ and_congr_right fun hx ↦
          (val_iff_of_subset hQ hWQ (child x hx).1).symm;
      · rw [mem_insert_iff_of_not_mem_domain hz, hv0];
        push Not;
        exact forall₂_congr fun x hx ↦ by
          rw [val_iff_of_subset hQ hWQ (child x hx).1, (child x hx).2];
  · intro w hw;
    rcases (by simpa using hw : w = ⟪⟪qqBex u p, e⟫, v⟫ ∨ w ∈ W) with rfl | h;
    · exact hr v hv;
    · exact hWN w h;

end

/-! ### The bound on a table

`tableBound z e` is a tower of exponentials over `tableExp z e` whose height grows linearly in `z`;
the tables of the children of `z` and the nodes `⟪⟪z, e⟫, v⟫` lie below its logarithm. -/

def tableExp (z e : V) : V := z + e + 2

noncomputable def tableBound (z e : V) : V := Exp.exp (iterExp (tableExp z e) (8 * z + 4))

section tableBound

variable {x v : V}

lemma le_tableExp_left (z e : V) : z ≤ tableExp z e := by simp [tableExp, add_assoc]

lemma le_tableExp_right (z e : V) : e ≤ tableExp z e := by simp [tableExp, add_right_comm z e]

lemma two_le_tableExp (z e : V) : 2 ≤ tableExp z e := by simp [tableExp]

lemma node_lt_iterExp (hv : v ≤ 1) : ⟪⟪z, e⟫, v⟫ < iterExp (tableExp z e) (8 * z + 4) :=
  calc ⟪⟪z, e⟫, v⟫ < iterExp (tableExp z e) 4 := by
        simp only [iterExp_ofNat, Function.iterate_succ_apply', Function.iterate_zero_apply];
        bound [le_tableExp_left z e, le_tableExp_right z e,
          hv.trans (one_le_two.trans (two_le_tableExp z e))]
    _ ≤ iterExp (tableExp z e) (8 * z + 4) := by gcongr; exact le_add_self

lemma lt_iterExp_of_mem {w : V} (hp : p < z) (he' : e' ≤ iterExp (tableExp z e) 5)
    (hq : q ≤ tableBound p e') (hw : w ∈ q) : w < iterExp (tableExp z e) (8 * z + 4) :=
  calc w < tableBound p e' := (lt_of_mem hw).trans_le hq
    _ ≤ Exp.exp (iterExp (iterExp (tableExp z e) 7) (8 * p + 4)) := by
        rw [tableBound];
        gcongr;
        change p + e' + 2 ≤ _;
        simp only [iterExp_ofNat, Function.iterate_succ_apply',
          Function.iterate_zero_apply] at he' ⊢;
        bound [hp.le.trans (le_tableExp_left z e), two_le_tableExp z e]
    _ = iterExp (tableExp z e) (7 + (8 * p + 4) + 1) := by
        rw [iterExp_succ, iterExp_add (tableExp z e) 7]
    _ ≤ iterExp (tableExp z e) (8 * z + 4) := iterExp_le_iterExp le_rfl <|
        calc 7 + (8 * p + 4) + 1 = 8 * (p + 1) + 4 := by ring
          _ ≤ 8 * z + 4 := by gcongr; exact succ_le_iff_lt.mpr hp

lemma adjoin_le_iterExp (hu : u < z) (hx : x < termVal (0 ∷ e) u) :
    x ∷ e ≤ iterExp (tableExp z e) 5 := by
  have : x ≤ Exp.exp (Exp.exp (Exp.exp (tableExp z e))) :=
    hx.le.trans <| (termVal_le _ _).trans <| by
      rw [listMax_adjoin];
      bound [le_tableExp_right z e, hu.le.trans (le_tableExp_left z e)];
  simp only [iterExp_ofNat, Function.iterate_succ_apply', Function.iterate_zero_apply];
  bound [le_tableExp_right z e];

end tableBound

/-! ### Existence -/

lemma exists_atom_table (hz : IsUFormula ℒₒᵣ z)
    (h : z = ^⊤ ∨ z = ^⊥ ∨ (∃ k r w, z = ^rel k r w) ∨ (∃ k r w, z = ^nrel k r w)) :
    ∃ q ≤ tableBound z e, BoundedSatisfactionTable q z e := by
  suffices ∃ v ≤ 1, Spec ({⟪⟪z, e⟫, v⟫} : V) z e by
    obtain ⟨v, hv, hs⟩ := this;
    exact ⟨_, exp_le_exp (node_lt_iterExp hv).le, of_atom hs⟩;
  rcases h with rfl | rfl | ⟨k, r, w, rfl⟩ | ⟨k, r, w, rfl⟩;
  · exact ⟨1, le_rfl, by disj 1; exact ⟨rfl, by simp⟩⟩;
  · exact ⟨0, by simp, by disj 2; exact ⟨rfl, by simp⟩⟩;
  · rcases rel_cases hz with ⟨t, u, ht, hu, hzz⟩ | ⟨t, u, ht, hu, hzz⟩ <;> rw [hzz];
    · obtain ⟨v, hv, hv1, hv0⟩ := exists_val (V := V) (termVal e t = termVal e u);
      exact ⟨v, hv, by disj 3; exact ⟨t, u, ht, hu, rfl, by simp [hv1], by simp [hv0]⟩⟩;
    · obtain ⟨v, hv, hv1, hv0⟩ := exists_val (V := V) (termVal e t < termVal e u);
      exact ⟨v, hv, by disj 5; exact ⟨t, u, ht, hu, rfl, by simp [hv1], by simp [hv0]⟩⟩;
  · rcases nrel_cases hz with ⟨t, u, ht, hu, hzz⟩ | ⟨t, u, ht, hu, hzz⟩ <;> rw [hzz];
    · obtain ⟨v, hv, hv1, hv0⟩ := exists_val (V := V) (termVal e t ≠ termVal e u);
      exact ⟨v, hv, by disj 4; exact ⟨t, u, ht, hu, rfl, by simp [hv1], by simp [hv0]⟩⟩;
    · obtain ⟨v, hv, hv1, hv0⟩ := exists_val (V := V) (¬termVal e t < termVal e u);
      exact ⟨v, hv, by disj 6; exact ⟨t, u, ht, hu, rfl, by simp [hv1], by simp [hv0]⟩⟩;

end BoundedSatisfactionTable

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
  · rintro e _ rfl hu;
    exact exists_atom_table hu (by disj 1; rfl);
  · rintro e _ rfl hu;
    exact exists_atom_table hu (by disj 2; rfl);
  · rintro k r w e _ rfl hu;
    exact exists_atom_table hu (by disj 3; exact ⟨k, r, w, rfl⟩);
  · rintro k r w e _ rfl hu;
    exact exists_atom_table hu (by disj 4; exact ⟨k, r, w, rfl⟩);
  · rintro p₁ p₂ - - ih₁ ih₂ e _ rfl hu;
    obtain ⟨hu₁, hu₂⟩ : IsUFormula ℒₒᵣ p₁ ∧ IsUFormula ℒₒᵣ p₂ := by simpa using hu;
    obtain ⟨q₁, hb₁, hq₁⟩ := ih₁ e _ rfl hu₁;
    obtain ⟨q₂, hb₂, hq₂⟩ := ih₂ e _ rfl hu₂;
    have he : e ≤ iterExp (tableExp (p₁ ^⋏ p₂) e) 5 :=
      (le_tableExp_right _ e).trans (le_iterExp _ _);
    obtain ⟨Q, hQ, hQN⟩ := hq₁.of_and hq₂ (fun _ ↦ lt_iterExp_of_mem (by simp) he hb₁)
      (fun _ ↦ lt_iterExp_of_mem (by simp) he hb₂) fun _ ↦ node_lt_iterExp;
    exact ⟨Q, (lt_exp_iff.mpr hQN).le, hQ⟩;
  · rintro p₁ p₂ - - ih₁ ih₂ e _ rfl hu;
    obtain ⟨hu₁, hu₂⟩ : IsUFormula ℒₒᵣ p₁ ∧ IsUFormula ℒₒᵣ p₂ := by simpa using hu;
    obtain ⟨q₁, hb₁, hq₁⟩ := ih₁ e _ rfl hu₁;
    obtain ⟨q₂, hb₂, hq₂⟩ := ih₂ e _ rfl hu₂;
    have he : e ≤ iterExp (tableExp (p₁ ^⋎ p₂) e) 5 :=
      (le_tableExp_right _ e).trans (le_iterExp _ _);
    obtain ⟨Q, hQ, hQN⟩ := hq₁.of_or hq₂ (fun _ ↦ lt_iterExp_of_mem (by simp) he hb₁)
      (fun _ ↦ lt_iterExp_of_mem (by simp) he hb₂) fun _ ↦ node_lt_iterExp;
    exact ⟨Q, (lt_exp_iff.mpr hQN).le, hQ⟩;
  · rintro t p ht - ih e _ rfl hu;
    have hp : IsUFormula ℒₒᵣ p := (IsUFormula.or.mp (IsUFormula.all.mp hu)).2;
    obtain ⟨Q, hQ, hQN⟩ := of_ball (e := e) ⟨t, ht, rfl⟩ (fun x hx ↦ by
        obtain ⟨q, hqb, hq⟩ := ih (x ∷ e) _ rfl hp;
        exact ⟨q, hq, fun _ ↦ lt_iterExp_of_mem (by simp) (adjoin_le_iterExp (by simp) hx) hqb⟩)
      (by simp) fun _ ↦ node_lt_iterExp;
    exact ⟨Q, (lt_exp_iff.mpr hQN).le, hQ⟩;
  · rintro t p ht - ih e _ rfl hu;
    have hp : IsUFormula ℒₒᵣ p := (IsUFormula.and.mp (IsUFormula.ex.mp hu)).2;
    obtain ⟨Q, hQ, hQN⟩ := of_bex (e := e) ⟨t, ht, rfl⟩ (fun x hx ↦ by
        obtain ⟨q, hqb, hq⟩ := ih (x ∷ e) _ rfl hp;
        exact ⟨q, hq, fun _ ↦ lt_iterExp_of_mem (by simp) (adjoin_le_iterExp (by simp) hx) hqb⟩)
      (by simp) fun _ ↦ node_lt_iterExp;
    exact ⟨Q, (lt_exp_iff.mpr hQN).le, hQ⟩;

/-! ## The satisfaction predicate -/

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

lemma iff_of_forall_table {P : Prop} (hz : IsBounded z) (hz' : IsUFormula ℒₒᵣ z)
    (H : ∀ r, BoundedSatisfactionTable r z e → (⟪⟪z, e⟫, 1⟫ ∈ r ↔ P)) :
    BoundedSatisfaction z e ↔ P := by
  obtain ⟨r, hr⟩ := BoundedSatisfactionTable.exists hz hz';
  exact (iff_val hz hz' hr).trans (H r hr);

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

@[simp] lemma eq_iff : BoundedSatisfaction (t ^= u) e ↔ termVal e t = termVal e u :=
  iff_of_forall_table (by simp [Arithmetic.qqEQ]) (by simp [Arithmetic.qqEQ, ht, hu])
    fun _ hr ↦ hr.val_eq hr.mem_dom_root

@[simp] lemma neq_iff : BoundedSatisfaction (t ^≠ u) e ↔ termVal e t ≠ termVal e u :=
  iff_of_forall_table (by simp [Arithmetic.qqNEQ]) (by simp [Arithmetic.qqNEQ, ht, hu])
    fun _ hr ↦ hr.val_neq hr.mem_dom_root

@[simp] lemma lt_iff : BoundedSatisfaction (t ^< u) e ↔ termVal e t < termVal e u :=
  iff_of_forall_table (by simp [Arithmetic.qqLT]) (by simp [Arithmetic.qqLT, ht, hu])
    fun _ hr ↦ hr.val_lt hr.mem_dom_root

@[simp] lemma nlt_iff : BoundedSatisfaction (t ^≮ u) e ↔ ¬(termVal e t < termVal e u) :=
  iff_of_forall_table (by simp [Arithmetic.qqNLT]) (by simp [Arithmetic.qqNLT, ht, hu])
    fun _ hr ↦ hr.val_nlt hr.mem_dom_root

end

@[simp] lemma and_iff {p q e : V} :
    BoundedSatisfaction (p ^⋏ q) e ↔ BoundedSatisfaction p e ∧ BoundedSatisfaction q e := by
  by_cases h : (IsBounded p ∧ IsUFormula ℒₒᵣ p) ∧ IsBounded q ∧ IsUFormula ℒₒᵣ q;
  · obtain ⟨⟨hdp, hfp⟩, hdq, hfq⟩ := h;
    exact iff_of_forall_table (IsBounded.and_iff.mpr ⟨hdp, hdq⟩) (by simp [hfp, hfq]) fun _ hr ↦ by
      obtain ⟨hn₁, hn₂⟩ := hr.mem_dom_and hr.mem_dom_root;
      rw [hr.val_and hr.mem_dom_root, iff_mem hr hn₁ hdp hfp, iff_mem hr hn₂ hdq hfq];
  · apply iff_of_false;
    · intro hs;
      obtain ⟨hdp, hdq⟩ := IsBounded.and_iff.mp hs.isBounded;
      obtain ⟨hfp, hfq⟩ := IsUFormula.and.mp hs.isUFormula;
      exact h ⟨⟨hdp, hfp⟩, hdq, hfq⟩;
    · exact fun ⟨h₁, h₂⟩ ↦ h ⟨h₁.dom, h₂.dom⟩;

@[simp] lemma or_iff {p q e : V} (hdp : IsBounded p) (hfp : IsUFormula ℒₒᵣ p)
    (hdq : IsBounded q) (hfq : IsUFormula ℒₒᵣ q) :
    BoundedSatisfaction (p ^⋎ q) e ↔ BoundedSatisfaction p e ∨ BoundedSatisfaction q e :=
  iff_of_forall_table (IsBounded.or_iff.mpr ⟨hdp, hdq⟩) (by simp [hfp, hfq]) fun _ hr ↦ by
    obtain ⟨hn₁, hn₂⟩ := hr.mem_dom_or hr.mem_dom_root;
    rw [hr.val_or hr.mem_dom_root, iff_mem hr hn₁ hdp hfp, iff_mem hr hn₂ hdq hfq];

section
variable {t q e : V} (ht : IsUTerm ℒₒᵣ t)
include ht

@[simp] lemma ball_iff (hq : IsBounded q) (hq' : IsUFormula ℒₒᵣ q) :
    BoundedSatisfaction (qqBall (termBShift ℒₒᵣ t) q) e ↔
      ∀ x < termVal e t, BoundedSatisfaction q (x ∷ e) :=
  iff_of_forall_table (IsBounded.ball ht hq)
    (by simp [qqBall, Arithmetic.qqNLT, ht.termBShift, hq'])
    fun _ hr ↦ (hr.val_ball ht hr.mem_dom_root).trans <| forall₂_congr fun _ hx ↦
      (iff_mem hr (hr.mem_dom_ball ht hr.mem_dom_root hx) hq hq').symm

@[simp] lemma bex_iff :
    BoundedSatisfaction (qqBex (termBShift ℒₒᵣ t) q) e ↔
      ∃ x < termVal e t, BoundedSatisfaction q (x ∷ e) := by
  by_cases h : IsBounded q ∧ IsUFormula ℒₒᵣ q;
  · obtain ⟨hq, hq'⟩ := h;
    exact iff_of_forall_table (IsBounded.bex ht hq)
      (by simp [qqBex, Arithmetic.qqLT, ht.termBShift, hq']) fun _ hr ↦
        (hr.val_bex ht hr.mem_dom_root).trans <| exists_congr fun _ ↦ and_congr_right fun hx ↦
          (iff_mem hr (hr.mem_dom_bex ht hr.mem_dom_root hx) hq hq').symm;
  · apply iff_of_false;
    · intro hs;
      exact h ⟨hs.isBounded.of_qqBex,
        by simpa [qqBex, Arithmetic.qqLT, ht.termBShift] using hs.isUFormula⟩;
    · exact fun ⟨_, _, hs⟩ ↦ h hs.dom;

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
      simp [ih hfq];
    · intro t q ht hdq ih h e;
      obtain ⟨-, hfq⟩ : IsUTerm ℒₒᵣ (termBShift ℒₒᵣ t) ∧ IsUFormula ℒₒᵣ q := by
        simpa [qqBex, Arithmetic.qqLT] using h;
      rw [neg_qqBex ht.termBShift hfq, ball_iff ht (IsBounded.neg hfq hdq) hfq.neg, bex_iff ht];
      simp [ih hfq];
  exact H p hp hp' e;

section
variable {n m w k r v e : V} (hw : IsSemitermVec ℒₒᵣ n m w)
include hw

lemma subst_rel (hp : IsSemiformula ℒₒᵣ n (^rel k r v)) :
    BoundedSatisfaction (Bootstrapping.subst ℒₒᵣ w (^rel k r v)) e ↔
      BoundedSatisfaction (^rel k r v) (termValVec e n w) := by
  rcases rel_cases hp.isUFormula with ⟨t, u, ht, hu, heq⟩ | ⟨t, u, ht, hu, heq⟩ <;>
    rw [heq] at hp ⊢;
  · obtain ⟨hts, hus⟩ : IsSemiterm ℒₒᵣ n t ∧ IsSemiterm ℒₒᵣ n u := by
      simpa [Arithmetic.qqEQ] using hp;
    rw [substs_qqEQ ht hu, eq_iff (hw.termSubst hts).isUTerm (hw.termSubst hus).isUTerm,
      eq_iff ht hu, termVal_termSubst hw hts, termVal_termSubst hw hus];
  · obtain ⟨hts, hus⟩ : IsSemiterm ℒₒᵣ n t ∧ IsSemiterm ℒₒᵣ n u := by
      simpa [Arithmetic.qqLT] using hp;
    rw [substs_qqLT ht hu, lt_iff (hw.termSubst hts).isUTerm (hw.termSubst hus).isUTerm,
      lt_iff ht hu, termVal_termSubst hw hts, termVal_termSubst hw hus];

lemma subst_nrel (hp : IsSemiformula ℒₒᵣ n (^nrel k r v)) :
    BoundedSatisfaction (Bootstrapping.subst ℒₒᵣ w (^nrel k r v)) e ↔
      BoundedSatisfaction (^nrel k r v) (termValVec e n w) := by
  rcases nrel_cases hp.isUFormula with ⟨t, u, ht, hu, heq⟩ | ⟨t, u, ht, hu, heq⟩ <;>
    rw [heq] at hp ⊢;
  · obtain ⟨hts, hus⟩ : IsSemiterm ℒₒᵣ n t ∧ IsSemiterm ℒₒᵣ n u := by
      simpa [Arithmetic.qqNEQ] using hp;
    rw [substs_qqNEQ ht hu, neq_iff (hw.termSubst hts).isUTerm (hw.termSubst hus).isUTerm,
      neq_iff ht hu, termVal_termSubst hw hts, termVal_termSubst hw hus];
  · obtain ⟨hts, hus⟩ : IsSemiterm ℒₒᵣ n t ∧ IsSemiterm ℒₒᵣ n u := by
      simpa [Arithmetic.qqNLT] using hp;
    rw [substs_qqNLT ht hu, nlt_iff (hw.termSubst hts).isUTerm (hw.termSubst hus).isUTerm,
      nlt_iff ht hu, termVal_termSubst hw hts, termVal_termSubst hw hus];

end

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
      exact subst_rel hw hp;
    · intro k r v n m w e hw hp;
      exact subst_nrel hw hp;
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
      exact forall₂_congr fun x _ ↦ by
        rw [ih (n + 1) (m + 1) (qVec ℒₒᵣ w) (x ∷ e) hw.qVec hq, termValVec_qVec hw];
    · intro t q ht hdq ih n m w e hw hpq;
      obtain ⟨hts, hq⟩ := isSemiformula_qqBex ht hpq;
      rw [substs_qqBex hw hts hq.isUFormula, bex_iff (hw.termSubst hts).isUTerm, bex_iff ht,
        termVal_termSubst hw hts];
      exact exists_congr fun x ↦ and_congr_right fun _ ↦ by
        rw [ih (n + 1) (m + 1) (qVec ℒₒᵣ w) (x ∷ e) hw.qVec hq, termValVec_qVec hw];
  exact H p hp' n m w e hw hp;

end BoundedSatisfaction

end FFL.FirstOrder.Arithmetic.Bootstrapping
