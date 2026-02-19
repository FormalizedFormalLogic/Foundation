module

public import Foundation.ProvabilityLogic.Classification.LetterlessTrace
public import Foundation.Modal.Boxdot.GL_S
public import Foundation.Modal.Logic.D.Basic

@[expose] public section




namespace LO

namespace Modal

variable {φ ψ : Formula ℕ}

open Kripke
open Formula.Kripke


namespace Formula

def trace (φ : Formula ℕ) : Set ℕ := { n |
  ∃ M : Kripke.Model, ∃ _ : Fintype M, ∃ _ : M.IsTransitive, ∃ _ : M.IsConverseWellFounded, ∃ r, ∃ _ : M.IsRootedBy r,
  (M.height = n ∧ r ⊭ φ)
}

lemma iff_mem_trace {n : ℕ} :
  n ∈ φ.trace ↔
  ∃ M : Kripke.Model, ∃ _ : Fintype M, ∃ _ : M.IsTransitive, ∃ _ : M.IsConverseWellFounded, ∃ r, ∃ _ : M.IsRootedBy r, M.height = n ∧ r ⊭ φ := by
  simp [Formula.trace];

lemma satisfies_of_not_mem_trace :
  n ∉ φ.trace ↔
  ∀ M : Kripke.Model, ∀ _ : Fintype M, ∀ _ : M.IsTransitive, ∀ _ : M.IsConverseWellFounded, ∀ r, ∀ _ : M.IsRootedBy r, M.height = n → r ⊧ φ := by
  simp [Formula.trace];

@[grind =]
lemma eq_trace_trace_of_letterless {φ : Formula ℕ} (φ_letterless : φ.Letterless) : φ.trace = φ.letterlessTrace := by
  ext n;
  apply Iff.trans ?_ (Kripke.letterlessSpectrum_TFAE φ_letterless (n := n) |>.out 1 0 |>.not);
  rw [iff_mem_trace];
  constructor;
  . rintro ⟨M, _, _, _, r, _, rfl, hr⟩;
    push_neg;
    refine ⟨M, inferInstance, inferInstance, inferInstance, r, inferInstance, r, by tauto⟩;
  . contrapose!;
    rintro h M _ _ _ r _ x rfl;
    apply Model.pointGenerate.modal_equivalent' x ⟨x, by tauto⟩ |>.mp;
    apply h;
    . apply Frame.pointGenerate.eq_original_height;
    . infer_instance

open Formula.Kripke

@[simp, grind =] lemma trace_bot : (⊥ : Formula ℕ).trace = Set.univ := by grind;
@[simp, grind =] lemma trace_top : (⊤ : Formula ℕ).trace = ∅ := by grind;

lemma trace_and : (φ ⋏ ψ).trace = φ.trace ∪ ψ.trace := by
  ext n;
  calc
    _ ↔ ∃ M : Kripke.Model, ∃ _ : Fintype M, ∃ _ : M.IsTransitive, ∃ _ : M.IsConverseWellFounded, ∃ r, ∃ _ : M.IsRootedBy r, M.height = n ∧ (r ⊭ φ ∨ r ⊭ ψ) := by
      simp [Semantics.NotModels, trace, -not_and, not_and_or]
    _ ↔
      (∃ M : Kripke.Model, ∃ _ : Fintype M, ∃ _ : M.IsTransitive, ∃ _ : M.IsConverseWellFounded, ∃ r, ∃ _ : M.IsRootedBy r, M.height = n ∧ r ⊭ φ) ∨
      (∃ M : Kripke.Model, ∃ _ : Fintype M, ∃ _ : M.IsTransitive, ∃ _ : M.IsConverseWellFounded, ∃ r, ∃ _ : M.IsRootedBy r, M.height = n ∧ r ⊭ ψ) := by
      constructor;
      . rintro ⟨M, _, _, _, r, _, rfl, h⟩;
        cases h with
        | inl h => left; tauto
        | inr h => right; tauto
      . rintro (⟨M, _, _, _, r, _, rfl, hr⟩ | ⟨M, _, _, _, r, _, rfl, hr⟩) <;>
        refine ⟨M, inferInstance, inferInstance, inferInstance, r, inferInstance, rfl, by grind⟩;
    _ ↔ _ := by simp [Formula.trace];

lemma trace_lconj₂ {s : List (Formula ℕ)} : (s.conj₂).trace = ⋃ φ ∈ s, φ.trace := by
  induction s using List.induction_with_singleton with
  | hcons φ s hs ih => simp [List.conj₂_cons_nonempty hs, Formula.trace_and, ih];
  | _ => simp [List.conj₂];

lemma trace_fconj {s : Finset (Formula ℕ)} : s.conj.trace = ⋃ φ ∈ s, φ.trace := by simp [Finset.conj, Formula.trace_lconj₂];

lemma subset_trace_of_provable_imp_GL (h : Modal.GL ⊢ φ ➝ ψ) : ψ.trace ⊆ φ.trace := by
  intro n hn;
  obtain ⟨M, _, _, _, r, _, rfl, hr⟩ := iff_mem_trace.mp hn;
  apply iff_mem_trace.mpr;
  refine ⟨M, inferInstance, inferInstance, inferInstance, r, inferInstance, rfl, ?_⟩;
  contrapose! hr;
  have := GL.Kripke.fintype_completeness_TFAE.out 0 2 |>.mp h;
  exact this M r hr;

end Formula


namespace FormulaSet

abbrev trace (X : FormulaSet ℕ) : Set ℕ := ⋃ φ ∈ X, φ.trace

@[simp] lemma trace_empty : (∅ : FormulaSet ℕ).trace = ∅ := by simp [FormulaSet.trace];

lemma eq_FormulaSet_trace_finset_conj {X : Finset (Formula ℕ)} : X.conj.trace = FormulaSet.trace X := by simp [FormulaSet.trace, Formula.trace_fconj];

lemma subset_trace_of_subset {X Y : FormulaSet ℕ} (h : X ⊆ Y) : X.trace ⊆ Y.trace := by
  simp only [trace, Set.iUnion_subset_iff];
  intro φ hφ i hi;
  simp only [Set.mem_iUnion, exists_prop];
  use φ;
  constructor;
  . apply h; assumption;
  . assumption;

end FormulaSet


abbrev Logic.trace (L : Logic ℕ) : Set ℕ := FormulaSet.trace L

lemma GL.eq_trace_ext {X : FormulaSet ℕ} (hX : ∀ ξ ∈ X, ∀ s : Substitution _, ξ⟦s⟧ ∈ X) : (Modal.GL.sumQuasiNormal X).trace = X.trace := by
  ext n;
  constructor;
  . suffices (∃ φ, Modal.GL.sumQuasiNormal X ⊢ φ ∧ n ∈ φ.trace) → (n ∈ X.trace) by simpa [Logic.trace, Logic.iff_provable];
    rintro ⟨φ, hφ₁, hφ₂⟩;
    obtain ⟨Y, hY₁, hY₂⟩ := Logic.sumQuasiNormal.iff_provable_finite_provable hX |>.mp hφ₁;
    apply FormulaSet.subset_trace_of_subset hY₁;
    apply FormulaSet.eq_FormulaSet_trace_finset_conj ▸ Formula.subset_trace_of_provable_imp_GL hY₂;
    assumption;
  . suffices (∃ φ ∈ X, n ∈ φ.trace) → (∃ φ, Modal.GL.sumQuasiNormal X ⊢ φ ∧ n ∈ φ.trace) by simpa [Logic.trace, Logic.iff_provable];
    rintro ⟨φ, hφ₁, hφ₂⟩;
    use φ;
    constructor;
    . apply Logic.sumQuasiNormal.mem₂!;
      simpa [Logic.iff_provable];
    . assumption;

lemma GL.unprovable_of_exists_trace (φ_letterless : φ.Letterless) : (∃ n, n ∈ φ.letterlessTrace) → Modal.GL ⊬ φ := by
  contrapose!;
  intro h;
  have := Modal.iff_GL_provable_letterlessSpectrum_Univ φ_letterless |>.mp (by simpa using h);
  simp_all [Formula.letterlessTrace];

@[simp]
lemma TBBMinus_trace (hβ : β.Cofinite) : (∼⩕ n ∈ hβ.toFinset, TBB n).letterlessTrace = β := by
  simp [Formula.letterlessTrace, TBBMinus_letterlessSpectrum']

@[simp]
lemma GL.eq_trace_emptyset : Modal.GL.trace = ∅ := by
  rw [←Logic.sumQuasiNormal.with_empty (L₁ := Modal.GL)]
  simpa using GL.eq_trace_ext (X := ∅) (by simp);

@[simp]
lemma GLα.eq_trace {α : Set ℕ} : (Modal.GLα α).trace = α := by
  apply Eq.trans $ GL.eq_trace_ext $ by grind;
  simp [FormulaSet.trace, Formula.eq_trace_trace_of_letterless];

@[simp]
lemma GLβMinus.eq_trace {β : Set ℕ} (hβ : β.Cofinite := by grind) : (Modal.GLβMinus β).trace = β := by
  apply Eq.trans $ GL.eq_trace_ext $ by grind;
  simp [FormulaSet.trace, Formula.eq_trace_trace_of_letterless];

@[simp, grind .] lemma S.provable_TBB {n : ℕ} : Modal.S ⊢ TBB n := by simp [TBB]

@[simp]
lemma subset_GLα_S : Modal.GLα α ⊆ Modal.S := by
  intro φ;
  suffices Modal.GLα α ⊢ φ → Modal.S ⊢ φ by grind;
  intro hφ;
  induction hφ using Modal.Logic.sumQuasiNormal.rec! with
  | mem₁ hφ => exact Entailment.WeakerThan.pbl hφ;
  | mem₂ hφ => obtain ⟨_, _, rfl⟩ := hφ; simp;
  | mdp ihφψ ihφ => exact ihφψ ⨀ ihφ;
  | subst ihφ => exact Logic.subst _ ihφ;

instance : Modal.GLα α ⪯ Modal.S := Logic.weakerThan_of_subset subset_GLα_S

@[simp]
lemma S.eq_trace : Modal.S.trace = Set.univ := by
  suffices ∀ (x : ℕ), ∃ i ∈ Modal.S, x ∈ i.trace by simpa [Set.eq_univ_iff_forall]
  intro n;
  use (TBB n);
  constructor;
  . apply Logic.iff_provable.mp; grind;
  . simp [Formula.eq_trace_trace_of_letterless];

variable {L : Logic ℕ} {φ : Formula ℕ}


lemma subset_of_provable (h : L ⊢ φ) : φ.trace ⊆ L.trace := by
  intro n h;
  suffices ∃ i ∈ L, n ∈ i.trace by simpa [Logic.trace, FormulaSet.trace];
  use φ;
  grind;


namespace Kripke

/--
  ... ≺ x ≺ a ≺ y ≺ ...
  ↓
  ... ≺ x ≺ (n - 1) ≺ ... ≺ 0 ≺ a ≺ y ≺ ...
-/
def Model.boneLengthening (M : Kripke.Model) (a : M) (n : ℕ) : Kripke.Model where
  World := M.World ⊕ Fin n
  Rel w v :=
    match w, v with
    | .inl x, .inl y => x ≺ y
    | .inl x, .inr _ => x ≺ a
    | .inr _, .inl y => y = a ∨ a ≺ y
    | .inr i, .inr j => i > j
  Val p x :=
    match x with
    | .inl w => M.Val p w
    | .inr _ => M.Val p a

namespace Model.boneLengthening

variable {M : Kripke.Model} {a : M} [M.IsIrreflexive] {k : ℕ} {φ : Formula ℕ}

@[coe] abbrev callus (i : Fin k) : M.boneLengthening a k := Sum.inr i
instance : Coe (Fin k) (M.boneLengthening a k) := ⟨callus⟩

@[coe] abbrev embed (x : M) : M.boneLengthening a k := Sum.inl x
instance : Coe (M.World) ((M.boneLengthening a k).World) := ⟨embed⟩

instance [Fintype M] : Fintype (M.boneLengthening a k) := by apply instFintypeSum

instance [M.IsTransitive] : (M.boneLengthening a k).IsTransitive where
  trans := by
    rintro (x | i) (y | j) (z | l) Rxy Ryz <;> simp_all only [Model.boneLengthening];
    . apply Frame.trans Rxy Ryz;
    . apply Frame.trans Rxy Ryz;
    . rcases Ryz with rfl | Ray;
      . assumption;
      . exact Frame.trans Rxy Ray;
    . rcases Rxy with rfl | Ray;
      . tauto;
      . right;
        exact Frame.trans Ray Ryz;
    . exfalso;
      rcases Rxy with rfl | Ray;
      . apply M.irrefl _ Ryz;
      . apply M.irrefl _ $ Frame.trans Ryz Ray;
    . omega;

instance [M.IsIrreflexive] : (M.boneLengthening a k).IsIrreflexive where
  irrefl := by
    rintro (x | i);
    . apply M.irrefl x;
    . simp [Model.boneLengthening];

instance isRooted [M.IsTransitive] [M.IsRootedBy r] (hra : r ≠ a) : (M.boneLengthening a k).IsRootedBy r where
  root_generates := by
    rintro (x | i) <;>
    . intro;
      apply Rel.TransGen.unwrap_iff.mpr;
      dsimp [Model.boneLengthening];
      apply Frame.root_genaretes'!;
      tauto;

instance isTree [M.IsTree r] (hra : r ≠ a) : (M.boneLengthening a k).IsTree r where
  asymm := by
    rintro (x | i) (y | j) Rxy;
    . apply M.asymm Rxy;
    . apply not_or.mpr;
      constructor;
      . contrapose! Rxy;
        simp_all [Model.boneLengthening];
      . exact M.asymm Rxy;
    . rcases Rxy with rfl | Ray;
      . apply Frame.irrefl;
      . apply M.asymm Ray;
    . simp_all [Model.boneLengthening];
      omega;
  root_generates := by
    rintro (x | i) <;>
    . intro;
      apply Rel.TransGen.unwrap_iff.mpr;
      dsimp [Model.boneLengthening];
      apply Frame.root_genaretes'!;
      tauto;

@[simp]
axiom eq_height [M.IsTree r] [Fintype M] (hra : r ≠ a) :
  have : (M.boneLengthening a k).IsTree r := isTree hra;
  (M.boneLengthening a k).height = M.height + k
  /-
  := by
  intro _;
  apply height_eq_iff_relItr.mpr;
  constructor;
  . obtain ⟨t, Rrt⟩ := Kripke.exists_rank_terminal (F := M.boneLengthening a k |>.toFrame) r;
    use t;
    induction k with
    | zero =>
      sorry;
    | succ k ih =>
      suffices (r : M.boneLengthening a (k + 1)) ≺^[(M.rank + k) + 1] t by
        rwa [(show M.rank + (k + 1) = (M.rank + k) + 1 by omega)];
      dsimp [Frame.RelItr', Rel.Iterate]
      sorry;
  . intro t Rrt x;
    sorry;
  -/

axiom equivalence {x : M} (hx : x = a ∨ a ≺ x) : ∀ φ, x ⊧ φ ↔ ((x : M.boneLengthening a k) ⊧ φ) -- := by sorry

lemma mainlemma_aux
  (hrfl : a ⊧ φ.rflSubformula.conj)
  {ψ} (hψ : ψ ∈ φ.subformulas) :
  (∀ i : Fin k, ((i : M.boneLengthening a k) ⊧ ψ ↔ (a : M.boneLengthening a k) ⊧ ψ)) ∧
  (∀ x : M, (x ⊧ ψ ↔ (x : M.boneLengthening a k) ⊧ ψ)) := by
  induction ψ with
  | hatom => simp [Semantics.Models, Satisfies, Model.boneLengthening];
  | hfalsum => simp;
  | himp ψ ξ ihψ ihξ => simp [ihψ (by grind), ihξ (by grind)];
  | hbox ψ ihφ =>
    have ⟨ihφ₁, ihφ₂⟩ := ihφ (by grind);
    constructor;
    . intro i;
      constructor;
      . rintro h j Raj;
        apply h;
        rcases j with (j | j);
        . right; exact Raj;
        . simp [Frame.Rel', Model.boneLengthening] at Raj;
      . intro h;
        have : (a : M.boneLengthening a k) ⊧ ψ := Satisfies.fconj_def.mp (equivalence (by tauto) _ |>.mp hrfl) (□ψ ➝ ψ) ?_ h;
        . rintro (y | j) Ri;
          . rcases Ri with rfl | Ray;
            . assumption;
            . apply h;
              exact Ray;
          . apply ihφ₁ j |>.mpr this;
        . simp only [Finset.mem_image, Finset.LO.preboxItr, Function.iterate_one, Finset.mem_preimage]
          use ψ;
    . intro y;
      constructor;
      . rintro h (z | j) Ryz;
        . apply ihφ₂ _ |>.mp;
          apply h;
          exact Ryz;
        . apply ihφ₁ j |>.mpr;
          apply ihφ₂ _ |>.mp;
          apply h;
          apply Ryz;
      . intro h z Ryz;
        apply ihφ₂ z |>.mpr;
        apply h;
        exact Ryz;

lemma mainlemma₁
  (hrfl : a ⊧ φ.rflSubformula.conj) {ψ} (hψ : ψ ∈ φ.subformulas) (i : Fin k)
  : ((i : M.boneLengthening a k) ⊧ ψ) ↔ (a : M.boneLengthening a k) ⊧ ψ := (mainlemma_aux hrfl (by grind)).1 i

lemma mainlemma₂
  (hrfl : a ⊧ φ.rflSubformula.conj) {ψ} (hψ : ψ ∈ φ.subformulas) (x : M)
  : (x ⊧ ψ) ↔ (x : M.boneLengthening a k) ⊧ ψ := (mainlemma_aux hrfl (by grind)).2 x

end Model.boneLengthening

end Kripke

axiom GL.formalized_validates_axiomT_set_in_irrefl_trans_chain : Modal.GL ⊢ ∼□^[(φ.rflSubformula.card + 1)]⊥ ➝ ◇φ.rflSubformula.conj

@[grind .]
lemma Formula.trace.finite_or_cofinite : φ.trace.Finite ∨ φ.trace.Cofinite := by
  suffices φ.trace.Infinite → φ.trace.Cofinite by tauto;
  intro tr_infinite;

  obtain ⟨m, hm₁, hm₂⟩ : ∃ m, m ∈ φ.trace ∧ φ.rflSubformula.card < m  := Set.infinite_iff_exists_gt.mp tr_infinite _;
  obtain ⟨M, _, _, _, r, _, rfl, hr⟩ := iff_mem_trace.mp hm₁;
  have : M.IsFiniteTree r := {}

  have H₁ : r ⊧ ∼□^[(φ.rflSubformula.card + 1)]⊥ := height_lt_iff_satisfies_boxbot (i := r) (n := φ.rflSubformula.card + 1) |>.not.mp $ by
    rw [←Frame.height];
    omega;

  have := GL.Kripke.fintype_completeness_TFAE (φ := ∼□^[(φ.rflSubformula.card + 1)]⊥ ➝ ◇φ.rflSubformula.conj) |>.out 0 2 |>.mp GL.formalized_validates_axiomT_set_in_irrefl_trans_chain;
  have H₂ : r ⊧ ∼□^[(φ.rflSubformula.card + 1)]⊥ ➝ ◇φ.rflSubformula.conj := this M r;
  obtain ⟨a, Rrx, hx⟩ := Satisfies.dia_def.mp $ H₂ H₁;
  replace Rrx : r ≠ a := by rintro rfl; apply M.irrefl _ Rrx;

  have : {k | k ≥ M.height} ⊆ φ.trace := by
    intro k hmk;
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmk;
    apply iff_mem_trace.mpr;
    refine ⟨M.boneLengthening a k, inferInstance, inferInstance, inferInstance, r, ?_, ?_, ?_⟩;
    . apply Model.boneLengthening.isRooted Rrx;
    . apply Model.boneLengthening.eq_height Rrx;
    . exact Model.boneLengthening.mainlemma₂ hx (by grind) r |>.not.mp hr;
  apply Set.Cofinite.subset this;
  apply Set.Finite.subset (s := Finset.range M.height);
  . apply Finset.finite_toSet;
  . intro i;
    simp;

@[grind →]
lemma Formula.trace.finite_of_coinfinite (h_ci : φ.trace.Coinfinite) : φ.trace.Finite := by
  apply or_iff_not_imp_right.mp $ Formula.trace.finite_or_cofinite;
  simpa;

/--
  `L` is contained in `GLα L.trace` when `L.trace` is coinfinite
-/
lemma subset_GLα_of_trace_coinfinite (hL : L.trace.Coinfinite) : L ⊆ Modal.GLα L.trace := by
  intro φ hφ;
  apply Modal.Logic.iff_provable.mp;

  have : φ.trace ⊆ L.trace := subset_of_provable (by grind);
  have : φ.trace.Finite := by
    have : φ.trace.Coinfinite := Set.Coinfinite.subset this hL
    grind
  let Tφ := this.toFinset;

  apply Logic.sumQuasiNormal.iff_provable_finite_provable_letterless ?_ |>.mpr ⟨(Tφ.image TBB), ?_, ?_⟩;
  . grind;
  . simpa [Tφ]
  . apply GL.Kripke.fintype_completeness_TFAE.out 2 0 |>.mp;
    intro M _ _ _ r _ hr;
    have : Fintype M.World := Fintype.ofFinite _;
    apply Formula.satisfies_of_not_mem_trace (n := M.height) |>.mp;
    . replace hr : ∀ n ∈ φ.trace, M.height ≠ n := by
        intro n h;
        apply iff_satisfies_TBB_ne_rank.mp;
        apply Satisfies.fconj_def.mp hr _;
        suffices ∃ m ∈ φ.trace, (□^[m]⊥ : Formula ℕ) = □^[n]⊥ by
          simp only [Finset.mem_image, Set.Finite.mem_toFinset, Tφ];
          use n;
        use n;
      by_contra hC;
      apply hr _ hC rfl;
    . rfl;

/--
  `L` is contained in `GLβMinus L.trace` when `L.trace` is cofinite
-/
lemma subset_GLβMinus_of_trace_cofinite (hL : L.trace.Cofinite) : L ⊆ Modal.GLβMinus L.trace := by
  intro φ hφ;
  apply Modal.Logic.iff_provable.mp;

  have : φ.trace ⊆ L.trace := subset_of_provable (by grind);

  let Tφ := hL.toFinset;

  apply Logic.sumQuasiNormal.iff_provable_finite_provable_letterless ?_ |>.mpr ⟨{∼⩕ n ∈ Tφ, TBB n}, ?_, ?_⟩;
  . grind;
  . simp_all [Set.compl_iUnion, Tφ];
  . apply GL.Kripke.fintype_completeness_TFAE.out 2 0 |>.mp;
    intro M _ _ _ r _ hr;
    have : Fintype M.World := Fintype.ofFinite _;
    apply Formula.satisfies_of_not_mem_trace (n := M.height) |>.mp;
    . replace hr : ∀ (n : ℕ), ∀ x ∈ L, n ∈ x.trace → ¬M.height = n := by
        rintro n ξ hξ₁ hξ₂ rfl;
        obtain ⟨m, hm₁, hm₂⟩ : ∃ m, m ∈ Tφ ∧ r ⊭ TBB m := Satisfies.not_fconj'_def.mp $ Satisfies.not_def.mp $ by
          simpa only [Finset.conj_singleton] using hr;
        replace hm₁ : ∀ i ∈ L, m ∉ i.trace := by simpa [Tφ] using hm₁;
        replace hm₂ : M.height = m := by simpa using iff_satisfies_TBB_ne_rank.not.mp hm₂;
        apply hm₁ ξ;
        . assumption;
        . grind;
      by_contra hC;
      apply hr M.height φ hφ hC rfl;
    . rfl;

@[simp]
lemma eq_GLβMinusOmega : Modal.GLβMinus Set.univ = Set.univ := by
  apply Set.eq_univ_iff_forall.mpr;
  intro φ;
  apply Logic.iff_provable.mp;
  apply Logic.sumQuasiNormal.iff_provable_finite_provable_letterless (by grind;) |>.mpr;
  use {∼⊤};
  constructor;
  . simp;
  . suffices Modal.GL ⊢ ∼⊤ ➝ φ by simpa;
    cl_prover;

end Modal

namespace ProvabilityLogic

open LO.Entailment Entailment.FiniteContext
open FirstOrder FirstOrder.ProvabilityAbstraction
open Arithmetic
open ArithmeticTheory (provabilityLogicOn)
open LO.Modal
open Modal.Kripke
open Formula.Kripke

variable {T U : ArithmeticTheory} [T.Δ₁]
variable {A : Formula ℕ}

lemma provable_TBB_of_mem_trace
  [𝗜𝚺₁ ⪯ T] [𝗜𝚺₁ ⪯ U]
  {L : Logic _} (hPL : L.IsProvabilityLogic T U)
  {n : ℕ} (h : n ∈ L.trace) : L ⊢ Modal.TBB n := by
  obtain ⟨A, hA₁, ⟨M, _, _, _, r, _, rfl, h₂⟩⟩ := by simpa using h;
  replace hA₁ : ∀ f : T.StandardRealization, U ⊢ f A := hPL A |>.mp $ by grind;

  let M₀ := M.extendRoot 1;
  let r₀ : M₀ := Frame.extendRoot.root (n := 1);
  have Rr₀ : ∀ {x : M}, r₀ ≺ x := λ {x} => Frame.root_genaretes'! (r := r₀) x (by simp);

  let S : SolovaySentences T.standardProvability M₀.toFrame r₀ := SolovaySentences.standard T M₀.toFrame;
  have : M₀ ⊧ A ➝ (Modal.TBB M.height) := by
    rintro x hA;
    rcases Nat.lt_trichotomy (Frame.rank x) M.height with h | h | h;
    . intro _;
      exact height_lt_iff_satisfies_boxbot.mp h;
    . exfalso;
      suffices x = r by
        apply h₂;
        apply Kripke.Model.extendRoot.modal_equivalence_original_world.mpr;
        rwa [this] at hA;
      apply Kripke.Frame.extendRoot.iff_eq_height_eq_original_root.mp h;
    . apply iff_satisfies_mem_rank_letterlessSpectrum (by grind) |>.mpr;
      simp;
      omega;
  have : ∀ i : M₀.World, 𝗜𝚺₁ ⊢ S i ➝ S.realization (A ➝ (Modal.TBB M.height)) := by
    rintro (a | i);
    . suffices 𝗜𝚺₁ ⊢ S r₀ ➝ S.realization (TBB M.height) by
        dsimp [Realization.interpret];
        rw [(show Sum.inl a = r₀ by simp [r₀])];
        cl_prover [this]
      have : 𝗜𝚺₁ ⊢ S r₀ ➝ ∼(T.standardProvability) (S.realization (□^[M.height]⊥)) := C!_trans (S.SC2 r₀ r Rr₀) $ contra! $
        prov_distribute_imply' $
        CN!_of_CN!_right $
        S.mainlemma_neg Rr₀ $
        height_lt_iff_satisfies_boxbot.not.mp $ by simp [Frame.extendRoot.eq_original_height_root]
      apply C!_trans this
      simp [Realization.interpret.def_boxItr]
    . apply S.mainlemma Rr₀;
      apply this;
  have : 𝗜𝚺₁ ⊢ (⩖ j, S j) ➝ S.realization (A ➝ (Modal.TBB M.height)) := left_Udisj!_intro _ this
  have : 𝗜𝚺₁ ⊢ S.realization (A ➝ (Modal.TBB M.height)) := by cl_prover [this, S.SC4];
  have : U ⊢ S.realization (Modal.TBB M.height) := by
    have : U ⊢ S.realization A ➝ S.realization (Modal.TBB M.height) := WeakerThan.pbl this;
    cl_prover [this, hA₁ S.realization];
  apply hPL _ |>.mpr;
  grind only [
    Realization.interpret.def_imp,
    Realization.interpret.def_boxItr,
    Realization.interpret.def_box,
    Realization.interpret.def_bot
  ];


/--
  `L` equals `GLα L.trace` when `L.trace` is coinfinite.
  - Corollary 48 in [A.B05]
-/
theorem eq_provablityLogic_GLα_of_coinfinite_trace
  [𝗜𝚺₁ ⪯ T] [𝗜𝚺₁ ⪯ U] [T ⪯ U] -- TODO: `[T ⪯ U]` might not be necessary
  {L : Logic _} (hPL : L.IsProvabilityLogic T U) (hCi : L.trace.Coinfinite)
  : L = Modal.GLα L.trace := by
  haveI := Logic.inst_Cl_of_isProvabilityLogic hPL;
  apply Set.Subset.antisymm;
  . apply subset_GLα_of_trace_coinfinite hCi;
  . intro A;
    suffices Modal.GLα L.trace ⊢ A → L ⊢ A by grind;
    intro hA;
    induction hA using
      Modal.Logic.sumQuasiNormal.rec!_omitSubst_strong (L₁ := Modal.GL) (L₂ := L.trace.image TBB)
      inferInstance $ Logic.substitution_of_letterless $ Modal.TBBSet_letterless
      with
    | mem₁ hA =>
      apply hPL _ |>.mpr;
      intro f;
      exact WeakerThan.pbl $ GL.arithmetical_soundness hA;
    | mem₂ hA =>
      obtain ⟨n, ⟨N, ⟨A, hA₁, hA₂⟩, hN₂⟩, rfl⟩ := hA;
      apply provable_TBB_of_mem_trace hPL;
      simp_all only [Set.mem_iUnion, exists_prop];
      use A;
    | mdp ihAB ihA =>
      exact ihAB ⨀ ihA;

lemma cofinite_of_not_subset_S
  [𝗜𝚺₁ ⪯ T] [𝗜𝚺₁ ⪯ U] [T ⪯ U]
  {L : Logic _} (hPL : L.IsProvabilityLogic T U) (hS : ¬L ⊆ Modal.S)
  : L.trace.Cofinite := by
  contrapose! hS;
  rw [eq_provablityLogic_GLα_of_coinfinite_trace hPL hS];
  simp;

lemma provable_TBBMinus_of_mem_trace
  [𝗜𝚺₁ ⪯ T] [𝗜𝚺₁ ⪯ U] [T ⪯ U]
  {L : Logic _} (hPL : L.IsProvabilityLogic T U) (hS : ¬L ⊆ Modal.S)
  : L ⊢ ∼⩕ i ∈ (cofinite_of_not_subset_S hPL hS).toFinset, TBB i := by
  haveI := Logic.inst_Cl_of_isProvabilityLogic hPL;

  obtain ⟨A, hA₁, hA₂⟩ := Set.not_subset.mp hS;
  replace hA₁ : L ⊢ A := Logic.iff_provable.mpr hA₁;
  replace hA₂ : Modal.GL ⊬ A.rflSubformula.conj ➝ A := Modal.Logic.iff_provable_rflSubformula_GL_provable_S.not.mpr $ Logic.iff_provable.not.mpr hA₂;
  obtain ⟨M₁, _, _, _, r₁, _, hM⟩ := Modal.GL.Kripke.iff_unprovable_exists_fintype_rooted_model.mp hA₂;

  let M₀ := Model.extendRoot M₁ 1;
  let r₀ : M₀.World := Model.extendRoot.root;
  have : Fintype M₀.World := Fintype.ofFinite _

  let R := Set.Finite.inter_of_left (s := (Finset.range M₁.height)) (t := L.trace) (Finset.finite_toSet _) |>.toFinset;
  let B := A ⋏ ⩕ i ∈ R, TBB i;
  have hB : L ⊢ B := by
    suffices L ⊢ A ∧ ∀ i ∈ R, L ⊢ TBB i by
      have ⟨h₁, h₂⟩ := this;
      replace h₂ : L ⊢ ⩕ i ∈ R, TBB i := Entailment.FConj'_iff_forall_provable.mpr h₂;
      cl_prover [h₁, h₂];
    constructor;
    . assumption;
    . rintro i hi;
      apply provable_TBB_of_mem_trace hPL;
      simp_all [R, Logic.trace];

  letI S := SolovaySentences.standard T M₀.toFrame;
  letI Tr := cofinite_of_not_subset_S hPL hS |>.toFinset;

  apply hPL _ |>.mpr;
  intro g;
  apply Realization.iff_provable_letterless_interpret ?_ |>.mp;
  . show U ⊢ S.realization (∼⩕ n ∈ Tr, TBB n);
    apply Entailment.mdp! (φ := S.realization B) ?_ $ hPL _ |>.mp hB S.realization;
    . apply WeakerThan.pbl (𝓢 := 𝗜𝚺₁);
      show 𝗜𝚺₁ ⊢ (S.realization B ➝ S.realization (∼⩕ n ∈ Tr, TBB n));
      apply ?_ ⨀ S.SC4;
      apply left_Udisj!_intro _;
      rintro (a | i);
      . rw [(show Sum.inl a = r₀ by simp [r₀])];
        have H₁ : 𝗜𝚺₁ ⊢ S r₀ ➝ ∼S.realization A := by
          convert SolovaySentences.rfl_mainlemma_neg (T := T) hM A (by simp) $ Satisfies.not_imp_def.mp hM |>.2;
        have H₂ : 𝗜𝚺₁ ⊢ S.realization B ⭤ S.realization A ⋏ S.realization (⩕ n ∈ R, TBB n) := Realization.interpret.iff_provable_and_inside;
        cl_prover [H₁, H₂];
      . suffices 𝗜𝚺₁ ⊢ S i ➝ S.realization (B ➝ (∼⩕ n ∈ Tr, TBB n)) by simpa;
        apply SolovaySentences.mainlemma (S := S) (T := T) (i := i);
        . apply Frame.root_genaretes'!;
          simp;
        . intro h;
          apply Satisfies.not_def.mpr;
          apply Satisfies.not_fconj'_def.mpr;
          use Frame.rank (i : M₀);
          constructor;
          . by_contra hC;
            apply iff_satisfies_TBB_ne_rank (w := (i : M₀)) (n := Frame.rank (i : M₀)) |>.mp;
            . apply Satisfies.fconj'_def.mp $ Satisfies.and_def.mp h |>.2;
              suffices Frame.rank (i : M₀) < M₁.height ∧ Frame.rank (i : M₀) ∈ L.trace by simpa [R];
              constructor;
              . suffices Frame.rank i < M₁.height by calc
                  _ = Frame.rank (i : M₁) := by
                    convert @Frame.extendRoot.eq_original_height (F := M₁.toFrame) (x := i) _ _ _ r₁ _;
                  _ < _                   := this;
                apply Frame.rank_lt_whole_height;
                apply M₁.root_genaretes'!;
                rintro rfl;
                apply Satisfies.not_imp_def.mp hM |>.2;
                apply Model.extendRoot.modal_equivalence_original_world.mpr;
                exact Satisfies.and_def.mp h |>.1;
              . simpa [Tr] using hC;
            . rfl;
          . apply iff_satisfies_TBB_ne_rank.not.mpr;
            simp;
  . apply TBBMinus_letterless';

/--
  `L` equals `GLβMinus L.trace` when `L` is not a subset of `S`.
  - Lemma 49 in [A.B05]
-/
theorem eq_provabilityLogic_GLβMinus_of_not_subset_S
  [𝗜𝚺₁ ⪯ T] [𝗜𝚺₁ ⪯ U] [T ⪯ U]
  {L : Logic _} (hPL : L.IsProvabilityLogic T U) (hS : ¬L ⊆ Modal.S)
  : L = Modal.GLβMinus L.trace (cofinite_of_not_subset_S hPL hS) := by
  haveI := Logic.inst_Cl_of_isProvabilityLogic hPL;

  apply Set.Subset.antisymm;
  . apply subset_GLβMinus_of_trace_cofinite;
    apply cofinite_of_not_subset_S hPL hS;
  . intro A;
    rw [←Logic.iff_provable, ←Logic.iff_provable]
    intro hA;
    induction hA using
      Modal.Logic.sumQuasiNormal.rec!_omitSubst_strong (L₁ := Modal.GL) (L₂ := {∼(⩕ n ∈ (cofinite_of_not_subset_S hPL hS).toFinset, (TBB n))})
      inferInstance (Logic.substitution_of_letterless TBBMinus_letterless) with
    | mem₁ hA =>
      apply hPL _ |>.mpr;
      intro f;
      exact WeakerThan.pbl $ GL.arithmetical_soundness hA;
    | mem₂ hA =>
      replace hA := Logic.iff_provable.mp hA;
      subst hA;
      exact provable_TBBMinus_of_mem_trace hPL hS;
    | mdp ihAB ihA => exact ihAB ⨀ ihA;

end ProvabilityLogic

end LO
