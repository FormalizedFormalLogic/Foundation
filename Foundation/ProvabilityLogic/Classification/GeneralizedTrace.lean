import Foundation.ProvabilityLogic.Classification.LetterlessTrace

namespace LO

namespace Modal

open Kripke

variable {φ ψ : Formula ℕ}

def Formula.gTrace (φ : Formula ℕ) : Set ℕ := { n | ∃ M : Kripke.Model, ∃ r, ∃ _ : M.IsTree r, ∃ _ : Fintype M, (M.finHeight = n ∧ ¬r ⊧ φ) }

lemma satisfies_of_not_mem_gTrace : n ∉ φ.gTrace ↔ (∀ M : Kripke.Model, ∀ r : M, [M.IsTree r] → [Fintype M] → M.finHeight = n → r ⊧ φ) := by
  simp [Formula.gTrace];

@[grind]
lemma Formula.eq_gTrace_trace_of_letterless {φ : Formula ℕ} (φ_letterless : φ.letterless) : φ.gTrace = φ.trace := by
  ext n;
  apply Iff.trans ?_ (Kripke.spectrum_TFAE φ_letterless (n := n) |>.out 1 0 |>.not);
  constructor;
  . rintro ⟨M, r, _, M_fintype, rfl, h⟩;
    push_neg;
    refine ⟨M, r, {}, ?_, r, ?_, ?_⟩;
    . assumption;
    . rfl;
    . assumption;
  . push_neg;
    rintro ⟨M, r, _, _, w, rfl, h⟩;
    refine ⟨M.pointGenerate w, Model.pointGenerate.root, {}, ?_, ?_, ?_⟩;
    . exact Fintype.ofFinite _;
    . sorry;
    . exact Model.pointGenerate.modal_equivalent_at_root _ |>.not.mpr h;

open Formula.Kripke

/-
lemma Formula.gTrace_and : (φ ⋏ ψ).gTrace = φ.gTrace ∪ ψ.gTrace := by
  ext n;
  calc
    _ ↔ ∃ M : Kripke.Model, ∃ r, ∃ _ : M.IsTree r, ∃ _ : Fintype M, ∃ w : M, Frame.World.finHeight w = n ∧ ¬w ⊧ (φ ⋏ ψ) := by simp [Formula.gTrace]
    _ ↔
      (∃ M : Kripke.Model, ∃ r, ∃ _ : M.IsTree r, ∃ _ : Fintype M, ∃ w : M, Frame.World.finHeight w = n ∧ ¬w ⊧ φ) ∨
      (∃ M : Kripke.Model, ∃ r, ∃ _ : M.IsTree r, ∃ _ : Fintype M, ∃ w : M, Frame.World.finHeight w = n ∧ ¬w ⊧ ψ) := by
      constructor;
      . rintro ⟨M, r, _, _, w, _, h⟩;
        replace h := Satisfies.and_def.not.mp h;
        set_option push_neg.use_distrib true in push_neg at h;
        rcases h with (h | h);
        . left; tauto;
        . right; tauto;
      . rintro (⟨M, r, _, _, w, _, h⟩ | ⟨M, r, _, _, w, _, h⟩) <;>
        . refine ⟨M, r, by assumption, by assumption, w, by assumption, ?_⟩;
          apply Satisfies.and_def.not.mpr;
          tauto;
    _ ↔ _ := by simp [Formula.gTrace];
-/

abbrev FormulaSet.gTrace (X : FormulaSet ℕ) : Set ℕ := ⋃ φ ∈ X, φ.gTrace

@[simp]
lemma FormulaSet.gTrace_empty : (∅ : FormulaSet ℕ).gTrace = ∅ := by simp [FormulaSet.gTrace];

abbrev Logic.trace (L : Logic ℕ) : Set ℕ := FormulaSet.gTrace L

lemma GL.eq_trace_ext
  {X : FormulaSet ℕ}
  (hX : ∀ ξ ∈ X, ∀ s : Substitution _, ξ⟦s⟧ ∈ X)
  : (Modal.GL.sumQuasiNormal X).trace = X.gTrace := by
  ext n;
  suffices (∃ φ ∈ Modal.GL.sumQuasiNormal X, n ∈ φ.gTrace) ↔ (∃ φ ∈ X, n ∈ φ.gTrace) by
    simpa [Logic.trace];
  constructor;
  . rintro ⟨φ, hφ₁, hφ₂⟩;
    obtain ⟨Y, hY₁, hY₂⟩ := Logic.sumQuasiNormal.iff_provable_finite_provable hX |>.mp $ Logic.iff_provable.mpr hφ₁;
    sorry;
  . rintro ⟨φ, hφ₁, hφ₂⟩;
    use φ;
    constructor;
    . apply Logic.iff_provable.mp;
      apply Logic.sumQuasiNormal.mem₂!;
      simpa [Logic.iff_provable];
    . assumption;

lemma Logic.sumQuasiNormal.with_empty [DecidableEq α] {L₁ : Logic α} [L₁.IsQuasiNormal] : L₁.sumQuasiNormal ∅ = L₁ := by
  ext φ;
  suffices L₁.sumQuasiNormal ∅ ⊢! φ ↔ L₁ ⊢! φ by simpa [Logic.iff_provable];
  constructor;
  . intro h;
    induction h using Logic.sumQuasiNormal.rec! with
    | mem₁ => assumption;
    | mem₂ => simp_all;
    | mdp ihφψ ihφ => cl_prover [ihφψ, ihφ];
    | subst ihφ => exact Logic.subst! _ ihφ;
  . intro h;
    exact Entailment.WeakerThan.pbl h;

lemma GL.unprovable_of_exists_trace (φ_letterless : φ.letterless) : (∃ n, n ∈ φ.trace) → Modal.GL ⊬ φ := by
  contrapose!;
  intro h;
  have := Modal.iff_GL_provable_spectrum_Univ φ_letterless |>.mp (by simpa using h);
  simp_all [Formula.trace];

@[simp]
lemma TBBMinus_trace (hβ : βᶜ.Finite) : (∼⩕ n ∈ hβ.toFinset, TBB n).trace = β := by
  simp [Formula.trace, TBBMinus_spectrum']

@[simp]
lemma GL.eq_trace_emptyset : Modal.GL.trace = ∅ := by
  rw [←Logic.sumQuasiNormal.with_empty (L₁ := Modal.GL)]
  simpa using GL.eq_trace_ext (X := ∅) (by simp);

@[simp]
lemma GLα.eq_trace {α : Set ℕ} : (Modal.GLα α).trace = α := by
  apply Eq.trans $ GL.eq_trace_ext $ by grind;
  simp [FormulaSet.gTrace, Formula.eq_gTrace_trace_of_letterless];

@[simp]
lemma GLβMinus.eq_trace {β : Set ℕ} (hβ : βᶜ.Finite := by grind) : (Modal.GLβMinus β).trace = β := by
  apply Eq.trans $ GL.eq_trace_ext $ by grind;
  simp [FormulaSet.gTrace, Formula.eq_gTrace_trace_of_letterless];

attribute [grind] Modal.Logic.iff_provable

@[simp, grind] lemma S.provable_TBB {n : ℕ} : Modal.S ⊢! TBB n := by simp [TBB]

@[simp, grind]
lemma subset_GLα_S : Modal.GLα α ⊆ Modal.S := by
  intro φ;
  suffices Modal.GLα α ⊢! φ → Modal.S ⊢! φ by grind;
  intro hφ;
  induction hφ using Modal.Logic.sumQuasiNormal.rec! with
  | mem₁ hφ => exact Entailment.WeakerThan.pbl hφ;
  | mem₂ hφ => obtain ⟨_, _, rfl⟩ := hφ; simp;
  | mdp ihφψ ihφ => exact ihφψ ⨀ ihφ;
  | subst ihφ => exact Logic.subst! _ ihφ;

@[grind]
lemma Logic.weakerThan_of_subset {L₁ L₂ : Logic α} (h : L₁ ⊆ L₂) : L₁ ⪯ L₂ := by
  constructor;
  simpa [Entailment.theory];

@[grind]
lemma Logic.strictWeakerThan_of_ssubset {L₁ L₂ : Logic α} (h : L₁ ⊂ L₂) : L₁ ⪱ L₂ := by
  simp_all [Entailment.strictlyWeakerThan_iff, Set.ssubset_iff_exists];
  aesop;

instance : Modal.GLα α ⪯ Modal.S := by grind

@[simp, grind]
lemma Logic.subset_of_weakerThan {L₁ L₂ : Logic α} [L₁ ⪯ L₂] : L₁ ⊆ L₂ := by
  intro φ;
  suffices L₁ ⊢! φ → L₂ ⊢! φ by grind;
  exact Entailment.WeakerThan.pbl;

@[simp]
lemma S.eq_trace : Modal.S.trace = Set.univ := by
  suffices ∀ (x : ℕ), ∃ i ∈ Modal.S, x ∈ i.gTrace by simpa [Set.eq_univ_iff_forall]
  intro n;
  use (TBB n);
  constructor;
  . grind;
  . simp [Formula.eq_gTrace_trace_of_letterless];

variable {L : Logic ℕ} {φ : Formula ℕ}


lemma subset_of_provable (h : L ⊢! φ) : φ.gTrace ⊆ L.trace := by
  intro n h;
  suffices ∃ i ∈ L, n ∈ i.gTrace by simpa [Logic.trace, FormulaSet.gTrace];
  use φ;
  grind;

abbrev _root_.Set.Cofinite (s : Set α) := sᶜ.Finite
abbrev _root_.Set.Coinfinite (s : Set α) := sᶜ.Infinite

lemma _root_.Set.Cofinite.subset {s t : Set α} (h : s ⊆ t) : s.Cofinite → t.Cofinite := by
  intro h;
  apply Set.Finite.subset (s := sᶜ) h;
  tauto_set;

lemma _root_.Set.Coinfinite.subset {s t : Set α} (h : t ⊆ s) : s.Coinfinite → t.Coinfinite := by
  contrapose!;
  simpa using Set.Cofinite.subset h;

@[grind]
lemma Formula.gTrace.finite_or_cofinite : φ.gTrace.Finite ∨ φ.gTrace.Cofinite := by
  sorry;

@[grind]
lemma Formula.gTrace.finite_of_coinfinite (h_ci : φ.gTrace.Coinfinite) : φ.gTrace.Finite := by
  rcases Formula.gTrace.finite_or_cofinite (φ := φ) with h | h_cf;
  . assumption;
  . exfalso;
    apply h_ci;
    exact h_cf;

@[simp]
lemma TBB_injective : Function.Injective TBB := by sorry;

lemma iff_satisfies_TBB_root_ne_finHeight {M : Model} {r : M} [M.IsTree r] [Fintype M] {n : ℕ} : r ⊧ (TBB n) ↔ M.finHeight ≠ n := by
  apply Iff.trans $ iff_satisfies_mem_finHeight_spectrum (φ := TBB n) (w := r)
  simp;
  tauto;

lemma subset_GLα_of_trace_coinfinite (hL : L.trace.Coinfinite) : L ⊆ Modal.GLα L.trace := by
  intro φ hφ;
  apply Modal.Logic.iff_provable.mp;

  have : φ.gTrace ⊆ L.trace := subset_of_provable (by grind);
  have : φ.gTrace.Finite := by
    have : φ.gTrace.Coinfinite := Set.Coinfinite.subset this hL
    grind
  let Tφ := this.toFinset;

  apply Logic.sumQuasiNormal.iff_provable_finite_provable_letterless ?_ |>.mpr ⟨(Tφ.image TBB), ?_, ?_⟩;
  . grind;
  . simpa [Tφ, Set.preimage_image_eq L.trace TBB_injective];
  . apply GL.Kripke.tree_completeness_TFAE.out 3 0 |>.mp;
    intro M r _ hr;
    have : Fintype M.World := Fintype.ofFinite _;
    apply satisfies_of_not_mem_gTrace (n := M.finHeight) |>.mp;
    . replace hr : ∀ n ∈ φ.gTrace, M.finHeight ≠ n := by
        intro n h;
        apply iff_satisfies_TBB_root_ne_finHeight.mp;
        apply Satisfies.fconj_def.mp hr _;
        suffices ∃ m ∈ φ.gTrace, □^[m]⊥ = □^[n]⊥ by simpa [Tφ];
        use n;
      by_contra hC;
      apply hr _ hC rfl;
    . rfl;


lemma Formula.Kripke.Satisfies.fconj'_def {M : Kripke.Model} {w : M} {X : Finset α} {ι : α → Formula ℕ} : w ⊧ (⩕ i ∈ X, ι i) ↔ ∀ i ∈ X, w ⊧ ι i := by
  sorry;

lemma Formula.Kripke.Satisfies.not_fconj'_def {M : Kripke.Model} {w : M} {X : Finset α} {ι : α → Formula ℕ} : ¬(w ⊧ (⩕ i ∈ X, ι i)) ↔ ∃ i ∈ X, ¬(w ⊧ ι i) := by
  simpa using Formula.Kripke.Satisfies.fconj'_def.not;


lemma subset_GLβMinus_of_trace_cofinite (hL : L.trace.Cofinite) : L ⊆ Modal.GLβMinus L.trace := by
  intro φ hφ;
  apply Modal.Logic.iff_provable.mp;

  have : φ.gTrace ⊆ L.trace := subset_of_provable (by grind);

  let Tφ := hL.toFinset;

  apply Logic.sumQuasiNormal.iff_provable_finite_provable_letterless ?_ |>.mpr ⟨{∼⩕ n ∈ Tφ, TBB n}, ?_, ?_⟩;
  . grind;
  . simp_all [Set.compl_iUnion, Tφ];
  . apply GL.Kripke.tree_completeness_TFAE.out 3 0 |>.mp;
    intro M r _ hr;
    have : Fintype M.World := Fintype.ofFinite _;
    apply satisfies_of_not_mem_gTrace (n := M.finHeight) |>.mp;
    . replace hr : ∀ (n : ℕ), ∀ x ∈ L, n ∈ x.gTrace → ¬M.finHeight = n := by
        rintro n ξ hξ₁ hξ₂ rfl;
        obtain ⟨m, hm₁, hm₂⟩ : ∃ m, m ∈ Tφ ∧ ¬r ⊧ TBB m := Satisfies.not_fconj'_def.mp $ Satisfies.not_def.mp $ by simpa using hr;
        replace hm₁ : ∀ i ∈ L, m ∉ i.gTrace := by simpa [Tφ] using hm₁;
        replace hm₂ : M.finHeight = m := by simpa using iff_satisfies_TBB_root_ne_finHeight.not.mp hm₂;
        apply hm₁ ξ;
        . assumption;
        . grind;
      by_contra hC;
      apply hr M.finHeight φ hφ hC rfl;
    . rfl;

namespace Kripke.Frame

variable {F : Frame} {r : F} [Fintype F.World] [F.IsTree r]

lemma eq_finHeight_root : Frame.World.finHeight x = F.finHeight ↔ x = r := by
  constructor;
  . rintro h;
    contrapose! h;
    apply Nat.ne_of_lt;
    apply Frame.World.finHeight_lt_whole_finHeight;
    apply F.root_genaretes'!;
    assumption;
  . tauto;

lemma terminal_rel_finHeight {x y : F} (h : x ≺^[World.finHeight x] y) : ∀ z, ¬y ≺ z := by
  intro z Ryz;
  suffices World.finHeight x + 1 ≤ World.finHeight x by omega;
  exact le_finHeight_iff_relItr.mpr ⟨z, HRel.Iterate.forward.mpr ⟨y, h, Ryz⟩⟩;

lemma extendRoot.eq_original_finHeight {x : F} : Frame.World.finHeight (x : F.extendRoot 1) = Frame.World.finHeight x := by
  apply finHeight_eq_iff_relItr.mpr;
  constructor;
  . obtain ⟨y, Rxy⟩ := exists_terminal (i := x);
    use y;
    apply extendRoot.embed_rel_iterate_embed_iff_rel.mpr;
    exact Rxy;
  . rintro (_ | y) Rxy (_ | z);
    . simp;
    . -- TODO: extract no loop lemma (x ≺^[n] i cannot happen where x is original and i is new elements by extension)
      exfalso;
      have : extendRoot.root ≺ (x : F.extendRoot 1) := Frame.root_genaretes'! (F := F.extendRoot 1) x (by simp);
      have : (x : F.extendRoot 1) ≺ x :=
        HRel.Iterate.unwrap_of_trans_of_pos (by omega) $
        HRel.Iterate.comp (m := 1) |>.mp ⟨_, Rxy, by simpa⟩;
      exact Frame.irrefl _ this;
    . apply Frame.asymm;
      exact Frame.root_genaretes'! (F := F.extendRoot 1) y (by simp);
    . have := terminal_rel_finHeight $ extendRoot.embed_rel_iterate_embed_iff_rel.mp Rxy;
      exact extendRoot.embed_rel_embed_iff_rel.not.mpr $ this z;

lemma extendRoot.eq_original_finHeight_root : Frame.World.finHeight (r : F.extendRoot 1) = F.finHeight := eq_original_finHeight

@[grind]
lemma extendRoot.iff_eq_finHeight_eq_original_root {x : F.extendRoot 1} : Frame.World.finHeight x = F.finHeight ↔ x = r := by
  constructor;
  . rcases x with (a | x);
    . intro h;
      have := h ▸ finHeight₁ (F := F);
      simp [Frame.finHeight] at this;
    . intro h;
      suffices x = r by simp [this];
      apply Frame.eq_finHeight_root.mp;
      exact h ▸ Frame.extendRoot.eq_original_finHeight.symm;
  . rintro rfl;
    exact eq_original_finHeight_root;

end Kripke.Frame

namespace Logic

variable {L L₁ L₂ : Logic α} {φ ψ : Formula α} {s : Substitution α}

inductive sumQuasiNormal' (L₁ L₂ : Logic α) : Logic α
| mem₁ {φ} (s : Substitution _) : L₁ ⊢! φ → sumQuasiNormal' L₁ L₂ (φ⟦s⟧)
| mem₂ {φ} (s : Substitution _) : L₂ ⊢! φ → sumQuasiNormal' L₁ L₂ (φ⟦s⟧)
| mdp {φ ψ : Formula α} : sumQuasiNormal' L₁ L₂ (φ ➝ ψ) → sumQuasiNormal' L₁ L₂ φ → sumQuasiNormal' L₁ L₂ ψ

namespace sumQuasiNormal'

@[grind]
lemma mem₁! (h : L₁ ⊢! φ) : sumQuasiNormal' L₁ L₂ ⊢! (φ⟦s⟧) := by
  apply iff_provable.mpr;
  apply sumQuasiNormal'.mem₁ _ h;

@[grind]
lemma mem₁!_nosub (h : L₁ ⊢! φ) : sumQuasiNormal' L₁ L₂ ⊢! φ := by
  simpa using mem₁! (s := Substitution.id) h;

@[grind]
lemma mem₂! (h : L₂ ⊢! φ) : sumQuasiNormal' L₁ L₂ ⊢! (φ⟦s⟧) := by
  apply iff_provable.mpr;
  apply sumQuasiNormal'.mem₂ _ h;

@[grind]
lemma mem₂!_nosub (h : L₂ ⊢! φ) : sumQuasiNormal' L₁ L₂ ⊢! φ := by
  simpa using mem₂! (s := Substitution.id) h;

instance : Entailment.ModusPonens (sumQuasiNormal' L₁ L₂) where
  mdp := by rintro φ ψ ⟨hφψ⟩ ⟨hφ⟩; exact ⟨sumQuasiNormal'.mdp hφψ hφ⟩;

lemma rec!
  {motive : (φ : Formula α) → ((sumQuasiNormal' L₁ L₂) ⊢! φ) → Sort}
  (mem₁  : ∀ {φ}, ∀ s, (h : L₁ ⊢! φ) → motive (φ⟦s⟧) (mem₁! h))
  (mem₂  : ∀ {φ}, ∀ s, (h : L₂ ⊢! φ) → motive (φ⟦s⟧) (mem₂! h))
  (mdp   : ∀ {φ ψ : Formula α},
           {hφψ : (sumQuasiNormal' L₁ L₂) ⊢! (φ ➝ ψ)} → {hφ : (sumQuasiNormal' L₁ L₂) ⊢! φ} →
          motive (φ ➝ ψ) hφψ → motive φ hφ → motive ψ (hφψ ⨀ hφ)
  )
  : ∀ {φ}, (h : sumQuasiNormal' L₁ L₂ ⊢! φ) → motive φ h := by
  intro φ hφ;
  induction (iff_provable.mp $ hφ) with
  | mdp hφψ hφ ihφψ ihφ =>
    apply mdp;
    . apply ihφψ;
    . apply ihφ;
    . apply iff_provable.mpr; assumption;
    . apply iff_provable.mpr; assumption;
  | _ => grind;

instance : (sumQuasiNormal' L₁ L₂).Substitution where
  subst s := by
    rintro ⟨hφ⟩;
    constructor;
    induction hφ with
    | mem₁ s' h => simpa using mem₁ (s := s' ∘ s) h
    | mem₂ s' h => simpa using mem₂ (s := s' ∘ s) h
    | mdp _ _ ihφψ ihφ => exact mdp ihφψ ihφ

end sumQuasiNormal'


attribute [grind] Logic.sumQuasiNormal.mem₁! Logic.sumQuasiNormal.mem₂!

lemma eq_sumQuasiNormal_sumQuasiNormal' : Logic.sumQuasiNormal L₁ L₂ = Logic.sumQuasiNormal' L₁ L₂ := by
  ext φ;
  suffices (Logic.sumQuasiNormal L₁ L₂ ⊢! φ) ↔ (Logic.sumQuasiNormal' L₁ L₂ ⊢! φ) by grind;
  constructor;
  . intro h;
    induction h using Logic.sumQuasiNormal.rec! with
    | @subst ψ s _ ihφ => exact subst! _ ihφ;
    | mdp ihφψ ihφ => exact ihφψ ⨀ ihφ;
    | _ => grind;
  . intro h;
    induction h using Logic.sumQuasiNormal'.rec! with
    | mdp ihφψ ihφ => exact ihφψ ⨀ ihφ;
    | _ => apply subst!; grind;

@[grind]
lemma iff_provable_sumQuasiNormal'_provable_sumQuasiNormal : (sumQuasiNormal' L₁ L₂ ⊢! φ) ↔ (sumQuasiNormal L₁ L₂ ⊢! φ) := by
  rw [eq_sumQuasiNormal_sumQuasiNormal'];

lemma sumQuasiNormal.rec!_omitSubst
  {motive : (φ : Formula α) → ((sumQuasiNormal L₁ L₂) ⊢! φ) → Sort}
  (mem₁  : ∀ {φ}, ∀ s, (h : L₁ ⊢! φ) → motive (φ⟦s⟧) (subst! s $ mem₁! h))
  (mem₂  : ∀ {φ}, ∀ s, (h : L₂ ⊢! φ) → motive (φ⟦s⟧) (subst! s $ mem₂! h))
  (mdp   : ∀ {φ ψ : Formula α},
           {hφψ : (sumQuasiNormal L₁ L₂) ⊢! (φ ➝ ψ)} → {hφ : (sumQuasiNormal L₁ L₂) ⊢! φ} →
           motive (φ ➝ ψ) hφψ → motive φ hφ → motive ψ (hφψ ⨀ hφ)
  )
  : ∀ {φ}, (h : sumQuasiNormal L₁ L₂ ⊢! φ) → motive φ h := by
  intro φ hφ;
  induction (iff_provable_sumQuasiNormal'_provable_sumQuasiNormal.mpr hφ) using Logic.sumQuasiNormal'.rec! with
  | mem₁ s h => grind;
  | mem₂ s h => grind;
  | @mdp _ _ hφψ hφ ihφψ ihφ => exact mdp (ihφψ $ by grind) (ihφ $ by grind);

attribute [grind] Logic.subst!

@[grind]
def substitution_of_letterless (L_letterless : FormulaSet.letterless L) : L.Substitution where
  subst s := by
    rintro ⟨hφ⟩;
    constructor;
    simpa [Formula.subst.subst_letterless (s := s) $ L_letterless _ hφ];

lemma sumQuasiNormal.rec!_omitSubst₁ (hL₁ : L₁.Substitution)
  {motive : (φ : Formula α) → ((sumQuasiNormal L₁ L₂) ⊢! φ) → Sort}
  (mem₁  : ∀ {φ}, (h : L₁ ⊢! φ) → motive φ (mem₁! h))
  (mem₂  : ∀ {φ}, ∀ s, (h : L₂ ⊢! φ) → motive (φ⟦s⟧) (subst! s $ mem₂! h))
  (mdp   : ∀ {φ ψ : Formula α},
           {hφψ : (sumQuasiNormal L₁ L₂) ⊢! (φ ➝ ψ)} → {hφ : (sumQuasiNormal L₁ L₂) ⊢! φ} →
           motive (φ ➝ ψ) hφψ → motive φ hφ → motive ψ (hφψ ⨀ hφ)
  )
  : ∀ {φ}, (h : sumQuasiNormal L₁ L₂ ⊢! φ) → motive φ h := by
  apply sumQuasiNormal.rec!_omitSubst;
  . intro φ s h;
    apply mem₁;
    grind;
  . assumption;
  . assumption;

lemma sumQuasiNormal.rec!_omitSubst₂ (hL₂ : L₂.Substitution)
  {motive : (φ : Formula α) → ((sumQuasiNormal L₁ L₂) ⊢! φ) → Sort}
  (mem₁  : ∀ {φ}, ∀ s, (h : L₁ ⊢! φ) → motive (φ⟦s⟧) (subst! s $ mem₁! h))
  (mem₂  : ∀ {φ}, (h : L₂ ⊢! φ) → motive φ (mem₂! h))
  (mdp   : ∀ {φ ψ : Formula α},
           {hφψ : (sumQuasiNormal L₁ L₂) ⊢! (φ ➝ ψ)} → {hφ : (sumQuasiNormal L₁ L₂) ⊢! φ} →
           motive (φ ➝ ψ) hφψ → motive φ hφ → motive ψ (hφψ ⨀ hφ)
  )
  : ∀ {φ}, (h : sumQuasiNormal L₁ L₂ ⊢! φ) → motive φ h := by
  simp_all only [Logic.sumQuasiNormal.symm (L₁ := L₁) (L₂ := L₂)]
  apply sumQuasiNormal.rec!_omitSubst₁ <;> assumption;

lemma sumQuasiNormal.rec!_omitSubst_strong (hL₁ : L₁.Substitution) (hL₂ : L₂.Substitution)
  {motive : (φ : Formula α) → ((sumQuasiNormal L₁ L₂) ⊢! φ) → Sort}
  (mem₁  : ∀ {φ}, (h : L₁ ⊢! φ) → motive φ (mem₁! h))
  (mem₂  : ∀ {φ}, (h : L₂ ⊢! φ) → motive φ (mem₂! h))
  (mdp   : ∀ {φ ψ : Formula α},
           {hφψ : (sumQuasiNormal L₁ L₂) ⊢! (φ ➝ ψ)} → {hφ : (sumQuasiNormal L₁ L₂) ⊢! φ} →
           motive (φ ➝ ψ) hφψ → motive φ hφ → motive ψ (hφψ ⨀ hφ)
  )
  : ∀ {φ}, (h : sumQuasiNormal L₁ L₂ ⊢! φ) → motive φ h := by
  apply sumQuasiNormal.rec!_omitSubst;
  . intro φ h _; apply mem₁; grind;
  . intro φ h _; apply mem₂; grind;
  . assumption;

end Logic


end Modal

namespace ProvabilityLogic

open LO.Entailment Entailment.FiniteContext
open FirstOrder Arithmetic
open ArithmeticTheory (ProvabilityLogic)
open Modal
open Modal.Kripke
open Formula.Kripke

variable {T U : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T ⪯ U] {A : Formula ℕ}

lemma provable_TBB_of_mem_trace {n : ℕ} (h : n ∈ (T.ProvabilityLogic U).trace) : T.ProvabilityLogic U ⊢! Modal.TBB n := by
  have : 𝗜𝚺₁ ⪯ U := WeakerThan.trans (𝓣 := T) inferInstance inferInstance;

  obtain ⟨A, hA₁, ⟨M, r, _, _, rfl, h₂⟩⟩ := by simpa using h;
  replace hA₁ : ∀ f : T.StandardRealization, U ⊢!. f A := ProvabilityLogic.provable_iff.mp (by grind);

  let M₀ := M.extendRoot 1;
  let r₀ : M₀ := Frame.extendRoot.root
  have Rr₀ : ∀ {x : M}, r₀ ≺ x := λ {x} => Frame.root_genaretes'! (r := r₀) x (by simp)

  have : M₀.IsFiniteTree r₀ := {};
  let S : SolovaySentences T.standardProvability M₀.toFrame r₀ := SolovaySentences.standard T M₀.toFrame;

  have : M₀ ⊧ A ➝ (Modal.TBB M.finHeight) := by
    rintro x hA;
    rcases Nat.lt_trichotomy (Frame.World.finHeight x) M.finHeight with h | h | h;
    . intro _;
      exact finHeight_lt_iff_satisfies_boxbot.mp h;
    . exfalso;
      suffices x = r by
        apply h₂;
        apply Kripke.Model.extendRoot.modal_equivalence_original_world.mpr;
        rwa [this] at hA;
      apply Kripke.Frame.extendRoot.iff_eq_finHeight_eq_original_root.mp h;
    . apply iff_satisfies_mem_finHeight_spectrum (by grind) |>.mpr;
      simp;
      omega;
  have : ∀ i : M₀.World, 𝗜𝚺₁ ⊢!. S i ➝ S.realization (A ➝ (Modal.TBB M.finHeight)) := by
    rintro (a | i);
    . suffices 𝗜𝚺₁ ⊢!. S r₀ ➝ S.realization (TBB M.finHeight) by
        dsimp [Realization.interpret];
        rw [(show Sum.inl a = r₀ by simp [r₀])];
        cl_prover [this]
      have : 𝗜𝚺₁ ⊢!. S r₀ ➝ ∼(T.standardProvability) (S.realization (□^[M.finHeight]⊥)) := C!_trans (S.SC2 r₀ r Rr₀) $ contra! $
        T.standardProvability.prov_distribute_imply' $
        CN!_of_CN!_right $
        S.mainlemma_neg Rr₀ $
        finHeight_lt_iff_satisfies_boxbot.not.mp $ by simp [Frame.extendRoot.eq_original_finHeight_root]
      apply C!_trans this
      simp [Realization.interpret.def_boxItr]
    . apply S.mainlemma Rr₀;
      apply this;
  have : 𝗜𝚺₁ ⊢!. (⩖ j, S j) ➝ S.realization (A ➝ (Modal.TBB M.finHeight)) := left_Udisj!_intro _ this
  have : 𝗜𝚺₁ ⊢!. S.realization (A ➝ (Modal.TBB M.finHeight)) := by cl_prover [this, S.SC4];

  have : U ⊢!. S.realization (Modal.TBB M.finHeight) := by
    have : U ⊢!. S.realization A ➝ S.realization (Modal.TBB M.finHeight) := WeakerThan.pbl this;
    cl_prover [this, hA₁ S.realization];
  apply ProvabilityLogic.provable_iff.mpr;
  intro g;
  simpa [Realization.letterless_interpret (A := Modal.TBB _) (by grind)] using this;

lemma eq_provablityLogic_GLα_of_coinfinite_trace (h : (T.ProvabilityLogic U).trace.Coinfinite) : T.ProvabilityLogic U = Modal.GLα (T.ProvabilityLogic U).trace := by
  apply Set.Subset.antisymm;
  . apply subset_GLα_of_trace_coinfinite h;
  . intro A;
    suffices Modal.GLα (T.ProvabilityLogic U).trace ⊢! A → T.ProvabilityLogic U ⊢! A by grind;
    intro hA;
    induction hA using Modal.Logic.sumQuasiNormal.rec!_omitSubst_strong (L₁ := Modal.GL) (L₂ := (T.ProvabilityLogic U).trace.image TBB) inferInstance (Logic.substitution_of_letterless (by grind)) with
    | mem₁ hA =>
      apply ProvabilityLogic.provable_iff.mpr;
      intro f;
      exact WeakerThan.pbl $ GL.arithmetical_soundness hA;
    | mem₂ hA =>
      replace hA := Modal.Logic.iff_provable.mp hA;
      obtain ⟨n, ⟨N, ⟨A, hA₁, hA₂⟩, hN₂⟩, rfl⟩ := hA;
      apply provable_TBB_of_mem_trace;
      simp_all only [Set.mem_iUnion, exists_prop];
      use A;
    | mdp ihAB ihA => exact ProvabilityLogic.mdp ihAB ihA;

lemma eq_provabilityLogic_GLβMinus_of_not_subset_S (h : ¬(T.ProvabilityLogic U) ⊆ Modal.S) : ∃ _ : (T.ProvabilityLogic U).trace.Cofinite, T.ProvabilityLogic U = Modal.GLβMinus (T.ProvabilityLogic U).trace := by
  refine ⟨?_, ?_⟩;
  . contrapose! h;
    rw [eq_provablityLogic_GLα_of_coinfinite_trace h];
    simp;
  . sorry;

end ProvabilityLogic

end LO
