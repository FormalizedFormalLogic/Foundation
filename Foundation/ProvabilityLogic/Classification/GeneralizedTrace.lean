import Foundation.ProvabilityLogic.Classification.LetterlessTrace
import Foundation.Modal.Boxdot.GL_S
import Foundation.Modal.Logic.SumQuasiNormal


namespace Set

abbrev Cofinite (s : Set α) := sᶜ.Finite

abbrev Coinfinite (s : Set α) := sᶜ.Infinite

lemma Cofinite.subset {s t : Set α} (h : s ⊆ t) : s.Cofinite → t.Cofinite := by
  intro h;
  apply Set.Finite.subset (s := sᶜ) h;
  tauto_set;

lemma Coinfinite.subset {s t : Set α} (h : t ⊆ s) : s.Coinfinite → t.Coinfinite := by
  contrapose!;
  simpa using Set.Cofinite.subset h;

@[grind] lemma univ_cofinite : (Set.univ (α := α)).Cofinite := by simp [Set.Cofinite];

end Set


namespace LO

namespace Entailment

variable {F : Type*} [LogicalConnective F]
         {S : Type*} [Entailment F S]
         {𝓢 : S} [Entailment.Minimal 𝓢]

lemma FConj'_iff_forall_provable [DecidableEq F] {s : Finset α} {ι : α → F} : (𝓢 ⊢! ⩕ i ∈ s, ι i) ↔ (∀ i ∈ s, 𝓢 ⊢! ι i) := by
  have : 𝓢 ⊢! ⋀(s.toList.map ι) ↔ ∀ i ∈ s, 𝓢 ⊢! ι i := by simpa using Conj₂!_iff_forall_provable (Γ := s.toList.map ι);
  apply Iff.trans ?_ this;
  simp [Finset.conj', List.conj'];

end Entailment



namespace Modal

variable {φ ψ : Formula ℕ}

open Kripke

namespace Kripke.Frame

variable {F : Frame} {r x y : F} [Fintype F] [F.IsTree r]

lemma eq_finHeight_root : Frame.World.finHeight x = F.finHeight ↔ x = r := by
  constructor;
  . rintro h;
    contrapose! h;
    apply Nat.ne_of_lt;
    apply Frame.World.finHeight_lt_whole_finHeight;
    apply F.root_genaretes'!;
    assumption;
  . tauto;

lemma terminal_rel_finHeight (h : x ≺^[World.finHeight x] y) : ∀ z, ¬y ≺ z := by
  intro z Ryz;
  suffices World.finHeight x + 1 ≤ World.finHeight x by omega;
  exact le_finHeight_iff_relItr.mpr ⟨z, HRel.Iterate.forward.mpr ⟨y, h, Ryz⟩⟩;

lemma extendRoot.eq_original_finHeight : Frame.World.finHeight (x : F.extendRoot 1) = Frame.World.finHeight x := by
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

instance [Fintype F] : Fintype (F↾x) := by sorry;

instance [F.IsTree r] : (F↾x).IsTree ⟨x, by tauto⟩ := by constructor;

lemma pointGenerate.eq_original_finHeight (hxy : y = x ∨ x ≺^+ y) : Frame.World.finHeight (F := F↾x) (⟨y, hxy⟩) = Frame.World.finHeight y := by
  rcases hxy with rfl | Rxy;
  . sorry;
  . sorry;

end Kripke.Frame


def Formula.gTrace (φ : Formula ℕ) : Set ℕ := { n | ∃ M : Kripke.Model, ∃ r, ∃ _ : M.IsTree r, ∃ _ : Fintype M, (M.finHeight = n ∧ ¬r ⊧ φ) }

lemma iff_mem_gTrace {n : ℕ} : n ∈ φ.gTrace ↔ ∃ M : Kripke.Model, ∃ r : M, ∃ _ : M.IsTree r, ∃ _ : Fintype M, M.finHeight = n ∧ ¬r ⊧ φ := by
  simp [Formula.gTrace];

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
  . dsimp [Formula.gTrace];
    contrapose!;
    rintro h M r _ _ x rfl;
    apply Model.pointGenerate.modal_equivalent' x ⟨x, by tauto⟩ |>.mp;
    apply h;
    apply Frame.pointGenerate.eq_original_finHeight;

open Formula.Kripke

@[simp, grind] lemma Formula.gTrace_bot : (⊥ : Formula ℕ).gTrace = Set.univ := by simp [Formula.eq_gTrace_trace_of_letterless];
@[simp, grind] lemma Formula.gTrace_top : (⊤ : Formula ℕ).gTrace = ∅ := by simp [Formula.eq_gTrace_trace_of_letterless];

lemma Formula.gTrace_and : (φ ⋏ ψ).gTrace = φ.gTrace ∪ ψ.gTrace := by
  ext n;
  calc
    _ ↔ ∃ M : Kripke.Model, ∃ r : M, ∃ _ : M.IsTree r, ∃ _ : Fintype M, M.finHeight = n ∧ (¬r ⊧ φ ∨ ¬r ⊧ ψ) := by simp [gTrace, -not_and, not_and_or]
    _ ↔
      (∃ M : Kripke.Model, ∃ r : M, ∃ _ : M.IsTree r, ∃ _ : Fintype M, M.finHeight = n ∧ ¬r ⊧ φ) ∨
      (∃ M : Kripke.Model, ∃ r : M, ∃ _ : M.IsTree r, ∃ _ : Fintype M, M.finHeight = n ∧ ¬r ⊧ ψ) := by
      constructor;
      . rintro ⟨M, r, _, _, _, (h | h)⟩;
        . left; tauto;
        . right; tauto;
      . rintro (⟨M, r, _, _, _, _⟩ | ⟨M, r, _, _, _, _⟩) <;>
        . refine ⟨M, r, by assumption, by assumption, by tauto⟩;
    _ ↔ _ := by simp [Formula.gTrace];

lemma Formula.gTrace_lconj₂ {s : List (Formula ℕ)} : (s.conj₂).gTrace = ⋃ φ ∈ s, φ.gTrace := by
  induction s using List.induction_with_singleton with
  | hcons φ s hs ih => simp [List.conj₂_cons_nonempty hs, Formula.gTrace_and, ih];
  | _ => simp [List.conj₂];

lemma Formula.gTrace_fconj {s : Finset (Formula ℕ)} : s.conj.gTrace = ⋃ φ ∈ s, φ.gTrace := by simp [Finset.conj, Formula.gTrace_lconj₂];

lemma subset_gTrace_of_provable_imp_GL (h : Modal.GL ⊢! φ ➝ ψ) : ψ.gTrace ⊆ φ.gTrace := by
  intro n hn;
  obtain ⟨M, r, _, _, rfl, h₁⟩ := iff_mem_gTrace.mp hn;
  apply iff_mem_gTrace.mpr;
  refine ⟨M, r, by assumption, by assumption, by rfl, ?_⟩;
  contrapose! h₁;
  have : M.IsFiniteTree r := {}
  apply GL.Kripke.iff_provable_satisfies_FiniteTransitiveTree.mp h;
  assumption;

abbrev FormulaSet.gTrace (X : FormulaSet ℕ) : Set ℕ := ⋃ φ ∈ X, φ.gTrace

@[simp] lemma FormulaSet.gTrace_empty : (∅ : FormulaSet ℕ).gTrace = ∅ := by simp [FormulaSet.gTrace];

lemma eq_FormulaSet_gTrace_finset_conj {X : Finset (Formula ℕ)} : X.conj.gTrace = FormulaSet.gTrace X.toSet := by simp [FormulaSet.gTrace, Formula.gTrace_fconj];

lemma FormulaSet.subset_gTrace_of_subset {X Y : FormulaSet ℕ} (h : X ⊆ Y) : X.gTrace ⊆ Y.gTrace := by
  simp only [gTrace, Set.iUnion_subset_iff];
  intro φ hφ i hi;
  simp only [Set.mem_iUnion, exists_prop];
  use φ;
  constructor;
  . apply h; assumption;
  . assumption;

abbrev Logic.trace (L : Logic ℕ) : Set ℕ := FormulaSet.gTrace L

lemma GL.eq_trace_ext {X : FormulaSet ℕ} (hX : ∀ ξ ∈ X, ∀ s : Substitution _, ξ⟦s⟧ ∈ X) : (Modal.GL.sumQuasiNormal X).trace = X.gTrace := by
  ext n;
  constructor;
  . suffices (∃ φ, Modal.GL.sumQuasiNormal X ⊢! φ ∧ n ∈ φ.gTrace) → (n ∈ X.gTrace) by simpa [Logic.trace];
    rintro ⟨φ, hφ₁, hφ₂⟩;
    obtain ⟨Y, hY₁, hY₂⟩ := Logic.sumQuasiNormal.iff_provable_finite_provable hX |>.mp hφ₁;
    apply FormulaSet.subset_gTrace_of_subset hY₁;
    apply eq_FormulaSet_gTrace_finset_conj ▸ subset_gTrace_of_provable_imp_GL hY₂;
    assumption;
  . suffices (∃ φ ∈ X, n ∈ φ.gTrace) → (∃ φ, Modal.GL.sumQuasiNormal X ⊢! φ ∧ n ∈ φ.gTrace) by simpa [Logic.trace];
    rintro ⟨φ, hφ₁, hφ₂⟩;
    use φ;
    constructor;
    . apply Logic.sumQuasiNormal.mem₂!;
      simpa [Logic.iff_provable];
    . assumption;

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
lemma TBB_injective : Function.Injective TBB := by
  rintro i j;
  suffices □^[i]⊥ = □^[j]⊥ → i = j by simpa;
  wlog hij : i < j;
  . rcases (show i = j ∨ i > j by omega) with h | h
    . tauto;
    . have := @this j i; grind;
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hij;
  simp [show ((i + k) + 1) = i + (k + 1) by omega, ←(Box.add (n := i) (m := (k + 1)))];

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
  . simpa [Tφ]
  . apply GL.Kripke.tree_completeness_TFAE.out 3 0 |>.mp;
    intro M r _ hr;
    have : Fintype M.World := Fintype.ofFinite _;
    apply satisfies_of_not_mem_gTrace (n := M.finHeight) |>.mp;
    . replace hr : ∀ n ∈ φ.gTrace, M.finHeight ≠ n := by
        intro n h;
        apply iff_satisfies_TBB_ne_finHeight.mp;
        apply Satisfies.fconj_def.mp hr _;
        suffices ∃ m ∈ φ.gTrace, □^[m]⊥ = □^[n]⊥ by simpa [Tφ];
        use n;
      by_contra hC;
      apply hr _ hC rfl;
    . rfl;


namespace Formula.Kripke.Satisfies

variable {M : Kripke.Model} {w : M} {X : Finset α} {ι : α → Formula ℕ}

lemma fconj'_def : w ⊧ (⩕ i ∈ X, ι i) ↔ ∀ i ∈ X, w ⊧ ι i := by
  sorry;

lemma not_fconj'_def : ¬(w ⊧ (⩕ i ∈ X, ι i)) ↔ ∃ i ∈ X, ¬(w ⊧ ι i) := by
  simpa using Formula.Kripke.Satisfies.fconj'_def.not;

lemma fdisj'_def : w ⊧ (⩖ i ∈ X, ι i) ↔ ∃ i ∈ X, w ⊧ ι i := by
  sorry;

lemma not_fdisj'_def : ¬(w ⊧ (⩖ i ∈ X, ι i)) ↔ ∀ i ∈ X, ¬(w ⊧ ι i) := by
  simpa using Formula.Kripke.Satisfies.fdisj'_def.not;

lemma not_and_def {φ ψ : Formula ℕ} : ¬(w ⊧ φ ⋏ ψ) ↔ ¬(w ⊧ φ) ∨ ¬(w ⊧ ψ) := by simp [-not_and, not_and_or];

end Formula.Kripke.Satisfies


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
        replace hm₂ : M.finHeight = m := by simpa using iff_satisfies_TBB_ne_finHeight.not.mp hm₂;
        apply hm₁ ξ;
        . assumption;
        . grind;
      by_contra hC;
      apply hr M.finHeight φ hφ hC rfl;
    . rfl;

protected abbrev GLαOmega := Modal.GLα Set.univ

@[simp]
lemma eq_GLβMinusOmega : Modal.GLβMinus Set.univ = Set.univ := by
  apply Set.eq_univ_iff_forall.mpr;
  intro φ;
  apply Logic.iff_provable.mp;
  apply Logic.sumQuasiNormal.iff_provable_finite_provable_letterless (by grind;) |>.mpr;
  use {∼⊤};
  constructor;
  . simp;
  . suffices Modal.GL ⊢! ∼⊤ ➝ φ by simpa;
    cl_prover;

protected abbrev D_inter_GLβMinus (β : Set ℕ) (hβ : βᶜ.Finite := by grind) := Modal.D ∩ Modal.GLβMinus β
@[simp] lemma eq_D_inter_GLβMinusOmega : Modal.D_inter_GLβMinus Set.univ = Modal.D := by simp

protected abbrev S_inter_GLβMinus (β : Set ℕ) (hβ : βᶜ.Finite := by grind) := Modal.S ∩ Modal.GLβMinus β
@[simp] lemma eq_S_inter_GLβMinusOmega : Modal.S_inter_GLβMinus Set.univ = Modal.S := by simp

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

theorem eq_provablityLogic_GLα_of_coinfinite_trace (h : (T.ProvabilityLogic U).trace.Coinfinite) : T.ProvabilityLogic U = Modal.GLα (T.ProvabilityLogic U).trace := by
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

@[grind]
lemma cofinite_of_not_subset_S (h : ¬(T.ProvabilityLogic U) ⊆ Modal.S) : (T.ProvabilityLogic U).trace.Cofinite := by
  contrapose! h;
  rw [eq_provablityLogic_GLα_of_coinfinite_trace h];
  simp;

@[grind]
lemma _root_.Set.iff_cofinite_not_coinfinite {s : Set α} : s.Cofinite ↔ ¬s.Coinfinite := by
  dsimp [Set.Cofinite, Set.Coinfinite];
  simp;

lemma provable_TBBMinus_of_mem_trace (h : ¬(T.ProvabilityLogic U) ⊆ Modal.S) : T.ProvabilityLogic U ⊢! ∼⩕ i ∈ (cofinite_of_not_subset_S h).toFinset, TBB i := by
  have : 𝗜𝚺₁ ⪯ U := WeakerThan.trans (𝓣 := T) inferInstance inferInstance;

  obtain ⟨A, hA₁, hA₂⟩ := Set.not_subset.mp h;
  replace hA₁ : T.ProvabilityLogic U ⊢! A := by grind;
  replace hA₂ : Modal.GL ⊬ A.rflSubformula.conj ➝ A := Modal.Logic.iff_provable_rflSubformula_GL_provable_S.not.mpr $ by grind;

  obtain ⟨M₁, r₁, _, hM⟩ := Modal.GL.Kripke.iff_unprovable_exists_unsatisfies_FiniteTransitiveTree.mp hA₂;
  have : Fintype M₁ := Fintype.ofFinite _;

  let M₀ := Model.extendRoot M₁ 1;
  let r₀ : M₀.World := Model.extendRoot.root;
  have : Fintype M₀.World := Fintype.ofFinite _

  let R := Set.Finite.inter_of_left (s := (Finset.range M₁.finHeight)) (t := (T.ProvabilityLogic U).trace) (Finset.finite_toSet _) |>.toFinset;

  let B := A ⋏ ⩕ i ∈ R, TBB i;
  have hB : T.ProvabilityLogic U ⊢! B := by
    suffices T.ProvabilityLogic U ⊢! A ∧ ∀ i ∈ R, T.ProvabilityLogic U ⊢! TBB i by
      have ⟨h₁, h₂⟩ := this;
      replace h₂ : T.ProvabilityLogic U ⊢! ⩕ i ∈ R, TBB i := Entailment.FConj'_iff_forall_provable.mpr h₂;
      cl_prover [h₁, h₂];
    constructor;
    . assumption;
    . rintro i hi;
      apply provable_TBB_of_mem_trace;
      simp_all [R, Logic.trace];

  have : M₁.IsFiniteTree r₁ := {};
  let S := SolovaySentences.standard T M₀.toFrame;

  have H₁ : 𝗜𝚺₁ ⊢!. (S.realization B ➝ S.realization (∼⩕ n ∈ (cofinite_of_not_subset_S h).toFinset, TBB n)) := by
    apply ?_ ⨀ S.SC4;
    apply left_Udisj!_intro _;
    rintro (a | i);
    . suffices 𝗜𝚺₁ ⊢!. S r₀ ➝ S.realization B ➝ S.realization (∼⩕ n ∈ (cofinite_of_not_subset_S h).toFinset, TBB n) by
        rwa [(show Sum.inl a = r₀ by simp [r₀])];
      have H₁ : 𝗜𝚺₁ ⊢!. S r₀ ➝ ∼S.realization A := by
        convert SolovaySentences.rfl_mainlemma_neg (T := T) hM A (by grind) ?_;
        exact Satisfies.not_imp_def.mp hM |>.2;
      have H₂ : 𝗜𝚺₁ ⊢!. S.realization B ⭤ S.realization A ⋏ S.realization (⩕ n ∈ R, TBB n) := Realization.interpret.iff_provable_and_inside;
      cl_prover [H₁, H₂];
    . suffices 𝗜𝚺₁ ⊢!. S i ➝ S.realization (B ➝ (∼⩕ n ∈ (cofinite_of_not_subset_S h).toFinset, TBB n)) by simpa;
      apply SolovaySentences.mainlemma (S := S) (T := T) (i := i) ?_ ?_;
      . apply Frame.root_genaretes'!;
        simp;
      . intro h;
        apply Satisfies.not_def.mpr;
        apply Satisfies.not_fconj'_def.mpr;
        use Frame.World.finHeight (i : M₀);
        constructor;
        . by_contra hC;
          apply iff_satisfies_TBB_ne_finHeight (w := (i : M₀)) (n := Frame.World.finHeight (i : M₀)) |>.mp;
          . apply Satisfies.fconj'_def.mp $ Satisfies.and_def.mp h |>.2;
            suffices Frame.World.finHeight (i : M₀) < M₁.finHeight ∧ Frame.World.finHeight (i : M₀) ∈ (T.ProvabilityLogic U).trace by
              simpa [R];
            constructor;
            . suffices Frame.World.finHeight i < M₁.finHeight by calc
                _ = Frame.World.finHeight (i : M₁) := by convert Frame.extendRoot.eq_original_finHeight
                _ < _                              := this;
              apply Frame.World.finHeight_lt_whole_finHeight;
              apply M₁.root_genaretes'!;
              rintro rfl;
              apply Satisfies.not_imp_def.mp hM |>.2;
              apply Model.extendRoot.modal_equivalence_original_world.mpr;
              exact Satisfies.and_def.mp h |>.1;
            . simpa using hC;
          . rfl;
        . apply iff_satisfies_TBB_ne_finHeight.not.mpr;
          simp;

  replace H₁ : U ⊢!. S.realization B ➝ S.realization (∼⩕ n ∈ (cofinite_of_not_subset_S h).toFinset, TBB n) := WeakerThan.pbl H₁;
  have H₂ : U ⊢!. S.realization B := ProvabilityLogic.provable_iff.mp hB (f := S.realization);
  have H : U ⊢!. S.realization (∼⩕ n ∈ (cofinite_of_not_subset_S h).toFinset, TBB n) := by cl_prover [H₁, H₂];

  apply ProvabilityLogic.provable_iff.mpr;
  intro g;

  rwa [Realization.letterless_interpret (f₁ := S.realization) (f₂ := g) (by grind)] at H;

/-- Artemov & Beklemishev. Lemma 49 -/
theorem eq_provabilityLogic_GLβMinus_of_not_subset_S (h : ¬(T.ProvabilityLogic U) ⊆ Modal.S) : T.ProvabilityLogic U = Modal.GLβMinus (T.ProvabilityLogic U).trace := by
  apply Set.Subset.antisymm;
  . apply subset_GLβMinus_of_trace_cofinite;
    grind;
  . intro A;
    suffices Modal.GLβMinus (T.ProvabilityLogic U).trace ⊢! A → T.ProvabilityLogic U ⊢! A by grind;
    intro hA;
    dsimp [Modal.GLβMinus] at hA;
    induction hA using Modal.Logic.sumQuasiNormal.rec!_omitSubst_strong (L₁ := Modal.GL) (L₂ := {∼(⩕ n ∈ (cofinite_of_not_subset_S h).toFinset, (TBB n))}) inferInstance (Logic.substitution_of_letterless (by grind)) with
    | mem₁ hA =>
      apply ProvabilityLogic.provable_iff.mpr;
      intro f;
      exact WeakerThan.pbl $ GL.arithmetical_soundness hA;
    | mem₂ hA =>
      suffices T.ProvabilityLogic U ⊢! ∼(⩕ n ∈ (cofinite_of_not_subset_S h).toFinset, (TBB n)) by
        replace hA := Logic.iff_provable.mp hA;
        subst hA;
        exact this;
      exact provable_TBBMinus_of_mem_trace h;
    | mdp ihAB ihA => exact ProvabilityLogic.mdp ihAB ihA;

end ProvabilityLogic

end LO
