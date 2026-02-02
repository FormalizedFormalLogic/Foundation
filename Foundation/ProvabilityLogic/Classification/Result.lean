module

public import Foundation.ProvabilityLogic.Classification.Trace

@[expose] public section

namespace LO

open FirstOrder
open ArithmeticTheory


namespace Modal

namespace Logic

variable {T U : ArithmeticTheory} [T.Δ₁] {L : Modal.Logic ℕ}

section

/-- α-type provability logic extension -/
def αPL (L : Modal.Logic ℕ) (X : Set ℕ) := L.sumQuasiNormal (X.image Modal.TBB)

variable {X : Set ℕ}

@[simp, grind =]
lemma eq_GLαω_GLαPL : Modal.GLαω = Modal.GL.αPL Set.univ := by
  simp [Modal.GLαω, Modal.GLα, αPL];

instance : Logic.Substitution (X.image Modal.TBB) := by
  constructor;
  simp only [iff_provable, Set.mem_image, forall_exists_index, and_imp];
  rintro A s a h rfl;
  use a;
  grind;

variable (hPL : L.IsProvabilityLogic T U) (hCf : L.trace.Cofinite)

lemma αPL_isProvabilityLogic [L.Substitution] (hPL : L.IsProvabilityLogic T U) :
  (L.αPL X).IsProvabilityLogic T (U + (X.image (T.LetterlessStandardRealization $ Modal.TBB ·))) := by
  intro A;
  constructor;
  . intro hA f;
    induction hA using Modal.Logic.sumQuasiNormal.rec_letterless_expansion (L₁ := L) (X := X.image Modal.TBB) (by grind) with
    | mem₁ hA => apply Entailment.WeakerThan.pbl $ hPL _ |>.mp hA f;
    | mem₂ hA =>
      obtain ⟨n, hn, rfl⟩ := by simpa using hA;
      sorry;
    | mdp ih₁ ih₂ => exact ih₁ ⨀ ih₂;
  . intro h;
    sorry;

lemma αPL_subset_S (hS : L ⊆ Modal.S) : L.αPL X ⊆ Modal.S := by
  intro A;
  suffices (L.αPL X) ⊢ A → Modal.S ⊢ A by grind;
  intro hA;
  induction hA using Modal.Logic.sumQuasiNormal.rec! with
  | mem₁ hA => grind;
  | mem₂ hA =>
    obtain ⟨_, _, rfl⟩ := by simpa using hA;
    simp only [S.provable_TBB]
  | mdp ih₁ ih₂ => exact ih₁ ⨀ ih₂;
  | subst ih => apply Logic.subst; assumption;

end

end Logic


end Modal


namespace ProvabilityLogic

open LO.Entailment Entailment.FiniteContext
open FirstOrder FirstOrder.ProvabilityAbstraction
open Arithmetic
open ArithmeticTheory
open Modal
open Modal.Logic
open Modal.Kripke
open Formula.Kripke

variable {T U : ArithmeticTheory} [Theory.Δ₁ T] [𝗜𝚺₁ ⪯ T] [𝗜𝚺₁ ⪯ U] [T ⪯ U]
variable {L : Modal.Logic ℕ}

/--
  Corollary 50 (half) in [A.B05]
-/
theorem subset_GLαω_of_omega_trace (L) (hPL : L.IsProvabilityLogic T U) (hT : L.trace = Set.univ) : Modal.GLαω ⊆ L := by
  have := Modal.Logic.inst_Cl_of_isProvabilityLogic hPL;
  intro A;
  suffices Modal.GLαω ⊢ A → L ⊢ A by grind only [Logic.iff_unprovable];
  intro hA;
  induction hA using Modal.Logic.sumQuasiNormal.rec_letterless_expansion (L₁ := Modal.GL) (X := TBB '' Set.univ) (by grind) with
  | mem₁ hA =>
    apply Logic.provable_GL_of_isProvabilityLogic hPL hA;
  | mem₂ hA =>
    obtain ⟨n, hn, rfl⟩ := by simpa using hA;
    apply provable_TBB_of_mem_trace hPL;
    simp [hT, Set.mem_univ]
  | mdp ihAB ihA =>
    exact ihAB ⨀ ihA;

section no_logic_between_GLαβ_D

/--
  - Corollary 52(2) in [A.B05]
-/
theorem subset_D_of_subset_GLαβ_of_omega_trace
  (L : Modal.Logic ℕ) (hPL : L.IsProvabilityLogic T U) (hT : L.trace = Set.univ)
  : Modal.GLαω ⊂ L → Modal.D ⊆ L := by
  have := Modal.Logic.inst_Cl_of_isProvabilityLogic hPL;
  have : L.Substitution := by sorry;

  intro h;
  obtain ⟨A, hAL, hAGL⟩ := Set.exists_of_ssubset h;
  trans Modal.GLαω.sumQuasiNormal {A};
  . sorry; -- Hard part
  . apply Modal.Logic.sumQuasiNormal.covered <;> grind;

/--
  - Corollary 55 in [A.B05]
-/
lemma no_logic_between_GLαω_D
  (L : Modal.Logic ℕ) (hPL : L.IsProvabilityLogic T U) (hT : L.trace = Set.univ)
  : ¬((Modal.GLαω ⊂ L) ∧ (L ⊂ Modal.D)) := by
  grind [subset_D_of_subset_GLαβ_of_omega_trace L hPL hT];

end no_logic_between_GLαβ_D


section no_logic_between_D_S

/--
  - Assertion 1 in [Bek90]
-/
theorem eq_S_of_not_subset_D_of_omega_trace (L : Modal.Logic ℕ) (hPL : L.IsProvabilityLogic T U) (hT : L.trace = Set.univ)
  : Modal.D ⊂ L → Modal.S ⊆ L := by
  have := Modal.Logic.inst_Cl_of_isProvabilityLogic hPL;
  have : L.Substitution := by sorry;

  intro h;
  obtain ⟨A, hAL, hAGL⟩ := Set.exists_of_ssubset h;
  trans Modal.D.sumQuasiNormal {A};
  . apply Modal.Logic.sumQuasiNormal.covered;
    . intro B hB;
      apply Logic.sumQuasiNormal.mem₁;
      rw [Logic.iff_provable];
      apply Logic.sumQuasiNormal.mem₁;
      rwa [Logic.iff_provable];
    . simp [←Logic.iff_provable]; -- Hard part
      sorry
  . apply Modal.Logic.sumQuasiNormal.covered <;> grind;

/--
  - Corollary 58 in [A.B05]
-/
lemma no_logic_between_D_S (L : Modal.Logic ℕ) (hPL : L.IsProvabilityLogic T U) (hT : L.trace = Set.univ)
  : ¬(Modal.D ⊂ L ∧ L ⊂ Modal.S) := by
  grind [eq_S_of_not_subset_D_of_omega_trace L hPL hT];

end no_logic_between_D_S

/--
  If `L.trace` is omega then `L` is one of `GLαω`, `D`, and `S`.
  - Assertion 3 in [Bek90]
-/
lemma classification_S_sublogics_of_omega_trace
  (L : Modal.Logic ℕ) (hPL : L.IsProvabilityLogic T U) (hT : L.trace = Set.univ) (L_subset_S : L ⊆ Modal.S)
  : L = Modal.GLαω ∨ L = Modal.D ∨ L = Modal.S
  := by
  wlog GLαω_ssubset_L : Modal.GLαω ⊂ L; . grind [subset_GLαω_of_omega_trace];

  have : Modal.D ⊆ L := by sorry; -- Hard part: Assertion 2 in [Bek90] using `GLαω_ssubset_L`
  rcases Set.eq_or_ssubset_of_subset this with rfl | D_ssubset_L;
  case inl => grind;

  right; right;
  apply Set.Subset.antisymm;
  . assumption;
  . apply eq_S_of_not_subset_D_of_omega_trace L hPL hT D_ssubset_L;

/--
  Suppose `L.trace` is cofinite and `L ⊆ S`.
  Then `L` is provability logic iff `L = (L.αPL L.traceᶜ) ∩ (GLβMinus L.trace)`.
-/
theorem iff_isProvabilityLogic_eq_inter_αPL_GLβMinus_of_cofinite_trace_of_subset_S
  (L : Modal.Logic ℕ) (hCf : L.trace.Cofinite) (hS : L ⊆ Modal.S)
  -- TODO: `U` is not correct in `L.IsProvabilityLogic T U`, might be `U + (...)`
  : L.IsProvabilityLogic T U ↔ L = (L.αPL L.traceᶜ) ∩ (Modal.GLβMinus L.trace) := by
  have : 𝗜𝚺₁ ⪯ U := by sorry;
  have : T ⪯ U := by sorry;

  constructor;
  . intro hPL;
    have := Modal.Logic.inst_Cl_of_isProvabilityLogic hPL;
    have : L.Substitution := by sorry;

    apply Set.Subset.antisymm;
    . intro A hA;
      constructor;
      . exact Logic.sumQuasiNormal.mem₁ $ Logic.iff_provable.mpr hA;
      . exact subset_GLβMinus_of_trace_cofinite hCf hA;
    . rintro A ⟨h₁, h₂⟩;
      simp only [Logic.αPL, ←Logic.iff_provable] at h₁ h₂ ⊢;
      obtain ⟨Γ, hΓ, h₁⟩ := sumQuasiNormal.iff_provable_finite_provable_letterless TBBSet_letterless |>.mp h₁;
      obtain ⟨Δ, hΔ, h₂⟩ := sumQuasiNormal.iff_provable_finite_provable_letterless TBBMinus_letterless |>.mp h₂;
      apply of_C!_of_C!_of_A! (φ := (⩕ n ∈ hCf.toFinset, TBB n)) ?_ ?_ lem!;
      . show L ⊢ (⩕ n ∈ hCf.toFinset, TBB n) ➝ A;
        apply Entailment.C!_trans ?_ h₁;
        suffices L ⊢ Finset.conj ((Set.Finite.toFinset hCf).image TBB) ➝ Γ.conj by sorry;
        apply CFConj_FConj!_of_subset;
        intro γ hγ;
        obtain ⟨n, hn, rfl⟩ := hΓ hγ;
        simp only [
          Set.compl_iUnion, Set.mem_iInter, Set.mem_compl_iff, Finset.mem_image,
          Set.Finite.mem_toFinset
        ] at hn ⊢;
        use n;
      . show L ⊢ (∼⩕ n ∈ hCf.toFinset, TBB n) ➝ A;
        rw [(show (∼⩕ n ∈ hCf.toFinset, TBB n) = Finset.conj {∼⩕ n ∈ hCf.toFinset, TBB n} by simp)];
        apply Entailment.C!_trans (CFConj_FConj!_of_subset ?_) $ Modal.Logic.provable_GL_of_isProvabilityLogic hPL h₂;
        intro δ hδ;
        grind [hΔ hδ];
  . rintro h;
    rw [h];
    sorry;

lemma eq_GLαω_inter_GLβMinus_GLα (hβ : L.trace.Cofinite) : Modal.GLα L.trace = Modal.GLαω ∩ (Modal.GLβMinus L.trace) := by
  let L₁ := (Modal.GLα L.trace).αPL (Modal.GLα L.trace).traceᶜ;
  let L₂ := Modal.GLβMinus (Modal.GLα L.trace).trace (by simpa);
  trans (L₁ ∩ L₂);
  . apply iff_isProvabilityLogic_eq_inter_αPL_GLβMinus_of_cofinite_trace_of_subset_S (T := 𝗜𝚺₁) (U := 𝗜𝚺₁) (L := Modal.GLα L.trace) ?_ ?_ |>.mp;
    . -- letterless_provabilityLogic
      sorry;
    . simpa only [GLα.eq_trace];
    . simp;
  . have : L₁ = Modal.GLαω := by
      subst L₁;
      rw [
        GLα.eq_trace,
        Logic.αPL,
        Logic.sumQuasiNormal.sum_sum_eq_sum_union,
        Modal.GLαω,
        Modal.GLα,
      ];
      simp [-Set.compl_iUnion, Set.image_univ];
    have : L₂ = Modal.GLβMinus L.trace := by grind [GLα.eq_trace (α := L.trace)];
    grind only;

lemma aPL_compl_trace_isProvabilityLogic [L.Substitution] (hPL : L.IsProvabilityLogic T U)
  : (L.αPL L.traceᶜ).IsProvabilityLogic T (U + (L.traceᶜ.image (T.LetterlessStandardRealization $ Modal.TBB ·))) := by
  apply Modal.Logic.αPL_isProvabilityLogic hPL;

lemma aPL_compl_trace_subset_S (hS : L ⊆ Modal.S) : L.αPL L.traceᶜ ⊆ Modal.S := by
  apply Modal.Logic.αPL_subset_S hS;

lemma aPL_compl_trace_omega_trace (hS : L ⊆ Modal.S)
  : (L.αPL L.traceᶜ).trace = Set.univ := by
  simp [Set.eq_univ_iff_forall, Modal.Logic.αPL];
  intro n;
  use (TBB n);
  constructor;
  . sorry;
  . sorry;

lemma classification_S_sublogics_of_cofinite_trace
  [L.Substitution] (hPL : L.IsProvabilityLogic T U) (hCf : L.trace.Cofinite) (hS : L ⊆ Modal.S)
  : L = Modal.GLα L.trace ∨ L = Modal.D ∩ (Modal.GLβMinus L.trace) ∨ L = Modal.S ∩ (Modal.GLβMinus L.trace)
  := by
  have : 𝗜𝚺₁ ⪯ U + (L.traceᶜ.image (T.LetterlessStandardRealization $ Modal.TBB ·)) := by trans U <;> infer_instance;
  have : T ⪯ U + (L.traceᶜ.image (T.LetterlessStandardRealization $ Modal.TBB ·)) := by trans U <;> infer_instance;
  rcases classification_S_sublogics_of_omega_trace (L := (L.αPL L.traceᶜ))
    (aPL_compl_trace_isProvabilityLogic hPL) (aPL_compl_trace_omega_trace hS) (aPL_compl_trace_subset_S hS)
    with _ | _ | _;
  case inl => grind [iff_isProvabilityLogic_eq_inter_αPL_GLβMinus_of_cofinite_trace_of_subset_S, eq_GLαω_inter_GLβMinus_GLα hCf];
  all_goals. grind [iff_isProvabilityLogic_eq_inter_αPL_GLβMinus_of_cofinite_trace_of_subset_S];

open Classical in
/--
  The classification theorem of provability logics.
  - Assertion 6 in [Bek90]
  - Theorem 40 in [A.B05]
-/
theorem classification_provability_logics
  (L : Modal.Logic ℕ) [L.Substitution] (hPL : L.IsProvabilityLogic T U) :
  if h_coinfinite : L.trace.Coinfinite then
    L = Modal.GLα L.trace
  else
    haveI h_cofinite : L.trace.Cofinite := Set.iff_cofinite_not_coinfinite.mpr h_coinfinite;
    if ¬(L ⊆ Modal.S) then
      L = Modal.GLβMinus L.trace
    else
      L = Modal.GLα L.trace                ∨
      L = Modal.D ∩ Modal.GLβMinus L.trace ∨
      L = Modal.S ∩ Modal.GLβMinus L.trace
  := by
  split_ifs with h_coinfinite h_S;
  . exact eq_provablityLogic_GLα_of_coinfinite_trace hPL h_coinfinite;
  . exact classification_S_sublogics_of_cofinite_trace hPL (Set.iff_cofinite_not_coinfinite.mpr h_coinfinite) h_S;
  . exact eq_provabilityLogic_GLβMinus_of_not_subset_S hPL h_S;

end ProvabilityLogic

end LO
