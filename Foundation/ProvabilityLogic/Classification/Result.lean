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
    induction hA using Modal.Logic.sumQuasiNormal.rec!_omitSubst_strong (L₁ := L) (L₂ := X.image Modal.TBB) inferInstance inferInstance with
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
open Modal.Kripke
open Formula.Kripke

variable {T U : ArithmeticTheory} [Theory.Δ₁ T] [𝗜𝚺₁ ⪯ T] [𝗜𝚺₁ ⪯ U] [T ⪯ U]
variable {L : Modal.Logic ℕ}

@[grind .] lemma GLαω_ssubset_D : Modal.GLαω ⊂ Modal.D := by sorry;
@[grind .] lemma D_ssubset_S : Modal.D ⊂ Modal.S := by sorry;

/--
  Corollary 50 (half) in [A.B05]
-/
theorem subset_GLαω_of_eq_trace_univ (L) (hPL : L.IsProvabilityLogic T U) (hT : L.trace = Set.univ) : Modal.GLαω ⊆ L := by
  have := Modal.Logic.inst_Cl_of_isProvabilityLogic hPL;
  intro A;
  suffices Modal.GLαω ⊢ A → L ⊢ A by grind only [Logic.iff_unprovable];
  intro hA;
  induction hA using Modal.Logic.sumQuasiNormal.rec!_omitSubst_strong
    (show Modal.GL.Substitution by infer_instance)
    (show Logic.Substitution (TBB '' Set.univ) by apply Modal.Logic.substitution_of_letterless Modal.TBBSet_letterless;)
    with
  | mem₁ hA =>
    apply Logic.provable_GL_of_isProvabilityLogic hPL hA;
  | mem₂ hA =>
    obtain ⟨n, hn, rfl⟩ := by simpa using hA;
    apply provable_TBB_of_mem_trace hPL;
    simp [hT, Set.mem_univ]
  | mdp ihAB ihA =>
    exact ihAB ⨀ ihA;

/--
  Corollary 55 in [A.B05]
-/
theorem no_logic_between_GLαω_D
  (L : Modal.Logic ℕ) (hPL : L.IsProvabilityLogic T U) (hT : L.trace = Set.univ)
  : ¬((Modal.GLαω ⊂ L) ∧ (L ⊂ Modal.D)) := by sorry;

/--
  Corollary 58 in [A.B05]
-/
theorem no_logic_between_D_S
  (L : Modal.Logic ℕ) (hPL : L.IsProvabilityLogic T U) (hT : L.trace = Set.univ)
  : ¬((Modal.D ⊂ L) ∧ (L ⊂ Modal.S)) := by sorry;

lemma beklemishev_lemma
  (L : Modal.Logic ℕ) (hPL : L.IsProvabilityLogic T U) (hT : L.trace = Set.univ) (hS : L ⊆ Modal.S)
  : L = Modal.GLαω ∨ L = Modal.D ∨ L = Modal.S := by
  wlog hS : L ⊂ Modal.S; . grind;
  have hGLαω_sub := subset_GLαω_of_eq_trace_univ L hPL hT;
  /-
  have H₂ := no_logic_between_GLαω_D L hPL hT;
  push_neg at H₂;
  have H₃ := no_logic_between_D_S L hPL hT;
  push_neg at H₃;
  -/
  rcases show (L = Modal.GLαω ∨ Modal.GLαω ⊂ L) by grind with (_ | h); . grind;
  rcases show (L = Modal.S ∨ L ⊂ Modal.S) by grind with (_ | h); . grind;
  right; right;

  have H₁ : ¬L ⊂ Modal.D := by grind [no_logic_between_GLαω_D L hPL hT];
  have H₂ : ¬Modal.D ⊂ L  := by grind [no_logic_between_D_S L hPL hT];

  have H₁ := Set.ssubset_iff_subset_ne.not.mp H₁;
  push_neg at H₁;

  have H₂ := Set.ssubset_iff_subset_ne.not.mp H₂;
  push_neg at H₂;

  sorry;

/--
  Suppose `L.trace` is cofinite and `L ⊆ S`.
  Then, `L` is provability logic if and only if `L = (L.αPL L.traceᶜ) ∩ (GLβMinus L.trace)`.
-/
theorem iff_isProvabilityLogic_eq_inter_αPL_GLβMinus_of_cofinite_trace_of_subset_S
  (L : Modal.Logic ℕ) (hCf : L.trace.Cofinite) (hS : L ⊆ Modal.S) :
  L.IsProvabilityLogic T U ↔ L = (L.αPL L.traceᶜ) ∩ (Modal.GLβMinus L.trace) := by
  constructor;
  . rintro h;
    sorry;
  . rintro h;
    sorry;

lemma artemov_isProvabilityLogic [L.Substitution] (hPL : L.IsProvabilityLogic T U) : (L.αPL L.traceᶜ).IsProvabilityLogic T (U + (L.traceᶜ.image (T.LetterlessStandardRealization $ Modal.TBB ·))) := by
  apply Modal.Logic.αPL_isProvabilityLogic hPL;

lemma artemov_subset_S (hS : L ⊆ Modal.S) : L.αPL L.traceᶜ ⊆ Modal.S := by
  apply Modal.Logic.αPL_subset_S hS;

lemma artemov_trace_univ (hS : L ⊆ Modal.S) : (L.αPL L.traceᶜ).trace = Set.univ := by
  simp [Set.eq_univ_iff_forall, Modal.Logic.αPL];
  intro n;
  use (TBB n);
  constructor;
  . sorry;
  . sorry;

lemma artemov_inbetween_GLαω_S [L.Substitution] (hPL : L.IsProvabilityLogic T U) (hS : L ⊆ Modal.S) : Modal.GLαω ⊆ (L.αPL L.traceᶜ) := by
  have : 𝗜𝚺₁ ⪯ U + (L.traceᶜ.image (T.LetterlessStandardRealization $ Modal.TBB ·)) := by trans U <;> infer_instance;
  have : T ⪯ U + (L.traceᶜ.image (T.LetterlessStandardRealization $ Modal.TBB ·)) := by trans U <;> infer_instance;
  apply subset_GLαω_of_eq_trace_univ (L := (L.αPL L.traceᶜ)) (artemov_isProvabilityLogic hPL) (artemov_trace_univ hS);

lemma classification_lemma
  [L.Substitution] (hPL : L.IsProvabilityLogic T U) (hCf : L.trace.Cofinite) (hS : L ⊆ Modal.S) :
  L = Modal.GLαω ∩ (Modal.GLβMinus L.trace) ∨
  L = Modal.D ∩ (Modal.GLβMinus L.trace) ∨
  L = Modal.S ∩ (Modal.GLβMinus L.trace)
  := by
  have : 𝗜𝚺₁ ⪯ U + (L.traceᶜ.image (T.LetterlessStandardRealization $ Modal.TBB ·)) := by trans U <;> infer_instance;
  have : T ⪯ U + (L.traceᶜ.image (T.LetterlessStandardRealization $ Modal.TBB ·)) := by trans U <;> infer_instance;
  rcases beklemishev_lemma (L := (L.αPL L.traceᶜ)) (artemov_isProvabilityLogic hPL) (artemov_trace_univ hS) (artemov_subset_S hS) with (_ | _ | _) <;>
  . grind [iff_isProvabilityLogic_eq_inter_αPL_GLβMinus_of_cofinite_trace_of_subset_S L hCf hS |>.mp hPL];

open Classical in
theorem classification_provability_logic
  (L : Modal.Logic ℕ) [L.Substitution] (hPL : L.IsProvabilityLogic T U) :
  if h_coinfinite : L.trace.Coinfinite then
    L = Modal.GLα L.trace
  else
    haveI h_cofinite : L.trace.Cofinite := Set.iff_cofinite_not_coinfinite.mpr h_coinfinite;
    if ¬(L ⊆ Modal.S) then
      L = Modal.GLβMinus L.trace
    else
      L = Modal.GLαω                   ∨
      L = Modal.D ∩ Modal.GLβMinus L.trace ∨
      L = Modal.S ∩ Modal.GLβMinus L.trace
  := by
  split_ifs with h_coinfinite h_S;
  . exact eq_provablityLogic_GLα_of_coinfinite_trace hPL h_coinfinite;
  . rcases classification_lemma hPL (Set.iff_cofinite_not_coinfinite.mpr h_coinfinite) h_S with (_ | _ | _);
    . left;
      sorry;
    . grind;
    . grind;
  . exact eq_provabilityLogic_GLβMinus_of_not_subset_S hPL h_S;

end ProvabilityLogic

end LO
