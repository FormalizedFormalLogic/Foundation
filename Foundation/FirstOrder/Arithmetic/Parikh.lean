module

public import Foundation.FirstOrder.Arithmetic.Model.Basic

/-!
# Parikh's theorem

An `𝗜𝚺₀`-provable $\Pi^0_2$ sentence with a $\Delta_0$ matrix is provable with the existential
quantifier bounded by a term.

## References

- [HP98]
- [Bus98]
-/

@[expose] public section

namespace FFL.FirstOrder

namespace Language

abbrev oringConst (k : ℕ) : Language := Language.add ℒₒᵣ (Language.constant (Fin k))

end Language

namespace Arithmetic

open Semiformula
open _root_.FFL.Entailment
open Semantics (modelsSet_iff)

universe u

variable {k : ℕ}

def cst {ξ n} (i : Fin k) : Semiterm (Language.oringConst k) ξ n :=
  Semiterm.func (arity := 0) (Sum.inr (Language.Constant.Func.const i)) ![]

def lift (φ : ArithmeticSemisentence k) : Sentence (Language.oringConst k) :=
  Rew.subst (fun i ↦ cst i) ▹ Semiformula.lMap (Language.Hom.add₁ ℒₒᵣ (Language.constant (Fin k))) φ

section

variable (M : Type u) [ORingStructure M] (a : Fin k → M)

def strucOfTuple : Tarski.Struc (Language.oringConst k) where
  Dom := M
  nonempty := ⟨0⟩
  struc :=
    letI : Tarski.Structure (Language.constant (Fin k)) M :=
      { func := fun _ c _ ↦ match c with | .const i => a i
        rel := fun _ r _ ↦ r.elim }
    Tarski.Structure.add ℒₒᵣ (Language.constant (Fin k)) M

@[simp] lemma strucOfTuple_models_lift_iff (φ : ArithmeticSemisentence k) :
    strucOfTuple M a ⊧ lift φ ↔ φ.Evalb a := by
  simp only [lift, strucOfTuple, models_iff, Semiformula.Realize, eval_substs,
    Tarski.Structure.eval_lMap_add₁]
  exact Iff.rfl

lemma strucOfTuple_models_eq : strucOfTuple M a ⊧* 𝗘𝗤 (Language.oringConst k) := by
  let s : Tarski.Structure (Language.oringConst k) M := (strucOfTuple M a).struc
  have : Nonempty M := ⟨0⟩
  have : Tarski.Structure.Eq (Language.oringConst k) M := ⟨fun _ _ ↦ iff_of_eq rfl⟩
  change M↓[Language.oringConst k] ⊧* 𝗘𝗤 (Language.oringConst k)
  infer_instance

lemma strucOfTuple_models_lMap_image {U : ArithmeticTheory} (h : M↓[ℒₒᵣ] ⊧* U) :
    strucOfTuple M a ⊧*
      Semiformula.lMap (Language.Hom.add₁ ℒₒᵣ (Language.constant (Fin k))) '' U := by
  apply Semantics.modelsSet_iff.mpr
  rintro _ ⟨σ, hσ, rfl⟩
  simpa [strucOfTuple, models_iff, Semiformula.Realize] using Semantics.modelsSet_iff.mp h hσ

end

section

def dominatingTerm (k : ℕ) : ℕ → ClosedSemiterm ℒₒᵣ k
  | 0 => ‘0’
  | n + 1 => ‘!!(dominatingTerm k n) + !!((Encodable.decode n).getD ‘0’)’

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]

lemma valb_le_valb_dominatingTerm {n : ℕ} {t : ClosedSemiterm ℒₒᵣ k}
  (ht : Encodable.encode t < n) (e : Fin k → M)
  : t.valb e ≤ (dominatingTerm k n).valb e := by
  induction n with
  | zero => simp at ht
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp ht with h | h
    · exact le_trans (ih h) (by simp [dominatingTerm])
    · have : (Encodable.decode n : Option (ClosedSemiterm ℒₒᵣ k)) = some t :=
        h ▸ Encodable.encodek t
      simp [dominatingTerm, this]

end

section

variable {T : Theory (Language.oringConst k)} [𝗘𝗤 (Language.oringConst k) ⪯ T]
  (sat : Semantics.Satisfiable (Tarski.Struc (Language.oringConst k)) T)

noncomputable def cstVal (i : Fin k) : ModelOfSatEq sat := Semiterm.valb ![] (cst i)

lemma reduct_eq :
    (ModelOfSatEq.struc sat).lMap (Language.Hom.add₁ ℒₒᵣ (Language.constant (Fin k))) =
      standardModel (ModelOfSatEq sat) :=
  letI s : Tarski.Structure ℒₒᵣ (ModelOfSatEq sat) :=
    (ModelOfSatEq.struc sat).lMap (Language.Hom.add₁ ℒₒᵣ (Language.constant (Fin k)))
  have : Tarski.Structure.Zero ℒₒᵣ (ModelOfSatEq sat) := ⟨rfl⟩
  have : Tarski.Structure.One ℒₒᵣ (ModelOfSatEq sat) := ⟨rfl⟩
  have : Tarski.Structure.Add ℒₒᵣ (ModelOfSatEq sat) := ⟨fun _ _ ↦ rfl⟩
  have : Tarski.Structure.Mul ℒₒᵣ (ModelOfSatEq sat) := ⟨fun _ _ ↦ rfl⟩
  have : Tarski.Structure.Eq ℒₒᵣ (ModelOfSatEq sat) := ⟨by
    intro _ _;
    simp [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq, Matrix.fun_eq_vec_two]⟩
  have : Tarski.Structure.LT ℒₒᵣ (ModelOfSatEq sat) := ⟨fun _ _ ↦ iff_of_eq rfl⟩
  standardModel_unique _ _

lemma models_lift_iff (φ : ArithmeticSemisentence k) :
    (ModelOfSatEq sat)↓[Language.oringConst k] ⊧ lift φ ↔ φ.Evalb (cstVal sat) := by
  simp only [lift, models_iff, Semiformula.Realize, eval_substs, Semiformula.eval_lMap]
  rw [reduct_eq]
  exact Iff.rfl

lemma models_of_lMap_image_subset {U : ArithmeticTheory}
    (h : Semiformula.lMap (Language.Hom.add₁ ℒₒᵣ (Language.constant (Fin k))) '' U ⊆ T) :
    (ModelOfSatEq sat)↓[ℒₒᵣ] ⊧* U := ⟨fun _ hσ ↦
  reduct_eq sat ▸ Semiformula.models_lMap.mp
    ((ModelOfSatEq.models sat).models _ (h (Set.mem_image_of_mem _ hσ)))⟩

end


lemma exists_countermodel_of_unprovable {T : ArithmeticTheory} [𝗘𝗤 ℒₒᵣ ⪯ T]
    {σ : ArithmeticSentence} (h : T ⊬ σ) :
    ∃ (M : Type) (_ : ORingStructure M) (_ : M↓[ℒₒᵣ] ⊧* T), ¬M↓[ℒₒᵣ] ⊧ σ := by
  by_contra! hc
  exact h (complete T σ fun M _ _ ↦ hc M ‹_› ‹_›)

section termCut

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]

private def termCut (c : Fin k → M) : Cut M where
  carrier := {x | ∃ t : ClosedSemiterm ℒₒᵣ k, x ≤ t.valb c}
  succ_mem := fun ⟨t, ht⟩ ↦ ⟨‘!!t + 1’, by simpa using add_le_add_right ht 1⟩
  mem_of_lt := fun hab ⟨t, ht⟩ ↦ ⟨t, le_trans hab.le ht⟩

private instance termCut_closed (c : Fin k → M) : (termCut c).Closed where
  zero_mem := ⟨‘0’, by simp⟩
  one_mem := ⟨‘1’, by simp⟩
  add_mem := fun ⟨s, hs⟩ ⟨t, ht⟩ ↦ ⟨‘!!s + !!t’, by
    simpa using add_le_add hs ht
  ⟩
  mul_mem := fun ⟨s, hs⟩ ⟨t, ht⟩ ↦ ⟨‘!!s * !!t’, by
    simpa using mul_le_mul hs ht (by simp) (by simp)
  ⟩

end termCut

theorem parikh (φ : ArithmeticSemisentence (k + 1)) (hφ : ℬ[<, ℒₒᵣ].Closure φ)
  (h : 𝗜𝚺₀ ⊢ ∀¹* ∃¹ φ) :
  ∃ t : ClosedSemiterm ℒₒᵣ k, 𝗜𝚺₀ ⊢ ∀¹* ∃¹[“#0 < !!(Rew.bShift t)”] φ := by
  by_contra! hcon
  set Tn : ℕ → Theory (Language.oringConst k) := fun n ↦
    𝗘𝗤 _
    ∪ Semiformula.lMap (Language.Hom.add₁ ℒₒᵣ _) '' 𝗜𝚺₀
    ∪ (fun t : ClosedSemiterm ℒₒᵣ k ↦ lift ((∼φ).ballLT t)) '' {t | Encodable.encode t < n}
  have : Cumulative Tn := by
    intro;
    apply Set.union_subset_union_right _;
    apply Set.image_mono;
    intro _ ht;
    exact Nat.lt_succ_of_lt ht;
  set T := ⋃ n, Tn n;
  have sat : Satisfiable T := (Compact.compact_cumulative ‹_›).mpr <| by
    intro n;
    obtain ⟨M, _, _, hM⟩ := exists_countermodel_of_unprovable <| hcon <| dominatingTerm k n;
    obtain ⟨a, ha⟩ : ∃ a : Fin k → M, ∀ y < (dominatingTerm k n).valb a, ¬φ.Evalb (y :> a) := by
      simpa [models_iff, eval_allClosure, eval_bexsLT] using hM
    use strucOfTuple M a;
    apply modelsSet_iff.mpr;
    rintro σ ((hσ | hσ) | ⟨t, ht, rfl⟩)
    · exact modelsSet_iff.mp (strucOfTuple_models_eq M a) hσ
    · exact modelsSet_iff.mp (strucOfTuple_models_lMap_image M a inferInstance) hσ
    · rw [strucOfTuple_models_lift_iff]
      simp only [eval_ballLT, LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq]
      intro y hy;
      exact ha y (lt_of_lt_of_le hy (valb_le_valb_dominatingTerm ht a))
  have : 𝗘𝗤 (Language.oringConst k) ⪯ T := WeakerThan.ofSubset
    <| Set.subset_iUnion_of_subset 0
    <| Set.subset_union_of_subset_left Set.subset_union_left _
  have hM : (ModelOfSatEq sat)↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := models_of_lMap_image_subset sat
    <| Set.subset_iUnion_of_subset 0
    <| Set.subset_union_of_subset_left Set.subset_union_right _
  have hunbounded : ∀ (t : ClosedSemiterm ℒₒᵣ k) (y), y < t.valb (cstVal sat) →
      ¬φ.Evalb (y :> cstVal sat) := by
    intro t;
    simpa [models_lift_iff, eval_ballLT] using modelsSet_iff.mp (ModelOfSatEq.models sat)
      <| Set.mem_iUnion_of_mem (Encodable.encode t + 1)
      <| Set.mem_union_right _ ⟨t, Nat.lt_succ_self _, rfl⟩
  set K : Cut (ModelOfSatEq sat) := termCut (cstVal sat);
  let _ : K.Closed := termCut_closed _
  let _ : ↥K.carrier ⊆ₑ ModelOfSatEq sat := K.endExtension
  have hK : (↥K.carrier)↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ :=
    EndExtension.models_ISigma0 (M := ↥K.carrier) (N := ModelOfSatEq sat)
  have hwit : ∀ w : Fin k → ↥K.carrier, ∃ b, φ.Evalb (b :> w) := by
    simpa [models_iff, eval_allClosure] using models_of_provable hK h
  obtain ⟨b, hb⟩ := hwit fun i ↦ ⟨cstVal sat i, Semiterm.bvar i, by simp⟩
  obtain ⟨t, ht⟩ : ∃ t : ClosedSemiterm ℒₒᵣ k, (b : ModelOfSatEq sat) ≤ t.valb (cstVal sat) := b.2
  have hbM : φ.Evalb ((b : ModelOfSatEq sat) :> cstVal sat) := by
    have h₂ :=
      (Bounding.bounded_absolute (ι := K.endExtension.emb) hφ _ Empty.elim).mp hb
    simp only [Matrix.comp_vecCons'', Empty.eq_elim] at h₂
    exact h₂
  exact hunbounded ‘!!t + 1’ b (by simpa using lt_succ_iff_le.mpr ht) hbM

end Arithmetic

end FFL.FirstOrder
