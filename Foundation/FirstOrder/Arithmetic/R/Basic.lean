module

public import Foundation.FirstOrder.LK.Interpretation
public import Foundation.FirstOrder.Arithmetic.R0.Undecidability

/-!
# The theory $\mathsf{R}$ of Tarski, Mostowski and Robinson

$\mathsf{R}$ is mutually interpretable with $\mathsf{R}_0$, and it is essentially undecidable.

## References

- [Hor11]
- [Sve08]
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic

open DirectTranslation ORingStructure

inductive IsRAxiom : ArithmeticSentence → Prop
  | r0 : ∀ φ ∈ 𝗥₀, IsRAxiom φ
  | Ω₅ (n : ℕ) : IsRAxiom “∀ x, x ≤ ↑n ∨ ↑n ≤ x”

abbrev R : ArithmeticTheory := Set.ofPred IsRAxiom

notation "𝗥" => R

namespace R

instance : 𝗥₀ ⪯ 𝗥 := Entailment.WeakerThan.ofSubset IsRAxiom.r0

instance : 𝗘𝗤 ℒₒᵣ ⪯ 𝗥 := Entailment.WeakerThan.trans (𝓣 := 𝗥₀) inferInstance inferInstance

section

variable {M : Type*} [ORingStructure M]

lemma models_iff_models_R0 : M↓[ℒₒᵣ] ⊧* 𝗥 ↔
    M↓[ℒₒᵣ] ⊧* 𝗥₀ ∧ ∀ (n : ℕ) (x : M), x = numeral n ∨ x < numeral n ∨ numeral n < x := by
  have hΩ (n : ℕ) : M↓[ℒₒᵣ] ⊧ (“∀ x, x ≤ ↑n ∨ ↑n ≤ x” : ArithmeticSentence) ↔
      ∀ x : M, x = numeral n ∨ x < numeral n ∨ numeral n < x := by
    simp [models_iff, Semiformula.Operator.LE.sentence_eq, Semiformula.Operator.val,
      Semiformula.Operator.Eq.sentence_eq, Semiformula.Operator.LT.sentence_eq]
    grind
  constructor
  · intro h
    and_intros
    · exact models_of_ss h IsRAxiom.r0
    · exact fun n ↦ (hΩ n).mp <| Theory.models M _ (IsRAxiom.Ω₅ n)
  · rintro ⟨h₀, h⟩
    constructor
    rintro σ (⟨_, hσ⟩ | n)
    · exact models_theory_iff.mp h₀ _ hσ
    · exact (hΩ n).mpr (h n)

instance [M↓[ℒₒᵣ] ⊧* 𝗥] : M↓[ℒₒᵣ] ⊧* 𝗥₀ := (models_iff_models_R0.mp inferInstance).1

end

instance : ℕ↓[ℒₒᵣ] ⊧* 𝗥 := by
  rw [models_iff_models_R0]
  and_intros
  · infer_instance
  · intro n x
    simpa using Nat.lt_trichotomy x n |>.elim (Or.inr ∘ Or.inl) (Or.imp_right Or.inr)

instance : Entailment.Consistent 𝗥 :=
  let : ℕ↓[ℒₒᵣ] ⊧* 𝗥 := inferInstance
  Sound.consistent_of_satisfiable ⟨_, this⟩

instance : 𝗥 ⪯ 𝗣𝗔⁻ := weakerThan_of_models.{0} _ _ fun _ _ _ ↦ models_iff_models_R0.mpr
  ⟨inferInstance, fun n x ↦ (lt_tri x (numeral n)).elim (Or.inr ∘ Or.inl) (Or.imp_right Or.inr)⟩

end R

section

variable {M : Type*} [ORingStructure M]

lemma eq_numeral_or_lt_numeral_or_numeral_lt [M↓[ℒₒᵣ] ⊧* 𝗥] (n : ℕ) (x : M) :
    x = numeral n ∨ x < numeral n ∨ numeral n < x :=
  (R.models_iff_models_R0.mp inferInstance).2 n x

end

namespace R0

def cobhamTranslation : DirectTranslation 𝗥₀ ℒₒᵣ where
  domain := ⟨“x. ⊤”⟩
  rel
    | .eq => ⟨“x y. x = y”⟩
    | .lt => ⟨cobhamLTDef.val⟩
  func f := ⟨“z. z = !!(Semiterm.func f (#·.succ))”⟩
  domain_nonempty := complete.{0} _ _ fun M _ _ ↦ (models_domainNonempty_iff _).mpr <| by
    simp [Semiformula.Operator.val]
  func_defined f := complete.{0} _ _ fun M _ _ ↦ (models_funcDefined_iff _ _).mpr <| by
    intro e _
    simp [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq, Function.comp_def]
  preserve_eq := complete.{0} _ _ fun M _ _ ↦ (models_preserveEq_iff _ _).mpr <| by
    simp [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]

section model

variable {M : Type*} [ORingStructure M]

@[simp]
lemma cobhamTranslation_dom (x : M) : cobhamTranslation.Dom x := by
  simp [dom_iff, cobhamTranslation, Semiformula.Operator.val]

namespace cobhamTranslation

abbrev oRingStructure : ORingStructure (cobhamTranslation.Model M) where
  zero := ⟨0, by simp⟩
  one := ⟨1, by simp⟩
  add x y := ⟨x + y, by simp⟩
  mul x y := ⟨x * y, by simp⟩
  lt x y := CobhamLT (x : M) y

attribute [local instance] oRingStructure in
lemma val_numeral (n : ℕ) : ((numeral n : cobhamTranslation.Model M) : M) = numeral n :=
  match n with
  | 0 => rfl
  | 1 => rfl
  | n + 2 => congrArg (· + (1 : M)) (val_numeral (n + 1))

variable [M↓[ℒₒᵣ] ⊧* 𝗥₀]

lemma struc_eq : Model.struc cobhamTranslation M = @standardModel _ oRingStructure :=
  Tarski.Structure.ext
    (funext₃ fun k f v ↦ by
      symm
      apply Model.func_iff.mpr
      cases f <;> simp [cobhamTranslation, Semiformula.Operator.val,
        Semiformula.Operator.Eq.sentence_eq] <;> rfl)
    (funext₃ fun k r v ↦ by
      cases r
      · exact propext <| Model.eq_iff v
      · change (cobhamTranslation.rel .lt).val (fun i ↦ (v i : M)) = CobhamLT (v 0 : M) (v 1)
        rw [Matrix.fun_eq_vec_two (fun i ↦ (v i : M))]
        simp [cobhamTranslation, Semiformula.Operator.val])

instance : (cobhamTranslation.Model M)↓[ℒₒᵣ] ⊧* 𝗥 := by
  rw [struc_eq]
  let := oRingStructure (M := M)
  have lt_iff (x : cobhamTranslation.Model M) (n : ℕ) :
      x < numeral n ↔ (x : M) < numeral n := by
    change CobhamLT (x : M) (numeral n : cobhamTranslation.Model M) ↔ _
    rw [val_numeral, cobhamLT_numeral_iff]
  rw [R.models_iff_models_R0]
  and_intros
  · constructor
    intro σ hσ
    cases hσ
    case equal hφ => exact models_theory_iff.mp inferInstance _ hφ
    case Ω₁ n m =>
      suffices (numeral n + numeral m : cobhamTranslation.Model M) = numeral (n + m) by
        simpa [models_iff]
      apply Model.ext
      rw [val_numeral, ← numeral_add_numeral]
      exact congrArg₂ (· + ·) (val_numeral n) (val_numeral m)
    case Ω₂ n m =>
      suffices (numeral n * numeral m : cobhamTranslation.Model M) = numeral (n * m) by
        simpa [models_iff]
      apply Model.ext
      rw [val_numeral, ← numeral_mul_numeral]
      exact congrArg₂ (· * ·) (val_numeral n) (val_numeral m)
    case Ω₃ n =>
      suffices ∀ x : cobhamTranslation.Model M, x < numeral n ↔ ∃ i < n, x = numeral i by
        simpa [models_iff]
      intro x
      rw [lt_iff, lt_numeral_iff, Fin.exists_iff]
      simp [← Model.val_inj_iff, val_numeral]
  · intro n x
    by_cases h : (x : M) = numeral n
    · exact Or.inl <| Model.ext <| h.trans (val_numeral n).symm
    · right
      have h' := cobhamLE_numeral_or (x := (x : M)) n
      rw [← val_numeral (M := M)] at h h'
      exact h'.imp (⟨·, h⟩) (⟨·, Ne.symm h⟩)

end cobhamTranslation

end model

end R0

instance : 𝗥₀ ⊳ 𝗥 where
  trln := R0.cobhamTranslation
  interpret_theory φ hφ := complete.{0} _ _ fun _ _ _ ↦
    Model.translate_iff.mpr <| models_theory_iff.mp inferInstance φ hφ

instance : 𝗥 ⊳ 𝗥₀ := DirectInterpretation.ofWeakerThan 𝗥 𝗥₀

instance : 𝗥₀ ⋈ 𝗥 := ⟨inferInstance, inferInstance⟩

instance : Entailment.EssentiallyUndecidable 𝗥 fun _ ↦ True :=
  .of_weakerThan 𝗥₀ 𝗥

end FFL.FirstOrder.Arithmetic
