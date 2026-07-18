module

public import Foundation.FirstOrder.Arithmetic.Basic.Misc

@[expose] public section
namespace LO.FirstOrder.Arithmetic

private lemma complete_aux (T : ArithmeticTheory) [𝗘𝗤 ℒₒᵣ ⪯ T] (φ : ArithmeticSentence)
    (H : ∀ (M : Type w)
           [ORingStructure M]
           [Structure ℒₒᵣ M]
           [Structure.ORing ℒₒᵣ M]
           [M↓[ℒₒᵣ] ⊧* T],
           M↓[ℒₒᵣ] ⊧ φ) :
    T ⊢ φ := Theory.Proof.complete <| consequence_iff_eq.mpr fun M _ _ _ hT ↦
  letI : (Structure.Model ℒₒᵣ M)↓[ℒₒᵣ] ⊧* T := Structure.ElementaryEquiv.modelsTheory.mp hT
  Structure.ElementaryEquiv.models.mpr (H (Structure.Model ℒₒᵣ M))

open Language

section semantics

variable (M : Type*) [ORingStructure M]

instance standardModel : Structure ℒₒᵣ M where
  func := fun _ f ↦
    match f with
    | ORing.Func.zero => fun _ ↦ 0
    |  ORing.Func.one => fun _ ↦ 1
    |  ORing.Func.add => fun v ↦ v 0 + v 1
    |  ORing.Func.mul => fun v ↦ v 0 * v 1
  rel := fun _ r ↦
    match r with
    | ORing.Rel.eq => fun v ↦ v 0 = v 1
    | ORing.Rel.lt => fun v ↦ v 0 < v 1

instance : Structure.Eq ℒₒᵣ M where
  eq a b := by
    unfold standardModel
    simp [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]

instance : Structure.Zero ℒₒᵣ M := ⟨rfl⟩

instance : Structure.One ℒₒᵣ M := ⟨rfl⟩

instance : Structure.Add ℒₒᵣ M := ⟨fun _ _ ↦ rfl⟩

instance : Structure.Mul ℒₒᵣ M := ⟨fun _ _ ↦ rfl⟩

instance : Structure.Eq ℒₒᵣ M := ⟨fun _ _ ↦ iff_of_eq rfl⟩

instance : Structure.LT ℒₒᵣ M := ⟨fun _ _ ↦ iff_of_eq rfl⟩

instance : ORing ℒₒᵣ := ORing.mk

lemma standardModel_unique' (s : Structure ℒₒᵣ M)
    (hZero : Structure.Zero ℒₒᵣ M) (hOne : Structure.One ℒₒᵣ M) (hAdd : Structure.Add ℒₒᵣ M) (hMul : Structure.Mul ℒₒᵣ M)
    (hEq : Structure.Eq ℒₒᵣ M) (hLT : Structure.LT ℒₒᵣ M) : s = standardModel M := Structure.ext
  (funext₃ fun k f _ ↦
    match k, f with
    | _, Language.Zero.zero => by simp [Matrix.empty_eq]
    | _,   Language.One.one => by simp [Matrix.empty_eq]
    | _,   Language.Add.add => by simp
    | _,   Language.Mul.mul => by simp)
  (funext₃ fun k r _ =>
    match k, r with
    | _, Language.Eq.eq => by simp
    | _, Language.LT.lt => by simp)

lemma standardModel_unique (s : Structure ℒₒᵣ M)
    [hZero : Structure.Zero ℒₒᵣ M] [hOne : Structure.One ℒₒᵣ M] [hAdd : Structure.Add ℒₒᵣ M] [hMul : Structure.Mul ℒₒᵣ M]
    [hEq : Structure.Eq ℒₒᵣ M] [hLT : Structure.LT ℒₒᵣ M] : s = standardModel M :=
  standardModel_unique' M s hZero hOne hAdd hMul hEq hLT

end semantics

/-- provable_of_models -/
lemma complete (T : ArithmeticTheory) [𝗘𝗤 ℒₒᵣ ⪯ T] (φ : ArithmeticSentence) (H : ∀ (M : Type*) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T], M↓[ℒₒᵣ] ⊧ φ) :
    T ⊢ φ := complete_aux T φ fun M _ s _ _ ↦ by
  rcases standardModel_unique M s
  exact H M

lemma weakerThan_of_models (T S : ArithmeticTheory) [𝗘𝗤 ℒₒᵣ ⪯ S]
    (H : ∀ (M : Type*)
           [ORingStructure M]
           [M↓[ℒₒᵣ] ⊧* S],
           M↓[ℒₒᵣ] ⊧* T) : T ⪯ S :=
  Entailment.weakerThan_iff.mpr fun h ↦ complete _ _ fun M _ _ ↦ Theory.Proof.sound h (H M)

end Arithmetic

class ArithmeticTheory.SoundOn (T : ArithmeticTheory) (F : ArithmeticSentence → Prop) where
  sound : ∀ {σ}, T ⊢ σ → F σ → ℕ↓[ℒₒᵣ] ⊧ σ

namespace ArithmeticTheory

variable (T : ArithmeticTheory) (F : ArithmeticSentence → Prop)

instance [ℕ↓[ℒₒᵣ] ⊧* T] : T.SoundOn F := ⟨fun b _ ↦ consequence_iff.mp (Theory.Proof.sound b) ℕ inferInstance⟩

lemma consistent_of_sound [SoundOn T F] (hF : F ⊥) : Entailment.Consistent T :=
  Entailment.consistent_iff_unprovable_bot.mpr fun b ↦ SoundOn.sound b hF

end ArithmeticTheory

end LO.FirstOrder
