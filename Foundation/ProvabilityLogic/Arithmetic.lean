module

public import Foundation.ProvabilityLogic.GL.Soundness
/-!
# Provability logic of arithmetic theory
-/


@[expose] public section

namespace LO

open FirstOrder

namespace Modal

namespace Logic

/-- `L` is provability logic of `T` relative to metatheory `U` -/
def IsProvabilityLogic (L : Modal.Logic ℕ) (T U : ArithmeticTheory) [T.Δ₁] := ∀ A, L ⊢ A ↔ ∀ f : T.StandardRealization, U ⊢ f A

variable {T U : ArithmeticTheory} [T.Δ₁] {L : Modal.Logic ℕ}

/-- `L` is Łukasiewicz if `L` is provability logic. -/
def inst_Łukasiewiicz_of_isProvabilityLogic (hPL : L.IsProvabilityLogic T U) : Entailment.Łukasiewicz L where
  mdp := by
    rintro A B ⟨hA⟩ ⟨hB⟩;
    constructor;
    simp only [←Modal.Logic.iff_provable, hPL A, hPL B, hPL (A ➝ B)] at hA hB ⊢;
    intro f;
    replace hA : U ⊢ f A ➝ f B := hA f;
    replace hB : U ⊢ f A := hB f;
    cl_prover [hA, hB];
  implyK {_ _} := by
    constructor;
    apply Modal.Logic.iff_provable.mp;
    apply hPL _ |>.mpr;
    simp;
  implyS {_ _ _} := by
    constructor;
    apply Modal.Logic.iff_provable.mp;
    apply hPL _ |>.mpr;
    simp;
  elimContra {_ _} := by
    constructor;
    apply Modal.Logic.iff_provable.mp;
    apply hPL _ |>.mpr;
    intro f;
    dsimp [ProvabilityLogic.Realization.interpret];
    cl_prover;

def inst_Cl_of_isProvabilityLogic (hPL : L.IsProvabilityLogic T U) : Entailment.Cl L := by
  have := inst_Łukasiewiicz_of_isProvabilityLogic hPL;
  infer_instance;

lemma subset_GL_of_isProvabilityLogic [𝗜𝚺₁ ⪯ T] [𝗜𝚺₁ ⪯ U] [T ⪯ U] (hPL : L.IsProvabilityLogic T U) : Modal.GL ⊆ L := by
  intro A hA;
  simp only [←Modal.Logic.iff_provable] at ⊢ hA;
  apply hPL A |>.mpr;
  intro f;
  apply Entailment.WeakerThan.pbl (𝓢 := T);
  apply ProvabilityLogic.GL.arithmetical_soundness (𝔅 := T.standardProvability) hA;

lemma provable_GL_of_isProvabilityLogic [𝗜𝚺₁ ⪯ T] [𝗜𝚺₁ ⪯ U] [T ⪯ U] (hPL : L.IsProvabilityLogic T U) : Modal.GL ⊢ A → L ⊢ A := by
  simp only [Modal.Logic.iff_provable];
  apply subset_GL_of_isProvabilityLogic hPL;

end Logic

end Modal


namespace FirstOrder

namespace ArithmeticTheory

variable {T U : ArithmeticTheory} [T.Δ₁] {A : Modal.Formula ℕ}

/-- Provability Logic of `T` relative to metatheory `U` -/
def provabilityLogicOn (T U : ArithmeticTheory) [T.Δ₁] : Modal.Logic ℕ := {A | ∀ f : T.StandardRealization, U ⊢ f A}

@[simp, grind .]
lemma isProvabilityLogic_provabilityLogicOn : (T.provabilityLogicOn U).IsProvabilityLogic T U := by
  simp [Modal.Logic.IsProvabilityLogic, provabilityLogicOn];
  grind;

@[grind =]
lemma provabilityLogicOn.provable_iff : (T.provabilityLogicOn U) ⊢ A ↔ ∀ f : T.StandardRealization, U ⊢ f A := by
  simp [Modal.Logic.iff_provable, provabilityLogicOn]

instance : Entailment.Cl (T.provabilityLogicOn U) := Modal.Logic.inst_Cl_of_isProvabilityLogic isProvabilityLogic_provabilityLogicOn

end ArithmeticTheory

end FirstOrder

end LO

end
