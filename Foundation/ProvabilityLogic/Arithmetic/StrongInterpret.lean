module

public import Foundation.ProvabilityLogic.Arithmetic.Interpret

/-!
# Strong interpretations

## References

- [Gol78]
- [Boo80]
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open Entailment FirstOrder FirstOrder.ProvabilityAbstraction

variable {α : Type*} {L : Language} [L.ReferenceableBy L] [L.DecidableEq]
         {T₀ T : Theory L} [T₀ ⪯ T] {𝔅 : Provability T₀ T}

namespace Formula

/-- The interpretation reading `□A` as `A ⋏ 𝔅 A`. -/
@[grind]
def strongInterpret (f : Realization α L) (𝔅 : Provability T₀ T) : Formula α → Sentence L
  | #a    => f.val a
  | ⊥     => ⊥
  | A 🡒 B => A.strongInterpret f 𝔅 🡒 B.strongInterpret f 𝔅
  | □A    => A.strongInterpret f 𝔅 ⋏ 𝔅 (A.strongInterpret f 𝔅)

variable [𝔅.HBL2] {f : Realization α L} {A : Formula α}

omit [L.DecidableEq] in
lemma interpret_boxdotTranslate_iff_strongInterpret :
    T ⊢ Aᵇ.interpret f 𝔅 🡘 A.strongInterpret f 𝔅 := by
  induction A with
  | atom a => simp [interpret, strongInterpret];
  | falsum => dsimp [interpret, strongInterpret]; cl_prover;
  | imp A B ihA ihB => dsimp [interpret, strongInterpret]; cl_prover [ihA, ihB];
  | box A ih =>
    have h₁ : T ⊢ (□A)ᵇ.interpret f 𝔅 🡘 Aᵇ.interpret f 𝔅 ⋏ 𝔅 (Aᵇ.interpret f 𝔅) := by
      dsimp [interpret];
      cl_prover;
    have h₂ : T ⊢ 𝔅 (Aᵇ.interpret f 𝔅) 🡘 𝔅 (A.strongInterpret f 𝔅) := WeakerThan.pbl (𝔅.ext ih);
    change T ⊢ _ 🡘 A.strongInterpret f 𝔅 ⋏ 𝔅 (A.strongInterpret f 𝔅);
    cl_prover [ih, h₁, h₂];

lemma provable_interpret_boxdotTranslate_iff :
    T ⊢ Aᵇ.interpret f 𝔅 ↔ T ⊢ A.strongInterpret f 𝔅 :=
  ⟨fun h ↦ C_of_E_mp interpret_boxdotTranslate_iff_strongInterpret ⨀ h,
    fun h ↦ C_of_E_mpr interpret_boxdotTranslate_iff_strongInterpret ⨀ h⟩

lemma models_interpret_boxdotTranslate_iff {M : Type*} [Nonempty M] [Tarski.Structure L M]
    [M↓[L] ⊧* T] [𝔅.SoundOn M] :
    M↓[L] ⊧ Aᵇ.interpret f 𝔅 ↔ M↓[L] ⊧ A.strongInterpret f 𝔅 := by
  have hT₀ : M↓[L] ⊧* T₀ := models_of_subtheory (T := T₀) (U := T) (M := M) inferInstance;
  induction A with
  | box A ih =>
    suffices (M↓[L] ⊧ Aᵇ.interpret f 𝔅 ∧ M↓[L] ⊧ 𝔅 (Aᵇ.interpret f 𝔅)) ↔
        (M↓[L] ⊧ A.strongInterpret f 𝔅 ∧ M↓[L] ⊧ 𝔅 (A.strongInterpret f 𝔅)) by
      simpa [interpret, strongInterpret] using this;
    have h₁ : M↓[L] ⊧ 𝔅 (Aᵇ.interpret f 𝔅) → M↓[L] ⊧ 𝔅 (A.strongInterpret f 𝔅) := fun h ↦
      models_of_provable hT₀ <| 𝔅.D1 <| provable_interpret_boxdotTranslate_iff.mp (𝔅.sound_on h);
    have h₂ : M↓[L] ⊧ 𝔅 (A.strongInterpret f 𝔅) → M↓[L] ⊧ 𝔅 (Aᵇ.interpret f 𝔅) := fun h ↦
      models_of_provable hT₀ <| 𝔅.D1 <| provable_interpret_boxdotTranslate_iff.mpr (𝔅.sound_on h);
    grind;
  | _ => simp_all [interpret, strongInterpret];

end Formula

end FFL.ProvabilityLogic

end
