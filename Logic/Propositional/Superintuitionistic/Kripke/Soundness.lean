import Logic.Propositional.Superintuitionistic.Kripke.Semantics

universe u

namespace LO.Propositional.Superintuitionistic.Kripke

variable {α : Type u} [Inhabited α]
variable {Λ : DeductionParameter α}

lemma sound : Λ ⊢! p → 𝔽(Λ) ⊧ p := LO.Kripke.sound

instance : Sound (𝐈𝐧𝐭 : DeductionParameter α) 𝔽((λ F => Transitive F ∧ Reflexive F)).alt :=
  LO.Kripke.instSoundOfCharacterizability (characterizability := Kripke.Characteraizable_Int)

/-
open LO.Kripke
open Formula Formula.Kripke
open Formula.Kripke.ValidOnFrame

variable {Λ : DeductionParameter α}

lemma sound! : Λ ⊢! p → 𝔽(Λ) ⊧ p := by simp_all [System.theory];

instance : Sound Λ 𝔽(Λ) := ⟨sound!⟩

lemma unprovable_bot (ne : 𝔽(Λ).Nonempty) : Λ ⊬! ⊥ := by
  apply (not_imp_not.mpr sound!);
  apply Kripke.ValidOnFrameClass.realize_bot ne;

instance (ne : 𝔽(Λ).Nonempty) : System.Consistent Λ := System.Consistent.of_unprovable $ unprovable_bot ne


lemma sound!_of_characteriazble [characteriability : Kripke.Characteraizable 𝔽(Λ) P] : Λ ⊢! p → 𝔽(P)# ⊧ p := by
  intro h F hF;
  apply sound! h;
  apply characteriability.characterize hF;

instance [Kripke.Characteraizable 𝔽(Λ) P] : Sound Λ 𝔽(P)# := ⟨sound!_of_characteriazble⟩

set_option pp.universes true

variable (P : Kripke.FrameProperty.{u})
         [characteriability : Kripke.Characteraizable 𝔽(Λ) P]

lemma unprovable_bot' : Λ ⊬! ⊥ := by
  apply (not_imp_not.mpr $ sound!_of_characteriazble (characteriability := characteriability));
  apply Kripke.ValidOnFrameClass.realize_bot;
  apply characteriability.nonempty;

instance : System.Consistent Λ := by
  apply System.Consistent.of_unprovable;
  exact unprovable_bot' (P := P);
-/

end LO.Propositional.Superintuitionistic.Kripke
