module

public import Foundation.Modal.Entailment.E

@[expose] public section

namespace LO.Modal.Entailment

open LO.Entailment LO.Entailment.FiniteContext

variable {S F : Type*} [BasicModalLogicalConnective F] [Entailment S F]
variable {𝓢 : S} [Entailment.E 𝓢] {φ : F}

variable [DecidableEq F]

instance {i j m n} [Entailment.HasAxiomGeach ⟨i, j, m, n⟩ 𝓢] : Entailment.HasAxiomGeach ⟨j, i, n, m⟩ 𝓢 where
  Geach := by
    intro φ;
    apply C_replace ?_ ?_ $ contra $ axiomGeach (g := ⟨i, j, m, n⟩) (φ := ∼φ);
    . apply C_trans diaItrDuality_mp;
      apply contra;
      apply K_right;
      apply multire;
      apply E_trans ?_ (E_symm multiDiaDuality);
      apply ENN_of_E;
      exact multi_ELLNN!;
    . apply C_trans $ CN_of_CN_left $ diaItrDuality_mpr;
      apply K_right;
      apply multire;
      apply multiDiaDuality;

def axiomTDual! [HasAxiomT 𝓢] : 𝓢 ⊢! φ 🡒 ◇φ := axiomGeach (g := ⟨0, 0, 0, 1⟩)
@[simp] lemma axiomTDual [HasAxiomT 𝓢] : 𝓢 ⊢ φ 🡒 ◇φ := ⟨axiomTDual!⟩

def axiomFourDual! [HasAxiomFour 𝓢] : 𝓢 ⊢! ◇◇φ 🡒 ◇φ := axiomGeach (g := ⟨2, 0, 0, 1⟩)
@[simp] lemma axiomFourDual [HasAxiomFour 𝓢] : 𝓢 ⊢ ◇◇φ 🡒 ◇φ := ⟨axiomFourDual!⟩

def axiomFiveDual! [HasAxiomFive 𝓢] : 𝓢 ⊢! ◇□φ 🡒 □φ := axiomGeach (g := ⟨1, 1, 1, 0⟩)
@[simp] lemma axiomFiveDual [HasAxiomFive 𝓢] : 𝓢 ⊢ ◇□φ 🡒 □φ := ⟨axiomFiveDual!⟩

end LO.Modal.Entailment
end
