import Foundation.Modal.Logic.WellKnown

namespace LO.Modal

namespace Logic

variable {L : Logic} [L.QuasiNormal] [L.Consistent] {φ ψ : Formula ℕ}

theorem makinson :
  letI p₁ := L ⊆ Logic.Ver;
  letI p₂ := Logic.KD ⊆ L ∧ L ⊆ Logic.Triv;
  (p₁ ∨ p₂) ∧ (¬p₁ ∨ ¬p₂) := by
  constructor;
  . apply or_iff_not_imp_left.mpr;
    intro h;
    have : Logic.KD ⊆ L := by sorry;
    constructor;
    . exact this;
    . sorry;
  . by_contra hC;
    push_neg at hC;
    have ⟨hVer, ⟨hKD, hTriv⟩⟩ := hC;
    have h₁ : ∼□⊥ ∈ Logic.Ver := by apply hVer; apply hKD; simp;
    have h₂ : □⊥ ∈ Logic.Ver := by simp;
    have : Hilbert.Ver ⊢! ⊥ := h₁ ⨀ h₂;
    have : Hilbert.Ver ⊬ ⊥ := System.Consistent.not_bot inferInstance;
    contradiction;


class VerFamily (L : Logic) : Prop where
  subset_Ver : L ⊆ Logic.Ver

lemma VerFamily.not_KD_subset_or_not_subset_Triv [L.VerFamily] : ¬(Logic.KD ⊆ L) ∨ ¬(L ⊆ Logic.Triv) := by
  have := (imp_iff_or_not.mpr $ Or.comm.mp $ makinson (L := L) |>.2) VerFamily.subset_Ver;
  tauto;


class TrivFamily (L : Logic) : Prop where
  KD_subset : Logic.KD ⊆ L
  subset_Triv : L ⊆ Logic.Triv

lemma TrivFamily.not_subset_Ver [L.TrivFamily] : ¬(L ⊆ Logic.Ver) := by
  apply imp_iff_or_not.mpr $ makinson.2;
  constructor;
  . exact TrivFamily.KD_subset;
  . exact TrivFamily.subset_Triv;


end Logic

end LO.Modal
