import Logic.Propositional.Intuitionistic.Kripke.Semantics
import Logic.Propositional.Intuitionistic.Deduction

namespace LO.Propositional.Intuitionistic

open Formula Kripke KripkeSatisfies

variable {α : Type u} [Inhabited α]

lemma Kripke.soundsAux (Γ : Theory α) (p : Formula α) (h : Γ ⊢ⁱ! p) : Γ ⊨ⁱ p := by
  induction h.some with
  | axm => simp_all [KripkeConsequence, Theory.KripkeSatisfies];
  | @modusPonens p q hpq hp ihpq ihp =>
    simp [KripkeConsequence];
    intro _ M w a;
    have spq := ihpq ⟨hpq⟩ M a;
    have sp := ihp ⟨hp⟩ M a;
    simpa using spq.modus_ponens sp;
  | eaxm ih =>
    obtain ⟨q, hq⟩ := ih;
    subst hq;
    apply KripkeConsequence.efq;
  | _ =>
    try first
    | apply KripkeConsequence.verum;
    | apply KripkeConsequence.imply₁;
    | apply KripkeConsequence.imply₂;
    | apply KripkeConsequence.conj₁;
    | apply KripkeConsequence.conj₂;
    | apply KripkeConsequence.conj₃;
    | apply KripkeConsequence.disj₁;
    | apply KripkeConsequence.disj₂;
    | apply KripkeConsequence.disj₃;

theorem Kripke.sounds {Γ : Theory α} {p : Formula α} : (Γ ⊢ⁱ! p) → (Γ ⊨ⁱ p) := Kripke.soundsAux Γ p

variable {β} [Inhabited β]

theorem Deduction.consistent : ∅ ⊬ⁱ! (⊥ : Formula α) := by
  by_contra hC;
  have : ∅ ⊨ⁱ (⊥ : Formula α) := Kripke.sounds (by simpa [System.unprovable_iff_not_provable] using hC);
  have : ¬(∅ ⊨ⁱ (⊥ : Formula α)) := by
    simp [KripkeConsequence, Theory.KripkeSatisfies];
    existsi β;
    existsi default;
    trivial;
  contradiction

end LO.Propositional.Intuitionistic
