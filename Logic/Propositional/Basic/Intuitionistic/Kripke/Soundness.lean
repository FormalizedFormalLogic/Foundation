import Logic.Propositional.Basic.Intuitionistic.Deduction
import Logic.Propositional.Basic.Intuitionistic.Kripke.Semantics

namespace LO.Propositional.Basic.Intuitionistic

variable {α : Type u} [Inhabited α]

lemma Kripke.sounds (h : Γ ⊢ⁱ! p) : Γ ⊨ⁱ p := by
  induction h.some with
  | axm => simp_all [Formula.Intuitionistic.Kripke.Consequence, Theory.Intuitionistic.Kripke.Satisfies];
  | @modusPonens p q hpq hp ihpq ihp =>
    simp [Formula.Intuitionistic.Kripke.Consequence];
    intro _ M w a;
    have spq := ihpq ⟨hpq⟩ M a;
    have sp := ihp ⟨hp⟩ M a;
    simpa using spq.modus_ponens sp;
  | eaxm ih =>
    obtain ⟨q, hq⟩ := ih;
    subst hq;
    apply Formula.Intuitionistic.Kripke.Consequence.efq;
  | _ =>
    try first
    | apply Formula.Intuitionistic.Kripke.Consequence.verum;
    | apply Formula.Intuitionistic.Kripke.Consequence.imply₁;
    | apply Formula.Intuitionistic.Kripke.Consequence.imply₂;
    | apply Formula.Intuitionistic.Kripke.Consequence.conj₁;
    | apply Formula.Intuitionistic.Kripke.Consequence.conj₂;
    | apply Formula.Intuitionistic.Kripke.Consequence.conj₃;
    | apply Formula.Intuitionistic.Kripke.Consequence.disj₁;
    | apply Formula.Intuitionistic.Kripke.Consequence.disj₂;
    | apply Formula.Intuitionistic.Kripke.Consequence.disj₃;

variable {β} [Inhabited β]

theorem Deduction.consistent : ∅ ⊬ⁱ! (⊥ : Formula α) := by
  by_contra hC;
  have : ∅ ⊨ⁱ (⊥ : Formula α) := Kripke.sounds (by simpa [System.unprovable_iff_not_provable] using hC);
  have : ¬(∅ ⊨ⁱ (⊥ : Formula α)) := by
    simp [Formula.Intuitionistic.Kripke.Consequence, Theory.Intuitionistic.Kripke.Satisfies];
    existsi β;
    existsi default;
    trivial;
  contradiction

end LO.Propositional.Basic.Intuitionistic
