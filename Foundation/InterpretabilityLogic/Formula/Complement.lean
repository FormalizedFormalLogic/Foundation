import Foundation.InterpretabilityLogic.Formula.Basic
import Foundation.Propositional.CMCF

namespace LO.InterpretabilityLogic

namespace Formula

variable {α}


@[elab_as_elim]
def cases_neg [DecidableEq α] {C : Formula α → Sort w}
    (hfalsum : C ⊥)
    (hatom   : ∀ a : α, C (atom a))
    (hneg    : ∀ φ : Formula α, C (∼φ))
    (himp    : ∀ (φ ψ : Formula α), ψ ≠ ⊥ → C (φ ➝ ψ))
    (hbox    : ∀ (φ : Formula α), C (□φ))
    (hrhd    : ∀ (φ ψ : Formula α), C (φ ▷ ψ))
    : (φ : Formula α) → C φ
  | ⊥       => hfalsum
  | atom a  => hatom a
  | □φ      => hbox φ
  | ∼φ      => hneg φ
  | φ ➝ ψ  => if e : ψ = ⊥ then e ▸ hneg φ else himp φ ψ e
  | φ ▷ ψ  => hrhd φ ψ

@[elab_as_elim]
def rec_neg [DecidableEq α] {C : Formula α → Sort w}
    (hfalsum : C ⊥)
    (hatom   : ∀ a : α, C (atom a))
    (hneg    : ∀ φ : Formula α, C (φ) → C (∼φ))
    (himp    : ∀ (φ ψ : Formula α), ψ ≠ ⊥ → C φ → C ψ → C (φ ➝ ψ))
    (hbox    : ∀ (φ : Formula α), C (φ) → C (□φ))
    (hrhd    : ∀ (φ ψ : Formula α), C (φ) → C (ψ) → C (φ ▷ ψ))
    : (φ : Formula α) → C φ
  | ⊥       => hfalsum
  | atom a  => hatom a
  | □φ      => hbox φ (rec_neg hfalsum hatom hneg himp hbox hrhd φ)
  | ∼φ      => hneg φ (rec_neg hfalsum hatom hneg himp hbox hrhd φ)
  | φ ➝ ψ  =>
    if e : ψ = ⊥
    then e ▸ hneg φ (rec_neg hfalsum hatom hneg himp hbox hrhd φ)
    else himp φ ψ e (rec_neg hfalsum hatom hneg himp hbox hrhd φ) (rec_neg hfalsum hatom hneg himp hbox hrhd ψ)
  | φ ▷ ψ  => hrhd φ ψ (rec_neg hfalsum hatom hneg himp hbox hrhd φ) (rec_neg hfalsum hatom hneg himp hbox hrhd ψ)


def complement : Formula α → Formula α
  | ∼φ => φ
  | φ  => ∼φ
instance : Compl (Formula α) where
  compl := complement

namespace complement

variable {φ ψ : Formula α}

@[grind] lemma neg_def : -(∼φ) = φ := by induction φ <;> rfl;

@[grind] lemma bot_def : -(⊥ : Formula α) = ∼(⊥) := rfl

@[grind] lemma box_def : -(□φ) = ∼(□φ) := rfl

@[grind] lemma rhd_def : -(φ ▷ ψ) = ∼(φ ▷ ψ) := rfl

@[grind]
lemma imp_def₁ (hq : ψ ≠ ⊥) : -(φ ➝ ψ) = ∼(φ ➝ ψ) := by
  suffices complement (φ ➝ ψ) = ∼(φ ➝ ψ) by tauto;
  unfold complement;
  split <;> simp_all;

@[grind] lemma imp_def₂ (hq : ψ = ⊥) : -(φ ➝ ψ) = φ := hq ▸ rfl

end complement

end Formula


open LO.Entailment in
instance [DecidableEq α] [Entailment S (Formula α)] {𝓢 : S} [Entailment.Cl 𝓢] : Entailment.ComplEquiv 𝓢 where
  compl_equiv! {φ} := by
    induction φ using Formula.cases_neg with
    | hneg => apply E_symm $ dn
    | himp φ ψ hψ =>
      rw [Formula.complement.imp_def₁ hψ];
      apply E_Id;
    | hbox | hatom | hfalsum | hrhd => apply E_Id;


end LO.InterpretabilityLogic
