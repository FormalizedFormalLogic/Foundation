import Foundation.Modal.Logic.Extension
import Foundation.Modal.Kripke.Logic.S4

namespace LO.Modal

inductive Modality : Type
  | empty : Modality
  | box : Modality → Modality
  | dia : Modality → Modality
  | neg : Modality → Modality


namespace Modality

def toString : Modality → String
  | empty => "·"
  | box m => s!"□{m.toString}"
  | dia m => s!"◇{m.toString}"
  | neg m => s!"∼{m.toString}"

instance : Repr Modality := ⟨λ t _ => toString t⟩

instance : ToString Modality := ⟨Modality.toString⟩


#eval Modality.box $ .dia $ .neg $ .empty

def op : Modality → (Modality → Modality)
  | empty => id
  | box m => λ n => m.op $ box n
  | dia m => λ n => m.op $ dia n
  | neg m => λ n => m.op $ neg n

#eval (box $ box $ dia $ empty).op (neg $ dia $ box $ empty)


inductive Polarity
| pos
| neg

def Polarity.inv : Polarity → Polarity
  | pos => neg
  | neg => pos

def polarity : Modality → Polarity
  | empty => .pos
  | box _ => .pos
  | dia _ => .neg
  | neg m => m.polarity.inv


def size : Modality → Nat
  | empty => 0
  | box m => 1 + m.size
  | dia m => 1 + m.size
  | neg m => 1 + m.size


end Modality


namespace Formula

@[simp]
def attachModality (m : Modality) (φ : Formula ℕ) : Formula ℕ :=
  match m with
  | .empty  => φ
  | .box m' => □ (φ.attachModality m')
  | .dia m' => ◇ (φ.attachModality m')
  | .neg m' => ∼ (φ.attachModality m')

instance : CoeFun (Modality) (λ _ => Formula ℕ → Formula ℕ) := ⟨Formula.attachModality⟩

#eval (Modality.box $ .empty) (.atom 1)

end Formula


namespace Logic

open Formula

variable {M : Modality} {L : Logic} [L.IsNormal] {φ ψ : Formula ℕ} {s : Substitution ℕ}

lemma modality_congruence (h : φ ⭤ ψ ∈ L) : (M φ) ⭤ (M ψ) ∈ L := by
  induction M with
  | empty => simpa;
  | box m' ih => apply L.box_congruence ih;
  | dia m' ih => apply L.dia_regularity ih;
  | neg m' ih => apply L.neg_congruence ih;

lemma E_subst_attachModality : ((M φ)⟦s⟧) ⭤ (M (φ⟦s⟧)) ∈ L := by
  induction M with
  | empty => simp;
  | box m' ih => apply L.box_congruence ih;
  | dia m' ih => apply L.dia_regularity ih;
  | neg m' ih => apply L.neg_congruence ih;

lemma C_subst_attachModality_mp : ((M φ)⟦s⟧) ➝ (M (φ⟦s⟧)) ∈ L := by
  apply L.C_of_E_mp E_subst_attachModality;

lemma C_subst_attachModality_mpr : (M (φ⟦s⟧)) ➝ ((M φ)⟦s⟧) ∈ L := by
  apply L.C_of_E_mpr E_subst_attachModality;

lemma attachModality_subst_of_subst_attachModality : (M φ)⟦s⟧ ∈ L → M (φ⟦s⟧) ∈ L := L.mdp C_subst_attachModality_mp

lemma subst_attachModality_of_attachModality_subst : M (φ⟦s⟧) ∈ L → (M φ)⟦s⟧ ∈ L := L.mdp C_subst_attachModality_mpr

end Logic


namespace Modality

open Formula

variable {L : Logic} [L.IsNormal] {M₁ M₂ : Modality}

class Translation (L : Logic) (M₁ M₂ : Modality) where
  translate : ∀ a, (M₁ (.atom a)) ➝ (M₂ (.atom a)) ∈ L

notation M₁ " ⇝[" L "] " M₂ => Translation L M₁ M₂

instance : IsRefl _ (Translation L) := ⟨by
  intro M;
  constructor;
  intro a;
  apply L.of_mem_K;
  simp;
⟩

instance : IsTrans _ (Translation L) where
  trans M₁ M₂ M₃ := by
    intro T₁₂ T₂₃;
    constructor;
    intro a;
    exact L.C_trans (T₁₂.translate a) (T₂₃.translate a);

class Equivalence (L : Logic) (M₁ M₂ : Modality) where
  equivalent : ∀ a, (M₁ (.atom a)) ⭤ (M₂ (.atom a)) ∈ L

notation M₁ " ↭[" L "] " M₂ => Equivalence L M₁ M₂

instance [M₁ ↭[L] M₂] : M₁ ⇝[L] M₂ := ⟨fun a ↦ L.C_of_E_mp $ Equivalence.equivalent a⟩
instance [M₁ ↭[L] M₂] : M₂ ⇝[L] M₁ := ⟨fun a ↦ L.C_of_E_mpr $ Equivalence.equivalent a⟩

lemma iff_equivalence_bi_translate : (M₁ ↭[L] M₂) ↔ (M₁ ⇝[L] M₂) ∧ (M₂ ⇝[L] M₁) := by
  constructor;
  . intro eq;
    constructor <;> infer_instance;
  . intro ⟨T₁₂, T₂₁⟩;
    constructor;
    intro a;
    apply L.E_of_C_of_C;
    . exact T₁₂.translate a;
    . exact T₂₁.translate a;

instance [M₁ ⇝[L] M₂] [M₂ ⇝[L] M₁] : M₁ ↭[L] M₂ := by
  apply iff_equivalence_bi_translate.mpr;
  constructor <;> infer_instance;

instance : IsSymm _ (Equivalence L) := ⟨by
  intro _ _ eq;
  apply iff_equivalence_bi_translate.mpr;
  constructor <;> infer_instance;
⟩

instance : IsRefl _ (Equivalence L) := ⟨by
  intro _;
  apply iff_equivalence_bi_translate.mpr;
  constructor <;> apply _root_.refl;
⟩

instance : IsTrans _ (Equivalence L) := ⟨by
  intro a b c;
  intro E₁₂ E₂₃;
  have ⟨T₁₂, T₂₁⟩ := iff_equivalence_bi_translate.mp E₁₂;
  have ⟨T₂₃, T₃₂⟩ := iff_equivalence_bi_translate.mp E₂₃;
  apply iff_equivalence_bi_translate.mpr;
  constructor;
  . exact _root_.trans T₁₂ T₂₃;
  . exact _root_.trans T₃₂ T₂₁;
⟩

instance : IsEquiv _ (Equivalence L) where


lemma translate_fml [M₁ ⇝[L] M₂] (φ : Formula _) : M₁ φ ➝ M₂ φ ∈ L := by
  let s : Substitution ℕ := λ a => if a = 0 then φ else (.atom a);
  apply L.C_replace $ L.subst (Translation.translate (L := L) (M₁ := M₁) (M₂ := M₂) 0) (s := s);
  . simpa [s] using L.C_subst_attachModality_mpr (s := s) (φ := (.atom 0));
  . simpa [s] using L.C_subst_attachModality_mp (s := s) (φ := (.atom 0));

def translation_of_axiomInstance {a : ℕ} (h : (M₁ a) ➝ (M₂ a) ∈ L) : M₁ ⇝[L] M₂ := ⟨by
  intro b;
  let s : Substitution ℕ := λ c => if c = a then b else c;
  apply L.C_replace $ L.subst h (s := s);
  . simpa [s] using L.C_subst_attachModality_mpr (s := s) (φ := (.atom a));
  . simpa [s] using L.C_subst_attachModality_mp (s := s) (φ := (.atom a));
⟩


lemma equivalent_fml [M₁ ↭[L] M₂] (φ : Formula _) : M₁ φ ⭤ M₂ φ ∈ L := by
  apply L.E_of_C_of_C <;> apply translate_fml;

def equivalence_of_axiomInstance {a : ℕ} (h : (M₁ a) ⭤ (M₂ a) ∈ L) : M₁ ↭[L] M₂ := by
  apply iff_equivalence_bi_translate.mpr;
  constructor;
  . apply translation_of_axiomInstance (a := a);
    apply L.C_of_E_mp h;
  . apply translation_of_axiomInstance (a := a);
    apply L.C_of_E_mpr h;

end Modality


namespace Logic

open Modality
open Formula

variable {H : Hilbert ℕ} [H.HasK]

instance [H.HasT] : (box $ empty) ⇝[H.logic] (empty) :=
  translation_of_axiomInstance (a := Hilbert.HasT.p H) $ by simp;

instance [H.HasTc] : (empty) ⇝[H.logic] (box $ empty) :=
  translation_of_axiomInstance (a := Hilbert.HasTc.p H) $ by simp;

instance [H.HasFour] : (box $ empty) ⇝[H.logic] (box $ box $ empty) :=
  translation_of_axiomInstance (a := Hilbert.HasFour.p (H := H)) $ by simp

instance [H.HasB] : (empty) ⇝[H.logic] (box $ dia $ empty) :=
  translation_of_axiomInstance (a := Hilbert.HasB.p (H := H)) $ by simp;

instance [H.HasD] : (box $ empty) ⇝[H.logic] (dia $ empty) :=
  translation_of_axiomInstance (a := Hilbert.HasD.p (H := H)) $ by simp;

instance [H.HasFive] : (dia $ empty) ⇝[H.logic] (box $ dia $ empty) :=
  translation_of_axiomInstance (a := Hilbert.HasFive.p (H := H)) $ by simp;

instance : (box $ empty) ⇝[Logic.S4] (empty) := inferInstance

instance : (box $ empty) ↭[Logic.Triv] (empty) := inferInstance

end Logic


end LO.Modal
