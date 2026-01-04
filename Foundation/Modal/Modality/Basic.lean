import Foundation.Modal.Hilbert.Normal.Basic
import Foundation.Modal.Logic.SumNormal
import Foundation.Meta.ClProver


namespace LO.Modal

open Formula
open LO.Entailment LO.Modal.Entailment

inductive Modality : Type
  | empty : Modality
  | box : Modality → Modality
  | dia : Modality → Modality
  | neg : Modality → Modality
deriving DecidableEq, BEq

namespace Modality

variable {m m₁ m₂ m₃ : Modality} {n n₁ n₂ : ℕ}

notation:max "-" => Modality.empty
prefix:80 "□" => Modality.box
prefix:80 "◇" => Modality.dia
prefix:80 "∼" => Modality.neg

def toString : Modality → String
  | - => "-"
  | □m => s!"□{m.toString}"
  | ◇m => s!"◇{m.toString}"
  | ∼m => s!"∼{m.toString}"

instance : Repr Modality := ⟨λ t _ => toString t⟩

instance : ToString Modality := ⟨Modality.toString⟩

/-- pure box -/
abbrev pbox : Modality := □-
notation:81 "□" => pbox

/-- pure diamond -/
abbrev pdia : Modality := ◇-
notation:81 "◇" => pdia

/-- pure negation -/
abbrev pneg : Modality := ∼-
notation:81 "∼" => pneg

#eval □◇◇

def sneg : Modality → Modality
  | -  => ∼-
  | □m => ∼□m
  | ◇m => ∼◇m
  | ∼m => m
prefix:80 "⩪" => Modality.sneg

abbrev psneg : Modality := ⩪-
notation:81 "⩪" => psneg

def add : Modality → Modality → Modality
  | - ,  m₂ => m₂
  | □m₁, m₂ => □(m₁.add m₂)
  | ◇m₁, m₂ => ◇(m₁.add m₂)
  | ∼m₁, m₂ => ∼(m₁.add m₂)
instance : Add Modality := ⟨Modality.add⟩

@[simp] lemma add_empty_left : - + m = m := by rfl
@[simp] lemma add_box_left : □m₁ + m₂ = □(m₁ + m₂) := rfl
@[simp] lemma add_dia_left : ◇m₁ + m₂ = ◇(m₁ + m₂) := rfl
@[simp] lemma add_neg_left : ∼m₁ + m₂ = ∼(m₁ + m₂) := rfl

@[simp]
lemma add_empty_right : m + - = m := by
  induction m with
  | empty => rfl
  | box m ih | dia m ih | neg m ih => simp [ih]

@[simp]
lemma add_assoc : (m₁ + m₂) + m₃ = m₁ + (m₂ + m₃) := by
  induction m₁ with
  | empty => rfl
  | box m₁ ih | dia m₁ ih | neg m₁ ih => simp [ih]

instance : Std.Associative (α := Modality) (· + ·) := ⟨@add_assoc⟩

inductive Polarity
| pos
| neg

variable {P : Polarity}

def Polarity.inv : Polarity → Polarity
  | pos => neg
  | neg => pos

@[simp]
lemma Polarity.eq_invinv : P.inv.inv = P := by
  induction P with
  | pos => rfl
  | neg => rfl

def polarity : Modality → Polarity
  | -  => .pos
  | □m => m.polarity
  | ◇m => m.polarity
  | ∼m => m.polarity.inv

@[simp] lemma pempty_pos : (-).polarity = .pos := rfl
@[simp] lemma pbox_pos   : (□).polarity = .pos := rfl
@[simp] lemma pdia_pos   : (◇).polarity = .pos := rfl
@[simp] lemma pneg_pos   : (∼).polarity = .neg := rfl
@[simp] lemma box_pos    : (□m).polarity = m.polarity := by simp [polarity]
@[simp] lemma dia_pos    : (◇m).polarity = m.polarity := by simp [polarity]
@[simp] lemma neg_pos    : (∼m).polarity = m.polarity.inv := by simp [polarity]

def size : Modality → Nat
  | -  => 0
  | □m => m.size + 1
  | ◇m => m.size + 1
  | ∼m => m.size + 1

@[simp] lemma empty_size_zero : (-).size = 0 := rfl
@[simp] lemma pbox_size_one   : (□).size = 1 := rfl
@[simp] lemma pdia_size_one   : (◇).size = 1 := rfl
@[simp] lemma pneg_size_one   : (∼).size = 1 := rfl
@[simp] lemma box_size_succ   : (□m).size = m.size + 1 := rfl
@[simp] lemma dia_size_succ   : (◇m).size = m.size + 1 := rfl
@[simp] lemma neg_size_succ   : (∼m).size = m.size + 1 := rfl

@[simp]
lemma sneg_size_le_succ : (⩪m).size ≤ (m.size + 1) := by
  match m with
  | - | □m | ◇m => simp [sneg];
  | ∼m => simp [sneg]; omega;

@[simp]
lemma sneg_size_le_neg_size : (⩪m).size ≤ (∼m).size := by trans (m.size + 1) <;> simp [sneg_size_le_succ];

@[simp]
lemma sneg_sneg_size_le_succ : (⩪⩪m).size ≤ m.size + 1 := by
  match m with
  | - | □m | ◇m | ∼- | ∼□m | ∼◇m => simp [sneg];
  | ∼∼m => simp [sneg]; omega;

@[simp]
lemma iff_size_0 : m.size = 0 ↔ m = - := by
  constructor;
  . match m with
    | -  => tauto;
    | □_ | ◇_ | ∼_ => simp;
  . rintro rfl; simp;

lemma iff_size_1 : m.size = 1 ↔ m = □ ∨ m = ◇ ∨ m = ∼ := by
  constructor;
  . match m with | - | □_ | ◇_ | ∼_ => simp;
  . rintro (rfl | rfl | rfl) <;> simp;

lemma iff_size_2 : m.size = 2 ↔
                   m = □□ ∨ m = □◇ ∨ m = □∼ ∨
                   m = ◇□ ∨ m = ◇◇ ∨ m = ◇∼ ∨
                   m = ∼□ ∨ m = ∼◇ ∨ m = ∼∼ := by
  constructor;
  . match m with
    | -  => simp;
    | □m | ◇m | ∼m  =>
      suffices m.size = 1 → (m = □) ∨ (m = ◇) ∨ (m = ∼) by simpa
      exact iff_size_1.mp;
  . rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp;

@[simp]
lemma add_size : (m₁ + m₂).size = m₁.size + m₂.size := by
  induction m₁ with
  | empty => simp [add];
  | box m₁ ih | dia m₁ ih | neg m₁ ih => simp [add, ih]; omega;

lemma split_left₁ (hm : m.size = n₂ + 1) : ∃ m₁ m₂, m₁.size = 1 ∧ m₂.size = n₂ ∧ m = m₁ + m₂ := by
  match m with
  | -  => tauto;
  | □m =>
    use □, m;
    refine ⟨by tauto, ?_, ?_⟩;
    . simpa using hm;
    . rfl;
  | ◇m =>
    use ◇, m;
    refine ⟨by tauto, ?_, ?_⟩;
    . simpa using hm;
    . rfl;
  | ∼m =>
    use ∼, m;
    refine ⟨by tauto, ?_, ?_⟩;
    . simpa using hm;
    . rfl;

lemma split_left₁' (hm : m.size = n + 1) : ∃ m', m'.size = n ∧ (m = □m' ∨ m = ◇m' ∨ m = ∼m') := by
  obtain ⟨m₁, m₂, hm₁, hm₂, rfl⟩ := split_left₁ hm;
  use m₂;
  constructor;
  . assumption;
  . rcases iff_size_1.mp hm₁ with (rfl | rfl | rfl) <;> tauto;

lemma split_right₁ (hm : m.size = n + 1) : ∃ m₁ m₂, m₁.size = n ∧ m₂.size = 1 ∧ m = m₁ + m₂ := by
  induction n generalizing m with
  | zero => use (-), m; tauto;
  | succ n ih =>
    match m with
    | -  => tauto;
    | □m =>
      obtain ⟨m₁, m₂, hm₁, hm₂, rfl⟩ := @ih m $ by simpa using hm;
      use (□m₁), m₂;
      simp_all;
    | ◇m =>
      obtain ⟨m₁, m₂, hm₁, hm₂, rfl⟩ := @ih m $ by simpa using hm;
      use (◇m₁), m₂;
      simp_all;
    | ∼m =>
      obtain ⟨m₁, m₂, hm₁, hm₂, rfl⟩ := @ih m $ by simpa using hm;
      use (∼m₁), m₂;
      simp_all;

lemma split (hm : m.size = n₁ + n₂) : ∃ m₁ m₂, m₁.size = n₁ ∧ m₂.size = n₂ ∧ m = m₁ + m₂ := by
  induction n₂ generalizing m with
  | zero =>
    subst hm;
    use m, -;
    refine ⟨?_, ?_, ?_⟩ <;> simp;
  | succ n₂ ih =>
    replace hm : m.size = (n₁ + n₂) + 1 := hm;
    obtain ⟨m₁, m₂, hm₁, hm₂, rfl⟩  := split_right₁ hm;
    obtain ⟨m₃, m₄, hm₃, hm₄, rfl⟩ := @ih m₁ hm₁;
    use m₃, (m₄ + m₂);
    refine ⟨by omega, ?_, ?_⟩;
    . simp_all;
    . simp [add_assoc]

lemma split_left₂' (hm : m.size = n + 2) : ∃ m', m'.size = n ∧
                                                    (m = □□m' ∨ m = □◇m' ∨ m = □∼m' ∨
                                                     m = ◇□m' ∨ m = ◇◇m' ∨ m = ◇∼m' ∨
                                                     m = ∼□m' ∨ m = ∼◇m' ∨ m = ∼∼m') := by
  obtain ⟨m₁, m₂, hm₁, hm₂, rfl⟩ := split $ show m.size = 2 + n by omega;
  use m₂;
  constructor;
  . assumption;
  . rcases iff_size_2.mp hm₁ with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp;

lemma split_left_le₁ (hm : m.size ≤ n₂ + 1) : ∃ m₁ m₂, m₁.size ≤ 1 ∧ m₂.size ≤ n₂ ∧ m = m₁ + m₂ := by
  induction n₂ generalizing m with
  | zero => simp_all;
  | succ n ih =>
    rcases Nat.le_or_eq_of_le_succ hm with (h | hm);
    . obtain ⟨m₁, m₂, hm₁, hm₂, rfl⟩ := @ih m h;
      use m₁, m₂;
      refine ⟨by omega, by omega, rfl⟩;
    . obtain ⟨m₁, m₂, hm₁, hm₂, rfl⟩ := split_left₁ hm;
      use m₁, m₂;
      refine ⟨by omega, by omega, rfl⟩;

lemma split_right_le₁ (hm : m.size ≤ n + 1) : ∃ m₁ m₂, m₁.size ≤ n ∧ m₂.size ≤ 1 ∧ m = m₁ + m₂ := by
  induction n generalizing m with
  | zero => use (-), m; tauto;
  | succ n ih =>
    rcases Nat.le_or_eq_of_le_succ hm with (h | hm);
    . obtain ⟨m₁, m₂, hm₁, hm₂, rfl⟩ := @ih m h;
      use m₁, m₂;
      refine ⟨by omega, by omega, rfl⟩;
    . obtain ⟨m₁, m₂, hm₁, hm₂, rfl⟩ := split_right₁ hm;
      use m₁, m₂;
      refine ⟨by omega, by omega, rfl⟩;

lemma split_le (hm : m.size ≤ n₁ + n₂) : ∃ m₁ m₂, m₁.size ≤ n₁ ∧ m₂.size ≤ n₂ ∧ m = m₁ + m₂ := by
  induction n₂ generalizing m with
  | zero =>
    simp at hm;
    use m, -;
    refine ⟨?_, ?_, ?_⟩;
    . assumption;
    . simp;
    . simp;
  | succ n₂ ih =>
    replace hm : m.size ≤ (n₁ + n₂) + 1 := hm;
    obtain ⟨m₁, m₂, hm₁, hm₂, rfl⟩  := split_right_le₁ hm;
    obtain ⟨m₃, m₄, hm₃, hm₄, rfl⟩ := @ih m₁ hm₁;
    use m₃, (m₄ + m₂);
    refine ⟨by omega, ?_, ?_⟩;
    . simp; omega;
    . simp [add_assoc]

instance : DecidablePred (Modality.size · = n) := inferInstance

end Modality


namespace Formula

variable {m m₁ m₂ : Modality} {φ ψ : Formula ℕ}

@[simp]
def attachmodality (m : Modality) (φ : Formula ℕ) : Formula ℕ :=
  match m with
  | -   => φ
  | □m' => □ (φ.attachmodality m')
  | ◇m' => ◇ (φ.attachmodality m')
  | ∼m' => ∼ (φ.attachmodality m')

instance : CoeFun (Modality) (λ _ => Formula ℕ → Formula ℕ) := ⟨Formula.attachmodality⟩

#eval (□-) (.atom 1)

@[simp]
lemma eq_attachModality_add : m₁ (m₂ φ) = (m₁ + m₂) φ := by
  induction m₁ with
  | empty      => rfl
  | box m₁' ih
  | dia m₁' ih
  | neg m₁' ih => simp [ih]

end Formula


namespace Logic

variable {m : Modality} {L : Logic _} [L.IsNormal] {φ ψ : Formula ℕ} {s : Substitution ℕ}

lemma modality_congruence (h : L ⊢ φ ⭤ ψ) : L ⊢ (m φ) ⭤ (m ψ) := by
  induction m with
  | empty => simpa [-iff_provable];
  | box m' ih => apply box_congruence! ih;
  | dia m' ih => apply dia_congruence! ih;
  | neg m' ih => apply neg_congruence! ih;

lemma E_subst_attachmodality : L ⊢ ((m φ)⟦s⟧) ⭤ (m (φ⟦s⟧)) := by
  induction m with
  | empty => simp;
  | box m' ih => apply box_congruence! ih;
  | dia m' ih => apply dia_congruence! ih;
  | neg m' ih => apply neg_congruence! ih;

lemma C_subst_attachmodality_mp : L ⊢ ((m φ)⟦s⟧) ➝ (m (φ⟦s⟧)) := by
  apply C_of_E_mp! E_subst_attachmodality;

lemma C_subst_attachmodality_mpr : L ⊢ (m (φ⟦s⟧)) ➝ ((m φ)⟦s⟧) := by
  apply C_of_E_mpr! E_subst_attachmodality;

lemma attachmodality_subst_of_subst_attachmodality : L ⊢ (m φ)⟦s⟧ → L ⊢ m (φ⟦s⟧) := mdp! $ C_subst_attachmodality_mp

lemma subst_attachmodality_of_attachmodality_subst : L ⊢ m (φ⟦s⟧) → L ⊢ (m φ)⟦s⟧ := mdp! $ C_subst_attachmodality_mpr

end Logic


namespace Modality

open Formula

variable {L : Logic ℕ} [L.IsNormal] {m₁ m₂ : Modality}

class Translation (L : Logic _) (m₁ m₂ : Modality) where
  translate : ∀ a,  L ⊢ (m₁ (.atom a)) ➝ (m₂ (.atom a))

notation:90 M₁ " ⤳[" L "] " M₂ => Translation L M₁ M₂

instance : IsRefl _ (· ⤳[L] ·) := ⟨by
  intro M;
  constructor;
  simp;
⟩

instance : IsTrans _ (· ⤳[L] ·) where
  trans M₁ M₂ M₃ := by
    intro T₁₂ T₂₃;
    constructor;
    intro a;
    exact C!_trans (T₁₂.translate a) (T₂₃.translate a);

class Equivalence (L : Logic ℕ) (M₁ M₂ : Modality) where
  equivalent : ∀ a, L ⊢ (M₁ (.atom a)) ⭤ (M₂ (.atom a))

notation M₁ " ≅[" L "] " M₂ => Equivalence L M₁ M₂

instance [m₁ ≅[L] m₂] : m₁ ⤳[L] m₂ := ⟨fun a ↦ C_of_E_mp! $ Equivalence.equivalent a⟩
instance [m₁ ≅[L] m₂] : m₂ ⤳[L] m₁ := ⟨fun a ↦ C_of_E_mpr! $ Equivalence.equivalent a⟩

lemma iff_equivalence_bi_translate : (m₁ ≅[L] m₂) ↔ (m₁ ⤳[L] m₂) ∧ (m₂ ⤳[L] m₁) := by
  constructor;
  . intro eq;
    constructor <;> infer_instance;
  . intro ⟨T₁₂, T₂₁⟩;
    constructor;
    intro a;
    apply E!_intro;
    . exact T₁₂.translate a;
    . exact T₂₁.translate a;

instance [m₁ ⤳[L] m₂] [m₂ ⤳[L] m₁] : m₁ ≅[L] m₂ := by
  apply iff_equivalence_bi_translate.mpr;
  constructor <;> infer_instance;

instance : Std.Symm (· ≅[L] ·) := ⟨by
  intro _ _ eq;
  apply iff_equivalence_bi_translate.mpr;
  constructor <;> infer_instance;
⟩

instance : IsRefl _ (· ≅[L] ·) := ⟨by
  intro _;
  apply iff_equivalence_bi_translate.mpr;
  constructor <;> apply _root_.refl;
⟩

instance : IsTrans _ (· ≅[L] ·) := ⟨by
  intro a b c;
  intro E₁₂ E₂₃;
  have ⟨T₁₂, T₂₁⟩ := iff_equivalence_bi_translate.mp E₁₂;
  have ⟨T₂₃, T₃₂⟩ := iff_equivalence_bi_translate.mp E₂₃;
  apply iff_equivalence_bi_translate.mpr;
  constructor;
  . exact _root_.trans T₁₂ T₂₃;
  . exact _root_.trans T₃₂ T₂₁;
⟩

instance : IsEquiv _ (· ≅[L] ·) where


lemma Translation.translate_fml [m₁ ⤳[L] m₂] (φ : Formula _) : L ⊢ m₁ φ ➝ m₂ φ := by
  let s : Substitution ℕ := λ a => if a = 0 then φ else (.atom a);
  apply C!_replace ?_ ?_ $ L.subst (Translation.translate (L := L) (m₁ := m₁) (m₂ := m₂) 0) (s := s);
  . simpa [s] using L.C_subst_attachmodality_mpr (s := s) (φ := (.atom 0));
  . simpa [s] using L.C_subst_attachmodality_mp (s := s) (φ := (.atom 0));

def translation_of_axiomInstance {a : ℕ} (h : L ⊢ (m₁ a) ➝ (m₂ a)) : m₁ ⤳[L] m₂ := ⟨by
  intro b;
  let s : Substitution ℕ := λ c => if c = a then b else c;
  apply C!_replace ?_ ?_ $ L.subst (s := s) h;
  . simpa [s] using L.C_subst_attachmodality_mpr (s := s) (φ := (.atom a));
  . simpa [s] using L.C_subst_attachmodality_mp (s := s) (φ := (.atom a));
⟩

lemma translation_expand_right {L : Logic _} [L.IsNormal] (m₁ m₂ m) [m₁ ⤳[L] m₂] : (m₁ + m) ⤳[L] (m₂ + m) := by
  constructor;
  intro a;
  simpa using Translation.translate_fml (L := L) (m₁ := m₁) (m₂ := m₂) $ m (.atom a);

lemma translation_expand_left {L : Logic _} [L.IsNormal] (m₁ m₂ m) [m₁ ⤳[L] m₂] [m ⤳[L] (-)] : (m + m₁) ⤳[L] (m₂) := by
  constructor;
  intro a;
  have H₁ : L ⊢ (m + m₁) (atom a) ➝ m₁ (atom a) := by simpa using Translation.translate_fml (m₁ := m) (m₂ := (-)) (m₁ (.atom a));
  have H₂ : L ⊢ m₁ (atom a) ➝ m₂ (atom a) := Translation.translate_fml (.atom a);
  exact C!_trans H₁ H₂;

lemma Equivalence.equivalent_fml [m₁ ≅[L] m₂] (φ : Formula _) : L ⊢ m₁ φ ⭤ m₂ φ := by
  apply E!_intro <;> apply Translation.translate_fml;

def equivalence_of_axiomInstance {a : ℕ} (h : L ⊢ (m₁ a) ⭤ (m₂ a)) : m₁ ≅[L] m₂ := by
  apply iff_equivalence_bi_translate.mpr;
  constructor;
  . apply translation_of_axiomInstance (a := a);
    apply C_of_E_mp! h;
  . apply translation_of_axiomInstance (a := a);
    apply C_of_E_mpr! h;

lemma equivalence_expand_right {L : Logic _} [L.IsNormal] (m₁ m₂ m) [m₁ ≅[L] m₂] : (m₁ + m) ≅[L] (m₂ + m) := by
  apply iff_equivalence_bi_translate.mpr;
  constructor <;> apply translation_expand_right;

lemma equivalence_expand_left {L : Logic _} [L.IsNormal] (m₁ m₂ m) [m₁ ≅[L] m₂] : (m + m₁) ≅[L] (m + m₂) := by
  constructor;
  intro a;
  induction m with
  | empty    => apply Equivalence.equivalent_fml (m₁ := m₁) (m₂ := m₂);
  | box m ih => apply box_congruence! ih;
  | dia m ih => apply dia_congruence! ih;
  | neg m ih => apply neg_congruence! ih;

end Modality


namespace Logic

open Modality
open Formula


section

open LO.Entailment

variable {L : Logic _} [L.IsNormal] {m : Modality}

instance : m ⤳[L] m := refl m

instance : (□) ≅[L] (∼◇∼) := ⟨by simp⟩

instance : (◇) ≅[L] (∼□∼) := ⟨by simp⟩

instance : (∼∼) ≅[L] (-) := by
  apply equivalence_of_axiomInstance (a := 0);
  simp only [attachmodality];
  cl_prover;

instance : (□∼) ≅[L] (∼◇) := by
  apply equivalence_of_axiomInstance (a := 0);
  simp only [attachmodality];
  -- TODO: extract ` □∼p ⭤ ∼◇p`
  apply E!_intro;
  . simp;
  . apply C!_trans (ψ := ∼∼□(∼(.atom 0)));
    . apply contra!; simp;
    . simp;

instance : (◇∼) ≅[L] (∼□) := by
  apply equivalence_of_axiomInstance (a := 0);
  simp only [attachmodality];
  -- TODO: extract `◇∼p ⭤ ∼□p`
  apply E!_intro;
  . apply C!_trans (ψ := ∼□(∼∼(.atom 0)));
    . simp;
    . simp;
  . apply C!_trans (ψ := ∼∼◇(∼(.atom 0)));
    . sorry;
    . simp;

end

section

open Hilbert.Normal

variable {H : Axiom ℕ} [H.HasK] {m : outParam (Modality)}
variable {L : Logic _} [L.IsNormal]

instance [Entailment.HasAxiomT L] : (□m) ⤳[L] (m) := translation_of_axiomInstance (a := 0) $ by simp;
instance [Entailment.HasAxiomFour L] : (□m) ⤳[L] (□□m) := translation_of_axiomInstance (a := 0) $ by simp;
instance [Entailment.HasAxiomTc L] : (m) ⤳[L] (□m) := translation_of_axiomInstance (a := 0) $ by simp;
instance [Entailment.HasAxiomB L] : (m) ⤳[L] (□◇m) := translation_of_axiomInstance (a := 0) $ by simp;
instance [Entailment.HasAxiomD L] : (□m) ⤳[L] (◇m) := translation_of_axiomInstance (a := 0) $ by simp;
instance [Entailment.HasAxiomFive L] : (◇m) ⤳[L] (□◇m) := translation_of_axiomInstance (a := 0) $ by simp;

end

instance : (□-) ⤳[Modal.S4] (-) := inferInstance

instance : (□-) ≅[Modal.Triv] (-) := inferInstance


end Logic


abbrev Modalities := Finset Modality

namespace Modalities

open Modality

variable {n : ℕ} {m : Modality} {M : Modalities}

def max_size (M : Modalities) (M_nonempty : M.Nonempty := by decide) := M.image (λ m => m.size) |>.max' $ Finset.image_nonempty.mpr M_nonempty

-- #eval max_size ({-, ∼, □, □, □, □□□□□□□, □, ◇})

lemma lt_max_size_of_mem {M_nonempty : M.Nonempty} (hM : m ∈ M) : m.size ≤ (M.max_size M_nonempty) := by
  apply Finset.le_max';
  simp only [Finset.mem_image];
  use m;

def allOfSize : ℕ → Modalities
  | 0 => {-}
  | n + 1 =>
    (allOfSize n).image (λ m => ∼m) ∪
    (allOfSize n).image (λ m => □m) ∪
    (allOfSize n).image (λ m => ◇m)

@[simp] lemma allOfSize.eq_zero : allOfSize 0 = {-} := rfl

lemma allOfSize.iff_mem_eq_size : m ∈ allOfSize n ↔ m.size = n := by
  induction n generalizing m with
  | zero => simp [allOfSize];
  | succ n ih =>
    simp only [allOfSize, Finset.union_assoc, Finset.mem_union, Finset.mem_image];
    constructor;
    . rintro (⟨m, ⟨hm, rfl⟩⟩ | ⟨M, ⟨hm, rfl⟩⟩ | ⟨M, ⟨hm, rfl⟩⟩) <;> simp [ih.mp hm];
    . intro;
      match m with
      | -  => contradiction;
      | ∼m => simp_all [allOfSize];
      | □m => simp_all [allOfSize];
      | ◇m => simp_all [allOfSize];

@[simp]
lemma allOfSize.mem_of_size : m ∈ allOfSize m.size := by simp only [allOfSize.iff_mem_eq_size];

@[simp]
lemma allOfSize.iff_mem_zero : m ∈ allOfSize 0 ↔ m = - := by
  simp [allOfSize.iff_mem_eq_size]

instance : DecidablePred (· ∈ allOfSize n) := by
  simp only [allOfSize.iff_mem_eq_size];
  infer_instance;

-- #eval allOfSize 2
-- #eval □ ∈ allOfSize 1

lemma allOfSize.eq_succ_left₁ : m ∈ allOfSize (n + 1) → ∃ m₁ m₂, m₁ ∈ allOfSize 1 ∧ m₂ ∈ allOfSize n ∧ m = m₁ + m₂ := by
  simp only [allOfSize.iff_mem_eq_size];
  apply split_left₁;

lemma allOfSize.eq_succ_right₁ : m ∈ allOfSize (n + 1) → ∃ m₁ m₂, m₁ ∈ allOfSize n ∧ m₂ ∈ allOfSize 1 ∧ m = m₁ + m₂ := by
  simp only [allOfSize.iff_mem_eq_size];
  apply split_right₁;


def allOfSizeLe : Nat → Modalities
  | 0 => allOfSize 0
  | n + 1 => allOfSizeLe n ∪ allOfSize (n + 1)

-- #eval allOfSizeLe 3

lemma allOfSizeLe.iff_mem_le_size : m ∈ allOfSizeLe n ↔ m.size ≤ n := by
  induction n with
  | zero => simp [allOfSizeLe];
  | succ n ih =>
    simp only [allOfSizeLe, Finset.mem_union];
    constructor;
    . rintro (h | h);
      . have := ih.mp h; omega;
      . have := allOfSize.iff_mem_eq_size.mp h; omega;
    . intro h;
      replace h := lt_or_eq_of_le h;
      rcases h with (h | h);
      . left;
        apply ih.mpr;
        omega;
      . right;
        exact allOfSize.iff_mem_eq_size.mpr h;

instance : DecidablePred (· ∈ allOfSizeLe n) := by
  simp only [allOfSizeLe.iff_mem_le_size];
  infer_instance;

#eval □◇ ∈ allOfSizeLe 2

@[simp]
lemma allOfSizeLe.iff_mem_zero : m ∈ allOfSizeLe 0 ↔ m = - := by
  simp [allOfSizeLe.iff_mem_le_size, allOfSize.iff_mem_eq_size]

@[simp]
lemma allOfSizeLe.mem_empty : - ∈ allOfSizeLe n := by induction n <;> simp_all [allOfSizeLe];

lemma allOfSizeLe.subset_of_le (h : n₁ ≤ n₂) : allOfSizeLe n₁ ⊆ allOfSizeLe n₂ := by
  intro m;
  simp_all [allOfSizeLe.iff_mem_le_size]
  omega;

lemma allOfSizeLe.eq_succ_left₁ : m ∈ allOfSizeLe (n₂ + 1) → ∃ m₁ m₂, m₁ ∈ allOfSizeLe 1 ∧ m₂ ∈ allOfSizeLe n₂ ∧ m = (m₁ + m₂) := by
  simp only [allOfSizeLe.iff_mem_le_size];
  apply split_left_le₁;

lemma allOfSizeLe.eq_succ_right₁ : m ∈ allOfSizeLe (n₁ + 1) → ∃ m₁ m₂, m₁ ∈ allOfSizeLe n₁ ∧ m₂ ∈ allOfSizeLe 1 ∧ m = (m₁ + m₂) := by
  simp only [allOfSizeLe.iff_mem_le_size];
  apply split_right_le₁;


def posOfSize : ℕ → Modalities
  | 0 => {-}
  | n + 1 => (posOfSize n).image (λ m => □m) ∪ (posOfSize n).image (λ m => ◇m)

#eval posOfSize 3

end Modalities



section

open Modality Modalities

variable {L : Logic _} {M : Modalities} {n : ℕ} {n : ℕ}

/-- In `L`, every `n`-size modality is reduced to some modality in `M` -/
abbrev ModalReduction (L : Logic _) (n : ℕ) (M : Modalities) := ∀ m, m.size = n → ∃ m' ∈ M, m ⤳[L] m'

lemma ModalReduction.of_allOfSize (h : ∀ m, m ∈ allOfSize n → ∃ m' ∈ M, m ⤳[L] m') : ModalReduction L n M := by
  intro m hm;
  apply h;
  exact allOfSize.iff_mem_eq_size.mpr hm;


/-- In `L`, every modality of size less than `n` is reduced to some modality in `M` -/
abbrev ModalReductionLe (L : Logic _) (n : ℕ) (M : Modalities) := ∀ m, m.size ≤ n → ∃ m' ∈ M, m ⤳[L] m'

lemma ModalReductionLe.of_allOfSizeLe (h : ∀ m, m ∈ allOfSizeLe n → ∃ m' ∈ M, m ⤳[L] m') : ModalReductionLe L n M := by
  intro m hm;
  apply h;
  exact allOfSizeLe.iff_mem_le_size.mpr hm;

lemma ModalReductionLe.of_cumulative (h : ∀ n' ≤ n, ModalReduction L n' M) : ModalReductionLe L n M := by
  intro m hm;
  apply h m.size ?_ m ?_ <;> tauto;

lemma ModalReductionLe.gt (h : ModalReductionLe L n M) (hn : n ≥ n'): ModalReductionLe L n' M := by
  intro m hm;
  apply h m (by omega);

lemma ModalReduction.of_le (h : ModalReductionLe L n M) : ModalReduction L n M := by
  intro m hm;
  apply h m (by omega);


macro "reduce_to " t:term : tactic => `(tactic| focus
  try simp only [add_empty_left, add_box_left, add_dia_left, add_neg_left];
  existsi $t;
  constructor;
  . set_option linter.unnecessarySimpa false in
    first | decide | simpa;
  . infer_instance;
)

section

variable [L.IsNormal]

lemma ModalReduction.reducible_0_of_mem (hM : (-) ∈ M) : ModalReduction L 0 M := by
  apply of_allOfSize;
  intro m hm;
  simp only [allOfSize.eq_zero, Finset.mem_singleton] at hm;
  subst hm;
  reduce_to (-);

lemma ModalReduction.reducible_1_of_mem (hNeg : (∼) ∈ M) (hBox : (□) ∈ M) (hDia : (◇) ∈ M) : ModalReduction L 1 M := by
  apply of_allOfSize;
  intro m hm;
  simp only [
    allOfSize, Finset.image_singleton, Finset.union_assoc, Finset.mem_union,
    Finset.mem_singleton
  ] at hm;
  rcases hm with (rfl | rfl | rfl);
  . reduce_to (∼);
  . reduce_to (□);
  . reduce_to (◇);

lemma ModalReduction.succ_max_of {M : Modalities} (M_ne : M.Nonempty)
  (hMR: ModalReductionLe L ((M.max_size M_ne) + 1) M)
  : ∀ n, ModalReductionLe L (n + (M.max_size M_ne) + 2) M := by
  generalize hk : (M.max_size M_ne) = k at hMR ⊢;
  intro n m hm;
  obtain ⟨m₁, m₂, hm₁, hm₂, rfl⟩ : ∃ m₁ m₂, m₁.size ≤ k + 1 ∧ m₂.size ≤ n + 1 ∧ m = m₁ + m₂ := split_le $ by omega;
  induction n generalizing m₂ with
  | zero =>
    obtain ⟨m₃, hm₃, _⟩ := hMR m₁ hm₁;
    obtain ⟨m₄, hm₄, _⟩ := hMR (m₃ + m₂) $ by
      have : m₃.size ≤ k := by simpa [hk] using @Modalities.lt_max_size_of_mem _ M M_ne hm₃;
      simp only [add_size];
      omega;
    use m₄;
    constructor;
    . assumption;
    . trans (m₃ + m₂);
      . apply translation_expand_right;
      . assumption;
  | succ n ih =>
    obtain ⟨m₃, m₄, hm₃, hm₄, rfl⟩ := split_right_le₁ hm₂;
    obtain ⟨m₅, hm₅, _⟩ := @ih m₃ hm₃ (by simp; omega);
    obtain ⟨m₆, hm₆, _⟩ := hMR (m₅ + m₄) $ by
      have : m₅.size ≤ k := by simpa [hk] using @Modalities.lt_max_size_of_mem _ M M_ne hm₅;
      simp only [add_size];
      omega;
    use m₆;
    constructor;
    . assumption;
    . trans (m₅ + m₄);
      . rw [show (m₁ + (m₃ + m₄)) = ((m₁ + m₃) + m₄) by simp];
        apply translation_expand_right;
      . assumption;

lemma ModalReductionLe.forall_of_reducibleLe_to_max (M_ne : M.Nonempty) (hMR: ModalReductionLe L ((M.max_size M_ne) + 1) M)
  : ∀ n, ModalReductionLe L n M := by
  intro n;
  by_cases hn : n ≤ (M.max_size M_ne) + 1;
  . apply ModalReductionLe.gt hMR;
    omega;
  . have : M.max_size M_ne + 2 ≤ n := by omega;
    apply ModalReductionLe.gt (n := n + M.max_size M_ne + 2) $ ModalReduction.succ_max_of M_ne hMR n;
    omega;

lemma ModalReduction.forall_of_reducibleLe_to_max (M_ne : M.Nonempty) (hMR: ModalReductionLe L ((M.max_size M_ne) + 1) M)
  : ∀ n, ModalReduction L n M := by
  intro n;
  apply ModalReduction.of_le;
  apply ModalReductionLe.forall_of_reducibleLe_to_max _ hMR;

theorem ModalReduction.forall_of_reducible_to_max (M_ne : M.Nonempty) (hMR: ∀ n' ≤ ((M.max_size M_ne) + 1), ModalReduction L n' M)
  : ∀ n, ModalReduction L n M := by
  intro n;
  apply forall_of_reducibleLe_to_max M_ne;
  apply ModalReductionLe.of_cumulative;
  exact hMR;

end


end

end LO.Modal
