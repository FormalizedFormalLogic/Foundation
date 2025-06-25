import Foundation.Modal.Hilbert.WellKnown
import Foundation.Modal.Logic.Extension

namespace LO.Modal

@[match_pattern]
inductive Modality : Type
  | empty : Modality
  | box : Modality → Modality
  | dia : Modality → Modality
  | neg : Modality → Modality
deriving DecidableEq, BEq

namespace Modality

variable {m m₁ m₂ : Modality}

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
notation:max "□" => pbox

/-- pure diamond -/
abbrev pdia : Modality := ◇-
notation:max "◇" => pdia

/-- pure negation -/
abbrev pneg : Modality := ∼-
notation:max "∼" => pneg

#eval □◇◇


def add : Modality → Modality → Modality
  | - ,  m₂ => m₂
  | □m₁, m₂ => □(m₁.add m₂)
  | ◇m₁, m₂ => ◇(m₁.add m₂)
  | ∼m₁, m₂ => ∼(m₁.add m₂)
instance : Add Modality := ⟨Modality.add⟩

@[simp] lemma add_box : □m₁ + m₂ = □(m₁ + m₂) := rfl
@[simp] lemma add_dia : ◇m₁ + m₂ = ◇(m₁ + m₂) := rfl
@[simp] lemma add_neg : ∼m₁ + m₂ = ∼(m₁ + m₂) := rfl

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

instance : DecidablePred (Modality.size · = n) := inferInstance

@[simp] lemma iff_empty_size_zero : m.size = 0 ↔ m = - := by
  constructor;
  . match m with
    | -  => tauto;
    | □_
    | ◇_
    | ∼_ => simp;
  . rintro rfl; simp;

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

open Formula

variable {m : Modality} {L : Logic} [L.IsNormal] {φ ψ : Formula ℕ} {s : Substitution ℕ}

lemma modality_congruence (h : φ ⭤ ψ ∈ L) : (m φ) ⭤ (m ψ) ∈ L := by
  induction m with
  | empty => simpa;
  | box m' ih => apply L.box_congruence ih;
  | dia m' ih => apply L.dia_congruence ih;
  | neg m' ih => apply L.neg_congruence ih;

lemma E_subst_attachmodality : ((m φ)⟦s⟧) ⭤ (m (φ⟦s⟧)) ∈ L := by
  induction m with
  | empty => simp;
  | box m' ih => apply L.box_congruence ih;
  | dia m' ih => apply L.dia_congruence ih;
  | neg m' ih => apply L.neg_congruence ih;

lemma C_subst_attachmodality_mp : ((m φ)⟦s⟧) ➝ (m (φ⟦s⟧)) ∈ L := by
  apply L.C_of_E_mp E_subst_attachmodality;

lemma C_subst_attachmodality_mpr : (m (φ⟦s⟧)) ➝ ((m φ)⟦s⟧) ∈ L := by
  apply L.C_of_E_mpr E_subst_attachmodality;

lemma attachmodality_subst_of_subst_attachmodality : (m φ)⟦s⟧ ∈ L → m (φ⟦s⟧) ∈ L := L.mdp C_subst_attachmodality_mp

lemma subst_attachmodality_of_attachmodality_subst : m (φ⟦s⟧) ∈ L → (m φ)⟦s⟧ ∈ L := L.mdp C_subst_attachmodality_mpr

end Logic


namespace Modality

open Formula

variable {L : Logic} [L.IsNormal] {m₁ m₂ : Modality}

class Translation (L : Logic) (m₁ m₂ : Modality) where
  translate : ∀ a, (m₁ (.atom a)) ➝ (m₂ (.atom a)) ∈ L

notation:90 M₁ " ⤳[" L "] " M₂ => Translation L M₁ M₂

instance : IsRefl _ (· ⤳[L] ·) := ⟨by
  intro M;
  constructor;
  intro a;
  apply L.of_mem_K;
  simp;
⟩

instance : IsTrans _ (· ⤳[L] ·) where
  trans M₁ M₂ M₃ := by
    intro T₁₂ T₂₃;
    constructor;
    intro a;
    exact L.C_trans (T₁₂.translate a) (T₂₃.translate a);

class Equivalence (L : Logic) (M₁ M₂ : Modality) where
  equivalent : ∀ a, (M₁ (.atom a)) ⭤ (M₂ (.atom a)) ∈ L

notation M₁ " ≅[" L "] " M₂ => Equivalence L M₁ M₂

instance [m₁ ≅[L] m₂] : m₁ ⤳[L] m₂ := ⟨fun a ↦ L.C_of_E_mp $ Equivalence.equivalent a⟩
instance [m₁ ≅[L] m₂] : m₂ ⤳[L] m₁ := ⟨fun a ↦ L.C_of_E_mpr $ Equivalence.equivalent a⟩

lemma iff_equivalence_bi_translate : (m₁ ≅[L] m₂) ↔ (m₁ ⤳[L] m₂) ∧ (m₂ ⤳[L] m₁) := by
  constructor;
  . intro eq;
    constructor <;> infer_instance;
  . intro ⟨T₁₂, T₂₁⟩;
    constructor;
    intro a;
    apply L.E_of_C_of_C;
    . exact T₁₂.translate a;
    . exact T₂₁.translate a;

instance [m₁ ⤳[L] m₂] [m₂ ⤳[L] m₁] : m₁ ≅[L] m₂ := by
  apply iff_equivalence_bi_translate.mpr;
  constructor <;> infer_instance;

instance : IsSymm _ (· ≅[L] ·) := ⟨by
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


lemma Translation.translate_fml [m₁ ⤳[L] m₂] (φ : Formula _) : m₁ φ ➝ m₂ φ ∈ L := by
  let s : Substitution ℕ := λ a => if a = 0 then φ else (.atom a);
  apply L.C_replace $ L.subst (Translation.translate (L := L) (m₁ := m₁) (m₂ := m₂) 0) (s := s);
  . simpa [s] using L.C_subst_attachmodality_mpr (s := s) (φ := (.atom 0));
  . simpa [s] using L.C_subst_attachmodality_mp (s := s) (φ := (.atom 0));

def translation_of_axiomInstance {a : ℕ} (h : (m₁ a) ➝ (m₂ a) ∈ L) : m₁ ⤳[L] m₂ := ⟨by
  intro b;
  let s : Substitution ℕ := λ c => if c = a then b else c;
  apply L.C_replace $ L.subst h (s := s);
  . simpa [s] using L.C_subst_attachmodality_mpr (s := s) (φ := (.atom a));
  . simpa [s] using L.C_subst_attachmodality_mp (s := s) (φ := (.atom a));
⟩

lemma translation_expand_right {L : Logic} [L.IsNormal] (m₁ m₂ m) [m₁ ⤳[L] m₂] : (m₁ + m) ⤳[L] (m₂ + m) := by
  constructor;
  intro a;
  simpa using Translation.translate_fml (L := L) (m₁ := m₁) (m₂ := m₂) $ m (.atom a);

lemma translation_expand_left {L : Logic} [L.IsNormal] (m₁ m₂ m) [m₁ ⤳[L] m₂] [m ⤳[L] (-)] : (m + m₁) ⤳[L] (m₂) := by
  constructor;
  intro a;
  have H₁ : (m + m₁) (atom a) ➝ m₁ (atom a) ∈ L := by simpa using Translation.translate_fml (m₁ := m) (m₂ := (-)) (m₁ (.atom a));
  have H₂ : m₁ (atom a) ➝ m₂ (atom a) ∈ L := Translation.translate_fml (.atom a);
  exact L.C_trans H₁ H₂;

lemma Equivalence.equivalent_fml [m₁ ≅[L] m₂] (φ : Formula _) : m₁ φ ⭤ m₂ φ ∈ L := by
  apply L.E_of_C_of_C <;> apply Translation.translate_fml;

def equivalence_of_axiomInstance {a : ℕ} (h : (m₁ a) ⭤ (m₂ a) ∈ L) : m₁ ≅[L] m₂ := by
  apply iff_equivalence_bi_translate.mpr;
  constructor;
  . apply translation_of_axiomInstance (a := a);
    apply L.C_of_E_mp h;
  . apply translation_of_axiomInstance (a := a);
    apply L.C_of_E_mpr h;

lemma equivalence_expand_right {L : Logic} [L.IsNormal] (m₁ m₂ m) [m₁ ≅[L] m₂] : (m₁ + m) ≅[L] (m₂ + m) := by
  apply iff_equivalence_bi_translate.mpr;
  constructor <;> apply translation_expand_right;

lemma equivalence_expand_left {L : Logic} [L.IsNormal] (m₁ m₂ m) [m₁ ≅[L] m₂] : (m + m₁) ≅[L] (m + m₂) := by
  constructor;
  intro a;
  induction m with
  | empty    => apply Equivalence.equivalent_fml (m₁ := m₁) (m₂ := m₂);
  | box m ih => apply L.box_congruence ih;
  | dia m ih => apply L.dia_congruence ih;
  | neg m ih => apply L.neg_congruence ih;

end Modality


namespace Logic

open Modality
open Formula


section

open LO.Entailment

variable {L : Logic} [L.IsNormal] {m : Modality}

instance : m ⤳[L] m := refl m

instance : (□) ≅[L] (∼◇∼) := by
  constructor;
  intro a;
  apply L.of_mem_K;
  simp;

instance : (◇) ≅[L] (∼□∼) := by
  constructor;
  intro a;
  apply L.of_mem_K;
  simp;

instance : (∼∼) ≅[L] (-) := by
  apply equivalence_of_axiomInstance (a := 0);
  apply L.of_mem_K;
  apply E!_symm;
  simp;

instance : (□∼) ≅[L] (∼◇) := by
  apply equivalence_of_axiomInstance (a := 0);
  apply L.of_mem_K;
  -- TODO: extract ` □∼p ⭤ ∼◇p`
  apply E!_intro;
  . simp;
  . apply C!_trans (ψ := ∼∼□(∼(.atom 0)));
    . apply contra!; simp;
    . simp;

instance : (◇∼) ≅[L] (∼□) := by
  apply equivalence_of_axiomInstance (a := 0);
  apply L.of_mem_K;
  -- TODO: extract `◇∼p ⭤ ∼□p`
  apply E!_intro;
  . apply C!_trans (ψ := ∼□(∼∼(.atom 0)));
    . simp;
    . simp;
  . apply C!_trans (ψ := ∼∼◇(∼(.atom 0)));
    . apply contra!;
      simp;
    . simp;

end

section

variable {H : Hilbert ℕ} [H.HasK] {m : outParam (Modality)}

instance [H.HasT] : (□) ⤳[H.logic] (-) :=
  translation_of_axiomInstance (a := Hilbert.HasT.p H) $ by simp;

instance [H.HasFour] : (□) ⤳[H.logic] (□□) :=
  translation_of_axiomInstance (a := Hilbert.HasFour.p (H := H)) $ by simp

instance [H.HasTc] : (m) ⤳[H.logic] (□m) :=
  translation_of_axiomInstance (a := Hilbert.HasTc.p H) $ by simp;

instance [H.HasB] : (m) ⤳[H.logic] (□◇m) :=
  translation_of_axiomInstance (a := Hilbert.HasB.p (H := H)) $ by simp;

instance [H.HasD] : (□m) ⤳[H.logic] (◇m) :=
  translation_of_axiomInstance (a := Hilbert.HasD.p (H := H)) $ by simp;

instance [H.HasFive] : (◇m) ⤳[H.logic] (□◇m) :=
  translation_of_axiomInstance (a := Hilbert.HasFive.p (H := H)) $ by simp;

end

instance : (□-) ⤳[Logic.S4] (-) := inferInstance

instance : (□-) ≅[Logic.Triv] (-) := inferInstance


end Logic


abbrev Modalities := Finset Modality

namespace Modalities

open Modality

variable {n : ℕ} {m : Modality}

def more (M : Modalities) : Modalities :=
  M.image (λ m => □m) ∪
  M.image (λ m => ◇m) ∪
  M.image (λ m => ∼m)

#eval more ({-, ∼, □, ◇})

def max_size (M : Modalities) (hM : M.Nonempty := by decide) := M.image (λ m => m.size) |>.max' $ Finset.image_nonempty.mpr hM

#eval max_size ({-, ∼, □, □, □, □□□□□□□, □, ◇})

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

instance : DecidablePred (· ∈ allOfSize n) := by
  simp only [allOfSize.iff_mem_eq_size];
  infer_instance;

#eval allOfSize 2
#eval □ ∈ allOfSize 1

lemma allOfSize.eq_succ_left (h : m ∈ allOfSize (n + 1)) : ∃ m' ∈ allOfSize n, m = ∼m' ∨ m = □m' ∨ m = ◇m' := by
  simp only [allOfSize, Finset.union_assoc, Finset.mem_union, Finset.mem_image] at h;
  rcases h with (⟨m, ⟨hm', rfl⟩⟩ | ⟨m, ⟨hm, rfl⟩⟩ | ⟨m, ⟨hm, rfl⟩⟩) <;>
  . use m;
    tauto;

lemma allOfSize.eq_succ_right (h : m ∈ allOfSize (n + 1)) : ∃ m' ∈ allOfSize n, m = (m' + ∼) ∨ m = (m' + □) ∨ m = (m' + ◇) := by
  induction n generalizing m with
  | zero =>
    use (-);
    simp only [
      allOfSize, Finset.image_singleton, Finset.union_assoc, Finset.mem_union,
      Finset.mem_singleton
    ] at h;
    constructor;
    . tauto;
    . rcases h with (rfl | rfl | rfl) <;> tauto;
  | succ n ih =>
    obtain ⟨m, hm, (rfl | rfl | rfl)⟩ := allOfSize.eq_succ_left h;
    . rcases @ih _ hm with ⟨m', hm', (rfl | rfl | rfl)⟩ <;>
      . use (∼m');
        constructor;
        . apply allOfSize.iff_mem_eq_size.mpr
          simpa using allOfSize.iff_mem_eq_size.mp hm';
        . tauto;
    . rcases @ih _ hm with ⟨m', hm', (rfl | rfl | rfl)⟩ <;>
      . use (□m');
        constructor;
        . apply allOfSize.iff_mem_eq_size.mpr
          simpa using allOfSize.iff_mem_eq_size.mp hm';
        . tauto;
    . rcases @ih _ hm with ⟨m', hm', (rfl | rfl | rfl)⟩ <;>
      . use (◇m');
        constructor;
        . apply allOfSize.iff_mem_eq_size.mpr
          simpa using allOfSize.iff_mem_eq_size.mp hm';
        . tauto;

def allOfSizeLt : Nat → Modalities
  | 0 => allOfSize 0
  | n + 1 => allOfSizeLt n ∪ allOfSize (n + 1)

#eval allOfSizeLt 3

lemma allOfSizeLt.iff_mem_le_size : m ∈ allOfSizeLt n ↔ m.size ≤ n := by
  induction n with
  | zero => simp [allOfSizeLt];
  | succ n ih =>
    simp only [allOfSizeLt, Finset.mem_union];
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

instance : DecidablePred (· ∈ allOfSizeLt n) := by
  simp only [allOfSizeLt.iff_mem_le_size];
  infer_instance;

#eval □◇ ∈ allOfSizeLt 2


/-
def posOfSize : ℕ → List Modality
  | 0 => [-]
  | n + 1 =>
    (posOfSize n).map (λ m => □m) ++
    (posOfSize n).map (λ m => ◇m)

#eval posOfSize 3

lemma posOfSize.eq_size_of_mem : ∀ M ∈ posOfSize n, M.size = n := by
  induction n with
  | zero => simp [posOfSize];
  | succ n ih =>
    simp only [posOfSize, List.append_assoc, List.mem_append, List.mem_map];
    rintro m (⟨m, ⟨hm, rfl⟩⟩ | ⟨m, ⟨hm, rfl⟩⟩) <;> simp [ih m hm];

lemma posOfSize.pos_of_mem : ∀ M ∈ posOfSize n, M.polarity = .pos := by
  induction n with
  | zero => simp [posOfSize];
  | succ n ih =>
    simp only [posOfSize, List.append_assoc, List.mem_append, List.mem_map];
    rintro m (⟨m, ⟨hm, rfl⟩⟩ | ⟨M, ⟨hm, rfl⟩⟩) <;> simp [ih _ hm];
-/

/-
lemma posOfSize.iff_mem_eq_size : M ∈ posOfSize n ↔ M.size = n ∧ M.polarity = .pos := by
  constructor;
  . intro h;
    constructor;
    . exact posOfSize.eq_size_of_mem M h;
    . exact posOfSize.pos_of_mem M h;
  . induction n generalizing M with
    | zero => simp [posOfSize]; tauto;
    | succ n ih =>
      simp only [posOfSize, List.append_assoc, List.mem_append, List.mem_map];
      rintro ⟨hm₁, hm₂⟩;
      match M with
      | -  => contradiction;
      | □M => simp_all [posOfSize];
      | ◇M => simp_all [posOfSize];
      | ∼M =>
        sorry;
-/

end Modalities




end LO.Modal
