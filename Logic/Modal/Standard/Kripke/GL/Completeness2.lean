import Logic.Modal.Standard.Deduction
import Logic.Modal.Standard.ConsistentTheory
import Logic.Modal.Standard.Kripke.Semantics
import Logic.Modal.Standard.Kripke.GL.Completeness

namespace LO.Modal.Standard

variable {α : Type u} [Inhabited α] [DecidableEq α]


namespace Formula

variable {p q r : Formula α}

@[elab_as_elim]
def cases_neg {C : Formula α → Sort w}
    (hfalsum : C ⊥)
    (hatom   : ∀ a : α, C (atom a))
    (hneg    : ∀ p : Formula α, C (~p))
    (himp    : ∀ (p q : Formula α), q ≠ ⊥ → C (p ⟶ q))
    (hbox    : ∀ (p : Formula α), C (□p))
    : (p : Formula α) → C p
  | ⊥       => hfalsum
  | atom a  => hatom a
  | □p      => hbox p
  | ~p      => hneg p
  | p ⟶ q  => if e : q = ⊥ then e ▸ hneg p else himp p q e

@[elab_as_elim]
def rec_neg {C : Formula α → Sort w}
    (hfalsum : C ⊥)
    (hatom   : ∀ a : α, C (atom a))
    (hneg    : ∀ p : Formula α, C (p) → C (~p))
    (himp    : ∀ (p q : Formula α), q ≠ ⊥ → C p → C q → C (p ⟶ q))
    (hbox    : ∀ (p : Formula α), C (p) → C (□p))
    : (p : Formula α) → C p
  | ⊥       => hfalsum
  | atom a  => hatom a
  | □p      => hbox p (rec_neg hfalsum hatom hneg himp hbox p)
  | ~p      => hneg p (rec_neg hfalsum hatom hneg himp hbox p)
  | p ⟶ q  =>
    if e : q = ⊥
    then e ▸ hneg p (rec_neg hfalsum hatom hneg himp hbox p)
    else himp p q e (rec_neg hfalsum hatom hneg himp hbox p) (rec_neg hfalsum hatom hneg himp hbox q)

section Complement

variable {p q: Formula α}

def negated : Formula α → Bool
  | ~_ => True
  | _  => False

@[simp]
lemma negated_def : (~p).negated := by simp [negated]

@[simp]
lemma negated_imp : (p ⟶ q).negated ↔ (q = ⊥) := by
  simp [negated, Formula.imp_eq];
  split;
  . simp_all [Formula.imp_eq]; rfl;
  . simp_all [Formula.imp_eq]; simpa;

lemma negated_iff : p.negated ↔ ∃ q, p = ~q := by
  induction p using Formula.cases_neg with
  | himp => simp [negated_imp];
  | _ => simp [negated]

lemma not_negated_iff : ¬p.negated ↔ ∀ q, p ≠ ~q := by
  induction p using Formula.cases_neg with
  | himp => simp [negated_imp];
  | _ => simp [negated]



lemma falsum_eq : (falsum : Formula α) = ⊥ := rfl

def complement : Formula α → Formula α
  | ~p => p
  | p  => ~p

prefix:80 "-" => complement

namespace complement

@[simp] lemma neg_def : -(~p) = p := by
  induction p using Formula.rec' <;> simp_all [complement]

@[simp] lemma bot_def : -(⊥ : Formula α) = ~(⊥) := by simp only [complement, imp_inj, and_true]; rfl;

@[simp] lemma box_def : -(□p) = ~(□p) := by simp only [complement, imp_inj, and_true]; rfl;

lemma imp_def₁ (hq : q ≠ ⊥) : -(p ⟶ q) = ~(p ⟶ q) := by
  simp only [complement];
  split;
  . rename_i h; simp [imp_eq, falsum_eq, hq] at h;
  . rfl;

lemma imp_def₂ (hq : q = ⊥) : -(p ⟶ q) = p := by
  subst_vars;
  apply neg_def;

lemma resort_box (h : -p = □q) : p = ~□q := by
  simp [complement] at h;
  split at h;
  . subst_vars; rfl;
  . contradiction;

lemma or (p : Formula α) : -p = ~p ∨ ∃ q, ~q = p := by
  induction p using Formula.cases_neg with
  | himp _ _ hn => simp [imp_def₁ hn];
  | hfalsum => simp;
  | hneg => simp;
  | hatom a => simp [complement];
  | hbox p => simp [complement]; rfl;

end complement

end Complement


@[elab_as_elim]
def rec_negated {C : Formula α → Sort w}
    (hfalsum : C ⊥)
    (hatom   : ∀ a : α, C (atom a))
    (hneg    : ∀ p : Formula α, C (p) → C (~p))
    (himp    : ∀ (p q : Formula α), ¬(p ⟶ q).negated → C p → C q → C (p ⟶ q))
    (hbox    : ∀ (p : Formula α), C (p) → C (□p))
    : (p : Formula α) → C p
  | ⊥       => hfalsum
  | atom a  => hatom a
  | □p      => hbox p (rec_negated hfalsum hatom hneg himp hbox p)
  | ~p      => hneg p (rec_negated hfalsum hatom hneg himp hbox p)
  | p ⟶ q  => by
    by_cases e : q = ⊥
    . exact e ▸ hneg p (rec_negated hfalsum hatom hneg himp hbox p)
    . refine himp p q ?_ (rec_negated hfalsum hatom hneg himp hbox p) (rec_negated hfalsum hatom hneg himp hbox q)
      . simpa [negated_imp]

end Formula



abbrev Formulae (α) := Finset $ Formula α

namespace Formulae

class SubformulaClosed (X : Formulae α) : Prop where
  imp_closed {p q} : p ⟶ q ∈ X → p ∈ X ∧ q ∈ X
  box_closed {p} : □p ∈ X → p ∈ X

namespace SubformulaClosed

instance {p : Formula α} : Formulae.SubformulaClosed (𝒮 p) where
  box_closed   := by aesop;
  imp_closed   := by aesop;

variable {p : Formula α} {X : Formulae α} [T_closed : X.SubformulaClosed]

lemma sub_mem_box (h : □p ∈ X) : p ∈ X := T_closed.box_closed h
lemma sub_mem_imp (h : p ⟶ q ∈ X) : p ∈ X ∧ q ∈ X := T_closed.imp_closed h
lemma sub_mem_imp₁ (h : p ⟶ q ∈ X) : p ∈ X := (T_closed.imp_closed h).1
lemma sub_mem_imp₂ (h : p ⟶ q ∈ X) : q ∈ X := (T_closed.imp_closed h).2

macro_rules | `(tactic| trivial) => `(tactic|
    first
    | apply sub_mem_box   $ by assumption
    | apply sub_mem_imp₁  $ by assumption
    | apply sub_mem_imp₂  $ by assumption
  )

end SubformulaClosed

def complementary (P : Formulae α) : Formulae α := P ∪ (P.image (Formula.complement))
postfix:80 "⁻" => Formulae.complementary

variable {P : Formulae α} {p : Formula α}

lemma complementary_mem : p ∈ P → p ∈ P⁻ := by simp [complementary]; tauto;

lemma complementary_mem_box [P.SubformulaClosed] : □p ∈ P⁻ → □p ∈ P := by
  simp [complementary];
  intro h;
  rcases h with (h | ⟨q, hq, eq⟩);
  . assumption;
  . replace eq := Formula.complement.resort_box eq;
    subst eq;
    trivial;

class ComplementaryClosed (X : Formulae α) (S : Formulae α) : Prop where
  subset : X ⊆ S⁻
  either : ∀ p ∈ S, p ∈ X ∨ -p ∈ X

def SubformulaeComplementaryClosed (X : Formulae α) (p : Formula α) : Prop := X.ComplementaryClosed (𝒮 p)

variable {S : Formulae α}

end Formulae



namespace Theory

variable {p : Formula α} {T : Theory α}

lemma not_mem_of_mem_neg (T_consis : (Λ)-Consistent T) (h : ~p ∈ T) : p ∉ T := by
  by_contra hC;
  have : [p, ~p] ⊬[Λ]! ⊥ := (Theory.def_consistent.mp T_consis) [p, ~p] (by simp_all);
  have : [p, ~p] ⊢[Λ]! ⊥ := System.bot_of_mem_either! (p := p) (Γ := [p, ~p]) (by simp) (by simp);
  contradiction;

lemma not_mem_neg_of_mem (T_consis : (Λ)-Consistent T) (h : p ∈ T) : ~p ∉ T := by
  by_contra hC;
  have : [p, ~p] ⊬[Λ]! ⊥ := (Theory.def_consistent.mp T_consis) [p, ~p] (by simp_all);
  have : [p, ~p] ⊢[Λ]! ⊥ := System.bot_of_mem_either! (p := p) (Γ := [p, ~p]) (by simp) (by simp);
  contradiction;

end Theory


section Encodable

variable {α : Type u} [Inhabited α] [Encodable α]

namespace Formula
open Sum

abbrev Node (α) := α ⊕ Fin 1 ⊕ Fin 1 ⊕ Fin 1

@[reducible]
def Edge (α) : Node α → Type
  | (inl _)             => Empty
  | (inr $ inl _)       => Empty
  | (inr $ inr $ inl _) => Unit
  | (inr $ inr $ inr _) => Bool

def toW : Formula α → WType (Edge α)
  | atom a  => ⟨inl a, Empty.elim⟩
  | falsum  => ⟨inr $ inl 0, Empty.elim⟩
  | box p   => ⟨inr $ inr $ inl 0, PUnit.rec p.toW⟩
  | imp p q => ⟨inr $ inr $ inr 0, Bool.rec p.toW q.toW⟩

def ofW : WType (Edge α) → Formula α
  | ⟨inl a, _⟩        => atom a
  | ⟨inr $ inl 0, _⟩ => falsum
  | ⟨inr $ inr $ inl 0, p⟩ => box (ofW $ p ())
  | ⟨inr $ inr $ inr 0, p⟩ => imp (ofW $ p false) (ofW $ p true)

lemma toW_ofW : ∀ (w : WType (Edge α)), toW (ofW w) = w
  | ⟨inl a, _⟩       => by simp [ofW, toW, Empty.eq_elim];
  | ⟨inr $ inl 0, _⟩ => by simp [ofW, toW, Empty.eq_elim];
  | ⟨inr $ inr $ inl 0, w⟩ => by
    simp [ofW, toW, toW_ofW (w ())];
  | ⟨inr $ inr $ inr 0, w⟩ => by
    simp [ofW, toW, toW_ofW (w false), toW_ofW (w true)];
    ext b; cases b <;> simp;

def equivW (α) : Formula α ≃ WType (Edge α) where
  toFun := toW
  invFun := ofW
  right_inv := toW_ofW
  left_inv := λ p => by induction p <;> simp_all [toW, ofW]

instance : (a : Node α) → Fintype (Edge α a)
  | (inl _)             => Fintype.ofIsEmpty
  | (inr $ inl _)       => Fintype.ofIsEmpty
  | (inr $ inr $ inl _) => Unit.fintype
  | (inr $ inr $ inr _) => Bool.fintype

instance : (a : Node α) → Primcodable (Edge α a)
  | (inl _)             => Primcodable.empty
  | (inr $ inl _)       => Primcodable.empty
  | (inr $ inr $ inl _) => Primcodable.unit
  | (inr $ inr $ inr _) => Primcodable.bool

instance : Encodable (Formula α) := Encodable.ofEquiv (WType (Edge α)) (equivW α)

end Formula

end Encodable


lemma complement_derive_bot
  {p : Formula α} [System (Formula α) S] {𝓢 : S} [System.ModusPonens 𝓢]
  (hp : 𝓢 ⊢! p) (hcp : 𝓢 ⊢! -p)
  : 𝓢 ⊢! ⊥ := by
  induction p using Formula.cases_neg with
  | hfalsum => assumption;
  | hatom a =>
    simp [Formula.complement] at hcp;
    exact hcp ⨀ hp;
  | hneg =>
    simp [Formula.complement] at hcp;
    exact hp ⨀ hcp;
  | himp p q h =>
    simp [Formula.complement.imp_def₁ h] at hcp;
    exact hcp ⨀ hp;
  | hbox p =>
    simp [Formula.complement] at hcp;
    exact hcp ⨀ hp;

lemma complement_derive_bot₂
  {Λ : DeductionParameter α} (hp : Λ ⊢! p) (hcp : Λ ⊢! -p) : Λ ⊢! ⊥ := complement_derive_bot hp hcp


lemma neg_complement_derive_bot
  {p : Formula α} [System (Formula α) S] {𝓢 : S} [System.ModusPonens 𝓢]
  (hp : 𝓢 ⊢! ~p) (hcp : 𝓢 ⊢! ~(-p))
  : 𝓢 ⊢! ⊥ := by
  induction p using Formula.cases_neg with
  | hfalsum =>
    simp [Formula.complement] at hcp;
    exact hcp ⨀ hp;
  | hatom a =>
    simp [Formula.complement] at hcp;
    exact hcp ⨀ hp;
  | hneg =>
    simp [Formula.complement] at hcp;
    exact hp ⨀ hcp;
  | himp p q h =>
    simp [Formula.complement.imp_def₁ h] at hcp;
    exact hcp ⨀ hp;
  | hbox p =>
    simp [Formula.complement] at hcp;
    exact hcp ⨀ hp;

namespace Theory

variable {Λ : DeductionParameter α}
variable {T : Theory α}

end Theory

namespace Formulae

open Theory

def Consistent (Λ : DeductionParameter α) (X : Formulae α) : Prop :=  X *⊬[Λ]! ⊥


variable {Λ : DeductionParameter α}
variable {X X₁ X₂ : Formulae α}

@[simp]
lemma iff_theory_consistent_formulae_consistent {X : Formulae α}
  : Theory.Consistent Λ X ↔ Formulae.Consistent Λ (↑X) := by simp [Consistent, Theory.Consistent]

lemma provable_iff_insert_neg_not_consistent : ↑X *⊢[Λ]! p ↔ ¬(Formulae.Consistent Λ (insert (~p) X)) := by
  rw [←iff_theory_consistent_formulae_consistent];
  simpa only [Finset.coe_insert, not_not] using Theory.provable_iff_insert_neg_not_consistent;

lemma neg_provable_iff_insert_not_consistent : ↑X *⊢[Λ]! ~p ↔ ¬(Formulae.Consistent Λ (insert (p) X)) := by
  rw [←iff_theory_consistent_formulae_consistent];
  simpa only [Finset.coe_insert, not_not] using Theory.neg_provable_iff_insert_not_consistent;

lemma unprovable_iff_singleton_neg_consistent : Λ ⊬! p ↔ Formulae.Consistent Λ ({~p}) := by
  rw [←iff_theory_consistent_formulae_consistent];
  simpa using Theory.unprovable_iff_singleton_neg_consistent;

lemma unprovable_iff_singleton_compl_consistent : Λ ⊬! p ↔ Formulae.Consistent Λ ({-p}) := by
  rcases (Formula.complement.or p) with (hp | ⟨q, rfl⟩);
  . rw [hp];
    convert Theory.unprovable_iff_singleton_neg_consistent (Λ := Λ) (p := p);
    simp;
  . simp only [Formula.complement];
    convert Theory.unprovable_iff_singleton_consistent (Λ := Λ) (p := q);
    simp;

lemma provable_iff_singleton_compl_inconsistent : Λ ⊢! p ↔ ¬(Formulae.Consistent Λ ({-p})) := by
  constructor;
  . contrapose; push_neg; apply unprovable_iff_singleton_compl_consistent.mpr;
  . contrapose; push_neg; apply unprovable_iff_singleton_compl_consistent.mp;

lemma intro_union_consistent
  (h : ∀ {Γ₁ Γ₂ : List (Formula α)}, (∀ p ∈ Γ₁, p ∈ X₁) → (∀ p ∈ Γ₂, p ∈ X₂) → Λ ⊬! ⋀Γ₁ ⋏ ⋀Γ₂ ⟶ ⊥)
  : Formulae.Consistent Λ (X₁ ∪ X₂) := by
  rw [←iff_theory_consistent_formulae_consistent];
  simpa using Theory.intro_union_consistent h;

@[simp]
lemma empty_conisistent [System.Consistent Λ] : Formulae.Consistent Λ ∅ := by
  rw [←iff_theory_consistent_formulae_consistent];
  convert Theory.emptyset_consistent (α := α);
  . simp;
  . assumption;

namespace exists_consistent_complementary_closed

open Classical

variable [Encodable α]

variable (Λ : DeductionParameter α)
variable {X : Formulae α}

noncomputable def next (p : Formula α) (X : Formulae α) : Formulae α :=
  if Formulae.Consistent Λ (insert p X) then insert p X else insert (-p) X

noncomputable def enum (X : Formulae α) : (List (Formula α)) → Formulae α
  | [] => X
  | q :: qs => next Λ q (enum X qs)
local notation:max t"[" l "]" => enum Λ t l

lemma next_consistent
  (X_consis : Formulae.Consistent Λ X) (p : Formula α)
  : Formulae.Consistent Λ (next Λ p X) := by
  simp only [next];
  split;
  . simpa;
  . rename_i h;
    have h₁ := Formulae.neg_provable_iff_insert_not_consistent (Λ := Λ) (X := X) (p := p) |>.mpr h;
    by_contra hC;
    have h₂ := Formulae.neg_provable_iff_insert_not_consistent (Λ := Λ) (X := X) (p := -p) |>.mpr hC;
    have := neg_complement_derive_bot h₁ h₂;
    contradiction;

lemma enum_consistent
  (X_consis : Formulae.Consistent Λ X)
  {l : List (Formula α)}
  : Formulae.Consistent Λ (X[l]) := by
  induction l with
  | nil => exact X_consis;
  | cons q qs ih =>
    simp only [enum];
    apply next_consistent;
    exact ih;

@[simp] lemma lindenbaum_enum_nil {X : Formulae α} : (X[[]]) = X := by simp [enum]

lemma lindenbaum_enum_subset_step {l : List (Formula α)} : (X[l]) ⊆ (X[(q :: l)]) := by
  simp [enum, next];
  split <;> simp;

lemma lindenbaum_enum_subset {l : List (Formula α)} : X ⊆ X[l] := by
  induction l with
  | nil => simp;
  | cons q qs ih => exact Set.Subset.trans ih $ by apply lindenbaum_enum_subset_step;

lemma lindenbaum_either {l : List (Formula α)} (hp : p ∈ l) : p ∈ X[l] ∨ -p ∈ X[l] := by
  induction l with
  | nil => simp_all;
  | cons q qs ih =>
    simp at hp;
    simp [enum, next];
    rcases hp with (rfl | hp);
    . split <;> simp [Finset.mem_insert];
    . split <;> {
        simp [Finset.mem_insert];
        rcases (ih hp) with (_ | _) <;> tauto;
      }

lemma lindenbaum_subset {l : List (Formula α)} {p : Formula α} (h : p ∈ X[l])
  : p ∈ X ∨ p ∈ l ∨ (∃ q ∈ l, -q = p)  := by
  induction l generalizing p with
  | nil => simp_all;
  | cons q qs ih =>
    simp_all [enum, next];
    split at h;
    . rcases Finset.mem_insert.mp h with (rfl | h)
      . tauto;
      . rcases ih h <;> tauto;
    . rcases Finset.mem_insert.mp h with (rfl | h)
      . tauto;
      . rcases ih h <;> tauto;

end exists_consistent_complementary_closed

open exists_consistent_complementary_closed in
lemma exists_consistent_complementary_closed
  (S : Formulae α)
  (h_sub : X ⊆ S⁻) (X_consis : Formulae.Consistent Λ X)
  : ∃ X', X ⊆ X' ∧ Formulae.Consistent Λ X' ∧ X'.ComplementaryClosed S := by
  use exists_consistent_complementary_closed.enum Λ X S.toList;
  refine ⟨?_, ?_, ?_, ?_⟩;
  . apply lindenbaum_enum_subset;
  . exact enum_consistent Λ X_consis;
  . simp [Formulae.complementary];
    intro p hp;
    simp only [Finset.mem_union, Finset.mem_image];
    rcases lindenbaum_subset Λ hp with (h | h | ⟨q, hq₁, hq₂⟩);
    . replace h := h_sub h;
      simp [complementary] at h;
      rcases h with (_ | ⟨a, b, rfl⟩);
      . tauto;
      . right; use a;
    . left; exact Finset.mem_toList.mp h;
    . right;
      use q;
      constructor;
      . exact Finset.mem_toList.mp hq₁;
      . assumption;
  . intro p hp;
    exact lindenbaum_either Λ (by simpa);


end Formulae


structure ComplementaryClosedConsistentFormulae (Λ) (S : Formulae α) where
  formulae : Formulae α
  consistent : formulae.Consistent Λ
  closed : formulae.ComplementaryClosed S
alias CCF := ComplementaryClosedConsistentFormulae

namespace ComplementaryClosedConsistentFormulae

open System
open Formula (atom)
variable {Λ : DeductionParameter α}

lemma lindenbaum
  (S : Formulae α)
  {X : Formulae α} (X_sub : X ⊆ S⁻) (X_consis : X.Consistent Λ)
  : ∃ X' : CCF Λ S, X ⊆ X'.formulae := by
  obtain ⟨X', ⟨X'_sub, x, b⟩⟩ := Formulae.exists_consistent_complementary_closed S X_sub X_consis;
  use ⟨X', (by assumption), (by assumption)⟩;

noncomputable instance [System.Consistent Λ] : Inhabited (CCF Λ S) := ⟨lindenbaum (X := ∅) S (by simp) (by simp) |>.choose⟩

variable {S} {X : CCF Λ S}

@[simp] lemma unprovable_falsum : X.formulae *⊬[Λ]! ⊥ := X.consistent

lemma mem_compl_of_not_mem (hs : q ∈ S) : q ∉ X.formulae → -q ∈ X.formulae := by
  intro h;
  rcases X.closed.either q (by assumption) with (h | h);
  . contradiction;
  . assumption;

lemma mem_of_not_mem_compl (hs : q ∈ S) : -q ∉ X.formulae → q ∈ X.formulae := by
  apply Not.imp_symm;
  exact mem_compl_of_not_mem hs;

lemma membership_iff (hq_sub : q ∈ S) : (q ∈ X.formulae) ↔ (X.formulae *⊢[Λ]! q) := by
  constructor;
  . intro h; exact Context.by_axm! h;
  . intro hp;
    suffices -q ∉ X.formulae by
      apply or_iff_not_imp_right.mp $ ?_;
      assumption;
      exact X.closed.either q hq_sub;
    by_contra hC;
    have hnp : X.formulae *⊢[Λ]! -q := Context.by_axm! hC;
    have := complement_derive_bot hp hnp;
    simpa;

lemma mem_verum (h : ⊤ ∈ S) : ⊤ ∈ X.formulae := by
  apply membership_iff h |>.mpr;
  exact verum!;

@[simp]
lemma mem_falsum : ⊥ ∉ X.formulae := Theory.not_mem_falsum_of_consistent X.consistent

lemma iff_mem_compl (hq_sub : q ∈ S) : (q ∈ X.formulae) ↔ (-q ∉ X.formulae) := by
  constructor;
  . intro hq; replace hq := membership_iff hq_sub |>.mp hq;
    by_contra hnq;
    induction q using Formula.cases_neg with
    | hfalsum => exact unprovable_falsum hq;
    | hatom a =>
      simp only [Formula.complement] at hnq;
      have : ↑X.formulae *⊢[Λ]! ~(atom a) := Context.by_axm! hnq;
      have : ↑X.formulae *⊢[Λ]! ⊥ := complement_derive_bot hq this;
      simpa;
    | hbox q =>
      simp only [Formula.complement] at hnq;
      have : ↑X.formulae *⊢[Λ]! ~(□q) := Context.by_axm! hnq;
      have : ↑X.formulae *⊢[Λ]! ⊥ := complement_derive_bot hq this;
      simpa;
    | hneg q =>
      simp only [Formula.complement] at hnq;
      have : ↑X.formulae *⊢[Λ]! q := Context.by_axm! hnq;
      have : ↑X.formulae *⊢[Λ]! ⊥ := complement_derive_bot hq this;
      simpa;
    | himp q r h =>
      simp only [Formula.complement.imp_def₁ h] at hnq;
      have : ↑X.formulae *⊢[Λ]! ~(q ⟶ r) := Context.by_axm! hnq;
      have : ↑X.formulae *⊢[Λ]! ⊥ := this ⨀ hq;
      simpa;
  . intro h; exact mem_of_not_mem_compl (by assumption) h;

lemma iff_mem_imp
  (hsub_qr : (q ⟶ r) ∈ S) (hsub_q : q ∈ S := by trivial)  (hsub_r : r ∈ S := by trivial)
  : ((q ⟶ r) ∈ X.formulae) ↔ (q ∈ X.formulae) → (-r ∉ X.formulae) := by
  constructor;
  . intro hqr hq;
    apply iff_mem_compl hsub_r |>.mp;
    replace hqr := membership_iff hsub_qr |>.mp hqr;
    replace hq := membership_iff hsub_q |>.mp hq;
    exact membership_iff hsub_r |>.mpr $ hqr ⨀ hq;
  . intro hqr; replace hqr := not_or_of_imp hqr
    rcases hqr with (hq | hr);
    . apply membership_iff hsub_qr |>.mpr;
      replace hq := mem_compl_of_not_mem hsub_q hq;
      induction q using Formula.cases_neg with
      | hfalsum => exact efq!;
      | hatom a => exact efq_of_neg! $ Context.by_axm! (by simpa using hq);
      | hbox q => exact efq_of_neg! $ Context.by_axm! (by simpa using hq);
      | hneg q =>
        simp only [Formula.complement.neg_def] at hq;
        exact efq_of_neg₂! $ Context.by_axm! hq;
      | himp q r h =>
        simp only [Formula.complement.imp_def₁ h] at hq;
        exact efq_of_neg! $ Context.by_axm! (by simpa using hq);
    . apply membership_iff (by assumption) |>.mpr;
      exact dhyp! $ membership_iff (by assumption) |>.mp $ iff_mem_compl (by assumption) |>.mpr hr;

lemma iff_not_mem_imp
  (hsub_qr : (q ⟶ r) ∈ S) (hsub_q : q ∈ S := by trivial)  (hsub_r : r ∈ S := by trivial)
  : ((q ⟶ r) ∉ X.formulae) ↔ (q ∈ X.formulae) ∧ (-r ∈ X.formulae) := by
  simpa using @iff_mem_imp α _ Λ S X q r hsub_qr hsub_q hsub_r |>.not;

end ComplementaryClosedConsistentFormulae

namespace Kripke

open Formula

variable {p q : Formula α}

abbrev GLCompleteFrame {p : Formula α} (h : 𝐆𝐋 ⊬! p) : Kripke.FiniteFrame where
  World := CCF 𝐆𝐋 (𝒮 p)
  World_finite := by
    simp;
    sorry;
  Rel X Y :=
    (∀ q ∈ □''⁻¹(𝒮 p), □q ∈ X.formulae → (q ∈ Y.formulae ∧ □q ∈ Y.formulae)) ∧
    (∃ r ∈ □''⁻¹(𝒮 p), □r ∉ X.formulae ∧ □r ∈ Y.formulae)

namespace GLCompleteFrame

variable {p : Formula α} {h : 𝐆𝐋 ⊬! p}

lemma irreflexive : Irreflexive (GLCompleteFrame h).Rel := by simp [Irreflexive];

lemma transitive : Transitive (GLCompleteFrame h).Rel := by
  simp;
  rintro X Y Z ⟨RXY, ⟨r, _, _, _⟩⟩ ⟨RYZ, _⟩;
  constructor;
  . rintro q hq₁ hq₂;
    exact RYZ q hq₁ $ RXY q hq₁ hq₂ |>.2;
  . use r;
    refine ⟨by assumption, by assumption, ?_⟩;
    exact RYZ r (by assumption) (by assumption) |>.2;

end GLCompleteFrame


abbrev GLCompleteModel (h : 𝐆𝐋 ⊬! p) : Kripke.Model α where
  Frame := GLCompleteFrame h
  Valuation X a := (atom a) ∈ X.formulae

open Formula.Kripke
open ComplementaryClosedConsistentFormulae

open System System.FiniteContext in
lemma contextual_nec (h : Γ ⊢[𝐆𝐋]! p) : (□'Γ) ⊢[𝐆𝐋]! (□p) :=
  provable_iff.mpr $ imp_trans''! collect_box_conj! $ imply_box_distribute'! $ provable_iff.mp h

open System System.FiniteContext in
lemma conjconj_provable!
  {Γ : List (Formula α)}
  (h : ∀ p, p ∈ Γ → Δ ⊢[𝐆𝐋]! p) : 𝐆𝐋 ⊢! ⋀Δ ⟶ ⋀Γ :=
  by induction Γ using List.induction_with_singleton with
  | hnil => exact dhyp! verum!;
  | hsingle => simp_all; exact provable_iff.mp h;
  | hcons p Γ hne ih => simp_all; exact imply_right_and! (provable_iff.mp h.1) ih;

open System System.FiniteContext in
lemma conjconj_provable'!
  {Γ : List (Formula α)}
  (h : ∀ p, p ∈ Γ → Δ ⊢[𝐆𝐋]! p) : Δ ⊢[𝐆𝐋]! ⋀Γ := provable_iff.mpr $ conjconj_provable! h

open System System.FiniteContext in
private lemma GL_truthlemma.lemma1
  {h : 𝐆𝐋 ⊬! p} {q : Formula α} (q_sub : □q ∈ 𝒮 p)
  {X : (GLCompleteModel h).World} (h_sub : □q ∉ X.formulae)
  : Formulae.Consistent 𝐆𝐋  ((X.formulae.prebox ∪ X.formulae.prebox.box) ∪ {□q, -q}) := by
  apply Formulae.intro_union_consistent;
  intro Γ₁ Γ₂ hΓ₁ hΓ₂;
  by_contra hC;
  have : 𝐆𝐋 ⊢! ⋀Γ₁ ⟶ ⋀Γ₂ ⟶ ⊥ := and_imply_iff_imply_imply'!.mp hC;
  have : Γ₁ ⊢[𝐆𝐋]! ⋀Γ₂ ⟶ ⊥ := provable_iff.mpr this;
  have : Γ₁ ⊢[𝐆𝐋]! (□q ⋏ -q) ⟶ ⊥ := imp_trans''! (by
    suffices Γ₁ ⊢[𝐆𝐋]! ⋀[□q, -q] ⟶ ⋀Γ₂ by simpa;
    apply conjconj_subset!;
    intro p hp;
    have := hΓ₂ p hp;
    simp at this;
    rcases this with (_ | _);
    . simp; left; assumption;
    . simp; right; assumption;
  ) this;
  have : Γ₁ ⊢[𝐆𝐋]! □q ⟶ -q ⟶ ⊥ := and_imply_iff_imply_imply'!.mp this;
  have : Γ₁ ⊢[𝐆𝐋]! □q ⟶ q := by
    rcases Formula.complement.or (p := q) with (hp | ⟨q, rfl⟩);
    . rw [hp] at this;
      exact imp_trans''! this dne!;
    . simpa [complement] using this;
  have : (□'Γ₁) ⊢[𝐆𝐋]! □(□q ⟶ q) := contextual_nec this;
  have : (□'Γ₁) ⊢[𝐆𝐋]! □q := axiomL! ⨀ this;
  have H₁ : 𝐆𝐋 ⊢! ⋀□'Γ₁ ⟶ □q := provable_iff.mp this;

  let Γ₁' := Γ₁.filter (λ r => r ∈ X.formulae.prebox);
  have hΓ₁' : ∀ r ∈ Γ₁', r ∈ X.formulae.prebox := by intro r hr; simpa using List.of_mem_filter hr;

  have H₂ : 𝐆𝐋 ⊢! ⋀□'Γ₁' ⟶ ⋀□'Γ₁ := conjconj_provable! $ by
    intro r hr; simp at hr;
    obtain ⟨r, hr, rfl⟩ := hr;
    have := hΓ₁ r hr; simp at this;
    rcases this with (_ | ⟨r, hr, rfl⟩);
    . apply by_axm!;
      simp [Γ₁'];
      sorry;
    . apply axiomFour'!;
      apply by_axm!;
      sorry;

  replace H₂ : 𝐆𝐋 ⊢! ⋀□'Γ₁' ⟶ ⋀□'Γ₁ := provable_iff.mp H₂;
  have := imp_trans''! H₂ H₁;

  have : X.formulae *⊢[𝐆𝐋]! □q := by
    apply Context.provable_iff.mpr;
    use (□'Γ₁');
    constructor;
    . intro q hq;
      simp at hq;
      obtain ⟨r, hr, rfl⟩ := hq;
      simpa using hΓ₁' r hr;
    . assumption;

  have : □q ∈ X.formulae := membership_iff q_sub |>.mpr this;
  contradiction;

open Formula.Subformulas in
macro_rules | `(tactic| trivial) => `(tactic|
    first
    | apply mem_self
    | apply mem_imp₁ $ by assumption
    | apply mem_imp₂ $ by assumption
    | apply mem_box  $ by assumption
  )

open System System.FiniteContext in
private lemma GL_truthlemma.lemma2
  {h : 𝐆𝐋 ⊬! p} {q : Formula α} (q_sub : □q ∈ 𝒮 p)
  {X : (GLCompleteModel h).World}
  : ((X.formulae.prebox ∪ X.formulae.prebox.box) ∪ {□q, -q}) ⊆ (𝒮 p)⁻ := by
  simp only [Formulae.complementary];
  intro r hr;
  simp [Finset.mem_union] at hr;
  rcases hr with (rfl | hp | ⟨r, hr, rfl⟩ | rfl);
  . apply Finset.mem_union.mpr;
    tauto;
  . have := X.closed.subset hp;
    have := Formulae.complementary_mem_box this;
    apply Finset.mem_union.mpr;
    left; trivial;
  . exact X.closed.subset hr;
  . apply Finset.mem_union.mpr;
    right; simp;
    use q;
    constructor;
    . trivial;
    . rfl;

open Formula MaximalConsistentTheory in
lemma GL_truthlemma₂
  {p : Formula α} (h : 𝐆𝐋 ⊬! p) {X : (GLCompleteModel h).World}
  {q : Formula α} (q_sub : q ∈ 𝒮 p) :
  Satisfies (GLCompleteModel h) X q ↔ q ∈ X.formulae := by
  induction q using Formula.rec' generalizing X with
  | hatom => simp [Satisfies];
  | hfalsum => simp [Satisfies];
  | himp q r ihq ihr =>
    constructor;
    . contrapose;
      intro h;
      simp [Satisfies];
      constructor;
      . apply ihq (by trivial) |>.mpr;
        exact iff_not_mem_imp q_sub |>.mp h |>.1;
      . apply ihr (by trivial) |>.not.mpr;
        have := iff_not_mem_imp q_sub |>.mp h |>.2;
        exact iff_mem_compl (by trivial) |>.not.mpr (by simpa using this);
    . contrapose;
      intro h; simp [Satisfies] at h;
      obtain ⟨hq, hr⟩ := h;
      replace hq := ihq (by trivial) |>.mp hq;
      replace hr := ihr (by trivial) |>.not.mp hr;
      apply iff_not_mem_imp q_sub |>.mpr;
      constructor;
      . assumption;
      . simpa using iff_mem_compl (by trivial) |>.not.mp (by simpa using hr);
  | hbox q ih =>
    constructor;
    . contrapose;
      intro h;
      obtain ⟨Y, hY₁⟩ := lindenbaum (S := 𝒮 p) (GL_truthlemma.lemma2 q_sub) (GL_truthlemma.lemma1 (h_sub := h) q_sub);
      simp only [Finset.union_subset_iff] at hY₁;
      have hY₁₁ : □q ∈ Y.formulae := by apply hY₁.2; simp;
      have hY₁₂ : -q ∈ Y.formulae := by apply hY₁.2; simp;
      simp [Satisfies];
      use Y;
      constructor;
      . intro r _ hr_sub;
        constructor;
        . apply hY₁.1.1; simpa;
        . apply hY₁.1.2; simpa;
      . use q;
        refine ⟨q_sub, h, hY₁₁, ?_⟩;
        . apply ih (by trivial) |>.not.mpr;
          exact iff_mem_compl (by trivial) |>.not.mpr (by simpa);
    . intro h Y RXY;
      apply ih (by trivial) |>.mpr;
      simp [Frame.Rel'] at RXY;
      refine RXY.1 q ?_ h |>.1;
      assumption;

private lemma GL_completeAux : TransitiveIrreflexiveFrameClass.{u}ꟳ# ⊧ p → 𝐆𝐋 ⊢! p := by
  contrapose;
  intro h;
  apply exists_finite_frame.mpr;
  use (GLCompleteFrame h);
  constructor;
  . exact ⟨GLCompleteFrame.transitive, GLCompleteFrame.irreflexive⟩;
  . simp [Formula.Kripke.ValidOnFrame, Formula.Kripke.ValidOnModel];
    obtain ⟨X, hX₁⟩ := lindenbaum (Λ := 𝐆𝐋) (S := 𝒮 p) (X := {-p})
      (by
        simp [Formulae.complementary];
        right; use p; constructor <;> simp;
      )
      (Formulae.unprovable_iff_singleton_compl_consistent.mp h);
    use (GLCompleteModel h).Valuation, X;
    apply GL_truthlemma₂ (by simpa) (by trivial) |>.not.mpr;
    exact iff_mem_compl (by trivial) |>.not.mpr $ by
      simp;
      apply hX₁;
      tauto;

instance GL_complete₂ : Complete (𝐆𝐋 : DeductionParameter α) TransitiveIrreflexiveFrameClass.{u}ꟳ# := ⟨GL_completeAux⟩

instance : FiniteFrameProperty (α := α) 𝐆𝐋 TransitiveIrreflexiveFrameClass where

end Kripke

end LO.Modal.Standard
