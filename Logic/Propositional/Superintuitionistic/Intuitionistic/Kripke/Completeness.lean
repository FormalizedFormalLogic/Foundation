import Logic.Propositional.Superintuitionistic.Intuitionistic.Deduction
import Logic.Propositional.Superintuitionistic.Intuitionistic.Kripke.Semantics
import Logic.Propositional.Superintuitionistic.Intuitionistic.Kripke.Soundness

/-!
  # Completeness for Kripke Semantics of Intuitionistic Propositional Logic

  ## References
  - Huayu Guo, Dongheng Chen, Bruno Bentzen, "Verified completeness in Henkin-style for intuitionistic propositional logic"
    - paper: https://arxiv.org/abs/2310.01916
    - inplements: https://github.com/bbentzen/ipl

  ## Theorems
  - `completes`: Deduction is complete to Kripke Semantics.
  - `disjunctive`: Deduction is disjunctive (via Kripke completeness).
-/

namespace LO.Propositional.Superintuitionistic

open Formula Theory
open Hilbert
open Set

namespace Theory

def Closed (Γ : Theory β) := ∀ {p}, (Γ ⊢ⁱ! p) → p ∈ Γ

def Disjunctive (Γ : Theory β) := ∀ {p q}, p ⋎ q ∈ Γ → p ∈ Γ ∨ q ∈ Γ

class Prime (T : Theory β) where
  consistent : T.Consistent 𝐄𝐅𝐐
  closed : Closed T
  disjunctive : Disjunctive T

end Theory

structure PrimeTheory (β : Type*) where
  theory : Theory β
  prime : Prime theory

namespace PrimeTheory

@[simp] def membership (p : Formula β) (Ω : PrimeTheory β) := p ∈ Ω.theory
instance : Membership (Formula β) (PrimeTheory β) := ⟨membership⟩

@[simp] def subset (Ω₁ Ω₂ : PrimeTheory β) := Ω₁.theory ⊆ Ω₂.theory
instance : HasSubset (PrimeTheory β) := ⟨subset⟩

instance : CoeSort (PrimeTheory β) (Theory β) := ⟨λ Ω => Ω.theory⟩

variable (Ω : PrimeTheory β)

def consistent : Ω.theory.Consistent 𝐄𝐅𝐐 := Ω.prime.consistent

def closed : Closed Ω.theory := Ω.prime.closed

def closed' {p : Formula β} : (Ω.theory ⊢ⁱ! p) → p ∈ Ω := Ω.closed

def disjunctive : Theory.Disjunctive Ω.theory := Ω.prime.disjunctive

def disjunctive' {p q : Formula β} : (p ⋎ q ∈ Ω) → (p ∈ Ω) ∨ (q ∈ Ω) := Ω.disjunctive

variable {Ω}

@[simp] lemma undeducible_falsum : Ω.theory ⊬ⁱ! ⊥ := Ω.consistent

end PrimeTheory

namespace Intuitionistic.Kripke

section

open Encodable
open Classical

variable {Γ : Theory β} {p : Formula β}
variable [Encodable β]

@[simp]
def insertFamily (Γ : Theory β) (p : Formula β) : ℕ → Theory β
  | 0 => Γ
  | n + 1 =>
    match (decode n) with
    | some (q : Formula β) =>
      match q with
      | q₁ ⋎ q₂ =>
        if (insertFamily Γ p n) ⊢ⁱ! (q₁ ⋎ q₂)
          then if (insert q₁ (insertFamily Γ p n)) ⊢ⁱ! p
            then insert q₂ (insertFamily Γ p n)
            else insert q₁ (insertFamily Γ p n)
          else (insertFamily Γ p n)
      | _ => insertFamily Γ p n
    | _ => insertFamily Γ p n
notation Γ "[" p "," i "]ⁱ" => insertFamily Γ p i

lemma insertFamily_mono (h : k ≤ m) : Γ[p, k]ⁱ ⊆ Γ[p, m]ⁱ := by
  induction h with
  | refl => rfl;
  | step h ih =>
    simp;
    split;
    . split;
      . split;
        . split;
          apply Set.Subset.trans ih; simp;
          apply Set.Subset.trans ih; simp;
        . simpa;
      . simpa;
    . simpa;

lemma insertFamily_subset_self : Γ ⊆ Γ[p, k]ⁱ := insertFamily_mono (zero_le k)

lemma insertFamily_undeducible (h : Γ ⊬ⁱ! p) : ∀ {i}, Γ[p, i]ⁱ ⊬ⁱ! p := by
  intro i;
  induction i with
  | zero => simpa using h
  | succ i ih =>
    simp;
    cases @decode (Formula β) _ i with
    | none => simpa using ih
    | some q =>
      simp;
      split;
      . split;
        . split;
          . rename_i q₁ q₂ hq₁₂ hq₁;
            by_contra hq₂;
            replace hq₁ : Γ[p,i]ⁱ ⊢ⁱ! q₁ ⟶ p := dtr'! (by simpa using hq₁);
            replace hq₂ : Γ[p,i]ⁱ ⊢ⁱ! q₂ ⟶ p := dtr'! (by simpa [System.not_unprovable_iff_provable] using hq₂);
            have : Γ[p,i]ⁱ ⊢ⁱ! p := disj₃'! hq₁ hq₂ hq₁₂;
            contradiction;
          . simp at*; assumption
        . simp at*; assumption
      . simpa using ih

lemma insertFamily_deducible : (Γ[p, i]ⁱ ⊢ⁱ! p) → (Γ ⊢ⁱ! p) := by
  contrapose;
  intro h;
  exact insertFamily_undeducible h

@[simp]
def iUnionInsertFamily (Γ : Theory β) (p : Formula β) : Theory β := ⋃ i, Γ[p, i]ⁱ
notation Γ "[" p "]ⁱ" => iUnionInsertFamily Γ p

lemma exists_insertFamily_deducible_of_iUnionInsertFamily_deducible : (Γ[p]ⁱ ⊢ⁱ! q) → (∃ k, Γ[p, k]ⁱ ⊢ⁱ! q) := by
  generalize e : Γ[p]ⁱ = Γ';
  intro h;
  induction h.some with
  | axm h₁ =>
    subst e;
    obtain ⟨m, hm⟩ := by simpa using h₁;
    existsi m;
    exact axm! hm;
  | modusPonens h₁ h₂ ih₁ ih₂ =>
    obtain ⟨m₁, hm₁⟩ := ih₁ ⟨h₁⟩;
    obtain ⟨m₂, hm₂⟩ := ih₂ ⟨h₂⟩;
    by_cases hm : m₁ ≤ m₂;
    case pos =>
      existsi m₂;
      exact (weakening! (insertFamily_mono hm) hm₁) ⨀ hm₂;
    case neg =>
      replace hm : m₂ ≤ m₁ := le_of_not_le hm;
      existsi m₁;
      exact hm₁ ⨀ (weakening! (insertFamily_mono hm) hm₂);
  | eaxm ih =>
    existsi 0;
    obtain ⟨q, hq⟩ := ih;
    subst hq;
    apply efq!;
  | _ =>
    existsi 0;
    try first
    | apply verum!;
    | apply imply₁!;
    | apply imply₂!;
    | apply conj₁!;
    | apply conj₂!;
    | apply conj₃!;
    | apply disj₁!;
    | apply disj₂!;
    | apply disj₃!;

@[simp]
def primeFamily (Γ : Theory β) (p : Formula β) : ℕ → Theory β
  | 0 => Γ
  | n + 1 => ⋃ i, (primeFamily Γ p n)[p, i]ⁱ
notation Γ "[" p "," i "]ᴾ" => primeFamily Γ p i

lemma primeFamily_mono (h : k ≤ m) : Γ[p, k]ᴾ ⊆ Γ[p, m]ᴾ := by
  induction h with
  | refl => rfl;
  | @step m _ ih =>
    apply Subset.trans ih;
    nth_rw 1 [(show Γ[p, m]ᴾ = (Γ[p, m]ᴾ)[p, 0]ⁱ by rfl)];
    apply subset_iUnion;

lemma exists_insertFamily_deducible_of_primeFamily_deducible (h : Γ[p, k + 1]ᴾ ⊢ⁱ! q) : ∃ m, Γ[p, k]ᴾ[p, m]ⁱ ⊢ⁱ! q := by
  obtain ⟨m, hm⟩ := exists_insertFamily_deducible_of_iUnionInsertFamily_deducible h;
  existsi m;
  simpa;

lemma primeFamily_deducible : (Γ[p, k]ᴾ ⊢ⁱ! p) → (Γ ⊢ⁱ! p) := by
  induction k with
  | zero => aesop;
  | succ k ih =>
    intro h;
    obtain ⟨m, hm⟩ := exists_insertFamily_deducible_of_primeFamily_deducible h;
    exact ih (insertFamily_deducible hm);

lemma primeFamily_undeducible : Γ ⊬ⁱ! p → ∀ {k}, Γ[p, k]ᴾ ⊬ⁱ! p := by
  contrapose;
  intro h;
  obtain ⟨k, (hk : Γ[p, k]ᴾ ⊢ⁱ! p)⟩ := by simpa [System.not_unprovable_iff_provable] using h;
  simpa [System.not_unprovable_iff_provable] using primeFamily_deducible hk;

@[simp]
def iUnionPrimeFamily (Γ : Theory β) (p : Formula β) : Theory β := ⋃ i, Γ[p, i]ᴾ
notation Γ "[" p "]ᴾ" => iUnionPrimeFamily Γ p

lemma mem_iUnionPrimeFamily (h : q ∈ (Γ[p, m]ᴾ)[p, k]ⁱ) : q ∈ Γ[p]ᴾ := by
  simp;
  existsi (m + 1);
  simp;
  existsi k;
  simpa;

lemma iUnionPrimeFamily_disjunctive : Disjunctive (Γ[p]ᴾ) := by
  intros q₁ q₂ hq;
  let k := encode (q₁ ⋎ q₂);
  obtain ⟨m, hm⟩ := by simpa using hq;
  have hm₀ : (Γ[p, m]ᴾ)[p, 0]ⁱ ⊢ⁱ! q₁ ⋎ q₂ := by simpa using axm! hm;
  have hmₖ : (Γ[p, m]ᴾ)[p, k]ⁱ ⊢ⁱ! q₁ ⋎ q₂ := weakening! (insertFamily_mono (zero_le k)) hm₀;
  have h : q₁ ∈ (Γ[p, m]ᴾ)[p, k + 1]ⁱ ∨ q₂ ∈ (Γ[p, m]ᴾ)[p, k + 1]ⁱ := by
    simp only [insertFamily, Nat.add_eq, add_zero, encodek, hmₖ, ↓reduceIte, k];
    split;
    . right; simp only [mem_insert_iff, true_or];
    . left; simp only [mem_insert_iff, true_or];
  cases h with
  | inl h => left; apply mem_iUnionPrimeFamily (by assumption);
  | inr h => right; apply mem_iUnionPrimeFamily (by assumption);

lemma exists_primeFamily_deducible_of_iUnionPrimeFamily_deducible : (Γ[p]ᴾ ⊢ⁱ! q) → (∃ k, Γ[p, k]ᴾ ⊢ⁱ! q) := by
  generalize e : Γ[p]ᴾ = Γ';
  intro h;
  induction h.some with
  | axm h₁ =>
    subst e;
    obtain ⟨m, hm⟩ := by simpa using h₁;
    existsi m;
    exact axm! hm;
  | modusPonens h₁ h₂ ih₁ ih₂ =>
    obtain ⟨m₁, hm₁⟩ := ih₁ ⟨h₁⟩;
    obtain ⟨m₂, hm₂⟩ := ih₂ ⟨h₂⟩;
    by_cases hm : m₁ ≤ m₂;
    case pos =>
      existsi m₂;
      exact (weakening! (primeFamily_mono hm) hm₁) ⨀ hm₂;
    case neg =>
      replace hm : m₂ ≤ m₁ := le_of_not_le hm;
      existsi m₁;
      exact hm₁ ⨀ (weakening! (primeFamily_mono hm) hm₂);
  | eaxm ih =>
    existsi 0;
    obtain ⟨q, hq⟩ := ih;
    subst hq;
    apply efq!;
  | _ =>
    existsi 0;
    try first
    | apply verum!;
    | apply imply₁!;
    | apply imply₂!;
    | apply conj₁!;
    | apply conj₂!;
    | apply conj₃!;
    | apply disj₁!;
    | apply disj₂!;
    | apply disj₃!;
    -- | apply efq!;

lemma iUnionPrimeFamily_closed : Closed (Γ[p]ᴾ) := by
  intro q hq;
  let k := encode (p ⋎ q);
  have hpq : Γ[p]ᴾ ⊢ⁱ! (p ⋎ q) := disj₂'! hq;
  obtain ⟨m, hm⟩ := exists_primeFamily_deducible_of_iUnionPrimeFamily_deducible hpq;
  have hm₀ : (Γ[p, m]ᴾ)[p, 0]ⁱ ⊢ⁱ! p ⋎ q := by simpa only [insertFamily];
  have hmₖ : (Γ[p, m]ᴾ)[p, k]ⁱ ⊢ⁱ! p ⋎ q := weakening! (insertFamily_mono (zero_le k)) hm₀;
  have h : q ∈ (Γ[p, m]ᴾ)[p, k + 1]ⁱ := by
    simp [insertFamily, hmₖ, k, (show insert p (Γ[p,m]ᴾ[p,encode (p ⋎ q)]ⁱ) ⊢ⁱ! p by apply axm!; simp)];
  exact mem_iUnionPrimeFamily (by assumption);

variable (hU : Γ ⊬ⁱ! p)

lemma iUnionPrimeFamily_undeducible : Γ[p]ᴾ ⊬ⁱ! p := by
  by_contra hC;
  replace hC : Γ[p]ᴾ ⊢ⁱ! p := by simpa [System.not_unprovable_iff_provable] using hC;
  obtain ⟨m, (hm : Γ[p, m]ᴾ ⊢ⁱ! p)⟩ := exists_primeFamily_deducible_of_iUnionPrimeFamily_deducible hC;
  have : Γ[p, m]ᴾ ⊬ⁱ! p := primeFamily_undeducible hU;
  contradiction;

lemma iUnionPrimeFamily_consistent : (Γ[p]ᴾ).Consistent 𝐄𝐅𝐐 := by
  by_contra hC;
  replace hC : Γ[p]ᴾ ⊢ⁱ! ⊥ := by simpa only [Consistent] using hC;
  have : Γ[p]ᴾ ⊬ⁱ! p := iUnionPrimeFamily_undeducible hU;
  have : Γ[p]ᴾ ⊢ⁱ! p := efq'! hC;
  contradiction;

lemma iUnionPrimeFamily_subset_self : Γ ⊆ Γ[p]ᴾ := by
  intro q hq;
  simp [iUnionPrimeFamily];
  existsi 0;
  simpa;

lemma prime_expansion : ∃ Ω : PrimeTheory β, (Γ ⊆ Ω.theory ∧ Ω.theory ⊬ⁱ! p) := by
  let Ω : PrimeTheory β := ⟨Γ[p]ᴾ, ⟨iUnionPrimeFamily_consistent hU, iUnionPrimeFamily_closed, iUnionPrimeFamily_disjunctive⟩⟩;
  existsi Ω;
  constructor;
  . apply iUnionPrimeFamily_subset_self;
  . apply iUnionPrimeFamily_undeducible hU;

end

variable [Encodable β]

def CanonicalModel (β) : Kripke.Model (PrimeTheory β) β where
  frame Ω₁ Ω₂ := Ω₁ ⊆ Ω₂
  val Ω p := atom p ∈ Ω
  trans Ω₁ Ω₂ Ω₃ := Set.Subset.trans
  refl Ω := by simpa using Set.Subset.rfl;
  hereditary h p hp := by apply h; exact hp;

@[simp]
lemma CanonicalModel.frame_def {Ω₁ Ω₂ : PrimeTheory β} : (CanonicalModel β).frame Ω₁ Ω₂ ↔ Ω₁ ⊆ Ω₂ := by rfl

@[simp]
lemma CanonicalModel.val_def {a : β} : (CanonicalModel β).val Ω a ↔ (atom a) ∈ Ω := by rfl

variable {β : Type u} [DecidableEq β] [Encodable β]

lemma truthlemma {Ω : PrimeTheory β} {p : Formula β} : (Ω ⊩ⁱ[(CanonicalModel β)] p) ↔ (Ω.theory ⊢ⁱ! p) := by
  induction p using rec' generalizing Ω with
  | hatom a =>
    simp_all;
    constructor;
    . intro h;
      exact ⟨Deduction.axm (CanonicalModel.val_def.mpr (by simpa using h))⟩;
    . apply PrimeTheory.closed;
  | hverum => simp; apply verum!;
  | hfalsum => simp [←System.unprovable_iff_not_provable]
  | hand p q ihp ihq =>
    simp_all;
    constructor;
    . intro h;
      exact conj₃'! h.1 h.2;
    . intro h;
      constructor;
      . exact conj₁'! h;
      . exact conj₂'! h;
  | hor p q ihp ihq =>
    simp_all;
    constructor;
    . intro h; simp at h;
      cases h with
      | inl h => simp [ihp] at h; exact disj₁'! h;
      | inr h => simp [ihq] at h; exact disj₂'! h;
    . intro h;
      cases Ω.disjunctive' (Ω.closed' h) with
      | inl h => left; exact ⟨Deduction.axm h⟩;
      | inr h => right; exact ⟨Deduction.axm h⟩;
  | himp p q ihp ihq =>
    constructor;
    . contrapose;
      intro h;
      simp;
      have h₁ : insert p Ω.theory ⊬ⁱ! q := dtr_not'! h;
      obtain ⟨Ω', hΩ'₁, hΩ'₂⟩ := prime_expansion h₁;
      existsi Ω';
      exact ⟨
        by simpa using ihp.mpr $ axm! (by apply hΩ'₁; simp_all;),
        Set.Subset.trans
          (show Ω.theory ⊆ insert p Ω.theory by simp_all)
          (show insert p Ω.theory ⊆ Ω'.theory by simp_all),
        by simpa using ihq.not.mpr (hΩ'₂);
      ⟩;
    . intro h;
      simp;
      by_contra hC; simp at hC;
      obtain ⟨Ω', ⟨hp, hΩΩ', hq⟩⟩ := hC;
      have hp : Ω'.theory ⊢ⁱ! p := ihp.mp hp;
      have hq : Ω'.theory ⊬ⁱ! q := ihq.not.mp hq;
      have : Ω'.theory ⊢ⁱ! q := (weakening! hΩΩ' h) ⨀ hp;
      contradiction;

theorem completes {Γ : Theory β} {p : Formula β} : (Γ ⊨ⁱ p) → (Γ ⊢ⁱ! p) := by
  contrapose;
  intro hnp hp;
  have ⟨Ω, ⟨hsΩ, hnpΩ⟩⟩ := prime_expansion hnp;
  replace : ¬Ω.theory ⊢ᴾ[𝐄𝐅𝐐]! p := hnpΩ;
  have := truthlemma.not.mpr hnpΩ;
  have := hp (CanonicalModel β) (by
    intro q hq;
    exact truthlemma.mpr ⟨(Deduction.axm (hsΩ hq))⟩;
  );
  contradiction;

theorem complete_iff {Γ : Theory β} {p : Formula β} : (Γ ⊨ⁱ p) ↔ Γ ⊢ⁱ! p:=
  ⟨Kripke.completes, Kripke.sounds⟩

section DisjProp

private def DPCounterModel (M₁ : Kripke.Model γ₁ β) (M₂ : Kripke.Model γ₂ β) (w₁ : γ₁) (w₂ : γ₂) : Kripke.Model (Unit ⊕ γ₁ ⊕ γ₂) β where
  frame w v :=
    match w, v with
    | (Sum.inl _), (Sum.inl _) => True
    | (Sum.inl _), (Sum.inr $ Sum.inl v) => M₁.frame w₁ v
    | (Sum.inl _), (Sum.inr $ Sum.inr v) => M₂.frame w₂ v
    | (Sum.inr $ Sum.inl w), (Sum.inr $ Sum.inl v) => M₁.frame w v
    | (Sum.inr $ Sum.inr w), (Sum.inr $ Sum.inr v) => M₂.frame w v
    | _, _ => False
  val w a :=
    match w with
    | Sum.inr $ Sum.inl w => M₁.val w a
    | Sum.inr $ Sum.inr w => M₂.val w a
    | _ => False
  refl := by
    simp only [Reflexive, Sum.forall, forall_const, true_and];
    constructor <;> { intros; rfl };
  trans := by
    simp only [Transitive, Sum.forall, forall_true_left, imp_self, forall_const, true_and, IsEmpty.forall_iff, implies_true, and_true, and_self, imp_false];
    constructor;
    . constructor;
      . intros; apply M₁.trans (by assumption) (by assumption);
      . intros; apply M₂.trans (by assumption) (by assumption);
    . constructor;
      . intros; apply M₁.trans (by assumption) (by assumption);
      . intros; apply M₂.trans (by assumption) (by assumption);
  hereditary := by
    simp only [Sum.forall, imp_false, not_false_eq_true, implies_true, forall_true_left, forall_const, IsEmpty.forall_iff, and_self, true_and, and_true];
    constructor;
    . intro _ _; apply M₁.hereditary;
    . intro _ _; apply M₂.hereditary;

variable {M₁ : Kripke.Model γ₁ β} {M₂ : Kripke.Model γ₂ β}

private lemma DPCounterModel_left {p : Formula β} : (w ⊩ⁱ[M₁] p) ↔ (Sum.inr $ Sum.inl w) ⊩ⁱ[DPCounterModel M₁ M₂ w₁ w₂] p := by
  induction p using rec' generalizing w with
  | himp p₁ p₂ ih₁ ih₂ =>
    constructor;
    . simp only [Formula.Intuitionistic.Kripke.Satisfies.imp_def'];
      intro h v hv hp₁;
      replace ⟨v, hv, hv'⟩ : ∃ v', M₁.frame w v' ∧ v = (Sum.inr (Sum.inl v')) := by
        simp [DPCounterModel] at hv;
        split at hv;
        all_goals simp_all;
      subst hv';
      have := ih₁.mpr hp₁;
      have := h v hv this;
      have := ih₂.mp this;
      simpa;
    . simp only [Formula.Intuitionistic.Kripke.Satisfies.imp_def'];
      intro h v hv hp₁;
      have := ih₁.mp hp₁;
      have := h (Sum.inr $ Sum.inl v) (by simpa [DPCounterModel]) this;
      have := ih₂.mpr this;
      simpa;
  | _ => simp_all [DPCounterModel];

private lemma DPCounterModel_right {p : Formula β} : (w ⊩ⁱ[M₂] p) ↔ (Sum.inr $ Sum.inr w) ⊩ⁱ[DPCounterModel M₁ M₂ w₁ w₂] p := by
  induction p using rec' generalizing w with
  | himp p₁ p₂ ih₁ ih₂ =>
    constructor;
    . simp only [Formula.Intuitionistic.Kripke.Satisfies.imp_def'];
      intro h v hv hp₂;
      replace ⟨v, hv, hv'⟩ : ∃ v', M₂.frame w v' ∧ v = (Sum.inr (Sum.inr v')) := by
        simp [DPCounterModel] at hv;
        split at hv;
        all_goals simp_all;
      subst hv';
      have := ih₁.mpr hp₂;
      have := h v hv this;
      have := ih₂.mp this;
      simpa;
    . simp only [Formula.Intuitionistic.Kripke.Satisfies.imp_def'];
      intro h v hv hp₁;
      have := ih₁.mp hp₁;
      have := h (Sum.inr $ Sum.inr v) (by simpa [DPCounterModel]) this;
      have := ih₂.mpr this;
      simpa;
  | _ => simp_all [DPCounterModel];

theorem disjunctive {p q : Formula β} : ∅ ⊢ⁱ! p ⋎ q → ∅ ⊢ⁱ! p ∨ ∅ ⊢ⁱ! q := by
  contrapose;
  intro h;
  apply not_imp_not.mpr Kripke.sounds;

  have ⟨(hp : ∅ ⊬ⁱ! p), (hq : ∅ ⊬ⁱ! q)⟩ := not_or.mp h;
  obtain ⟨γ₁, M₁, w₁, hp⟩ := by simpa [Formula.Intuitionistic.Kripke.Consequence] using not_imp_not.mpr Kripke.completes hp;
  obtain ⟨γ₂, M₂, w₂, hq⟩ := by simpa [Formula.Intuitionistic.Kripke.Consequence] using not_imp_not.mpr Kripke.completes hq;
  let M : Kripke.Model (Unit ⊕ γ₁ ⊕ γ₂) β := DPCounterModel M₁ M₂ w₁ w₂;

  simp [Formula.Intuitionistic.Kripke.Consequence, Theory.Intuitionistic.Kripke.Satisfies];
  existsi _, M, Sum.inl ();

  have : ¬Sum.inl () ⊩ⁱ[M] p := not_imp_not.mpr (Kripke.hereditary_formula (by simp [M]; rfl)) (DPCounterModel_left.not.mp hp)
  have : ¬Sum.inl () ⊩ⁱ[M] q := not_imp_not.mpr (Kripke.hereditary_formula (by simp [M]; rfl)) (DPCounterModel_right.not.mp hq)

  simp_all;

end DisjProp

end LO.Propositional.Superintuitionistic.Intuitionistic.Kripke
