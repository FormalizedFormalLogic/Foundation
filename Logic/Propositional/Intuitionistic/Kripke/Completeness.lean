import Logic.Propositional.Intuitionistic.Deduction
import Logic.Propositional.Intuitionistic.Kripke.Semantics

namespace LO.Propositional.Intuitionistic

open Formula Theory Kripke
open Hilbert

section Consistency

variable {Γ : Theory β} (hConsisΓ : Theory.Consistent Γ)

lemma consistent_subset_undeducible_falsum (hΔ : Δ ⊆ Γ) : (Δ ⊬ᴵ! ⊥) := Hilbert.consistent_subset_undeducible_falsum (· ⊢ᴵ ·) hConsisΓ hΔ

@[simp] lemma consistent_no_falsum : ⊥ ∉ Γ := Hilbert.consistent_no_falsum (· ⊢ᴵ ·) hConsisΓ
@[simp] lemma consistent_iff_undeducible_falsum : Consistent Γ ↔ (Γ ⊬ᴵ! ⊥) := Hilbert.consistent_iff_undeducible_falsum (· ⊢ᴵ ·) Γ
@[simp] lemma consistent_undeducible_falsum : Γ ⊬ᴵ! ⊥ := consistent_iff_undeducible_falsum.mp hConsisΓ

lemma consistent_neither_undeducible : (Γ ⊬ᴵ! p) ∨ (Γ ⊬ᴵ! ~p) := Hilbert.consistent_neither_undeducible (· ⊢ᴵ ·) hConsisΓ p

end Consistency


namespace Theory

def Closed (Γ : Theory β) := ∀ p, (Γ ⊢ᴵ! p) → (p ∈ Γ)

def Disjunctive (Γ : Theory β) := ∀ p q, (p ⋎ q ∈ Γ) → (p ∈ Γ) ∨ (q ∈ Γ)

class Prime (T : Theory β) where
  consistent : Consistent T
  closed : Closed T
  disjunctive : Disjunctive T

end Theory

structure PrimeTheory (β) where
  theory : Theory β
  prime : Prime theory

namespace PrimeTheory

variable (Ω : PrimeTheory β)

def consistent : Consistent Ω.theory := Ω.prime.consistent
def closed : Closed Ω.theory := Ω.prime.closed
def disjunctive : Disjunctive Ω.theory := Ω.prime.disjunctive

@[simp] def membership (p : Formula β) (Ω : PrimeTheory β) := p ∈ Ω.theory
instance : Membership (Formula β) (PrimeTheory β) := ⟨membership⟩

@[simp] def subset (Ω₁ Ω₂ : PrimeTheory β) := Ω₁.theory ⊆ Ω₂.theory
instance : HasSubset (PrimeTheory β) := ⟨subset⟩

variable {Ω}

@[simp] lemma undeducible_falsum : Ω.theory ⊬ᴵ! ⊥ := consistent_undeducible_falsum Ω.consistent

@[simp] lemma no_falsum : ⊥ ∉ Ω := consistent_no_falsum Ω.consistent

lemma closed' {p : Formula β} : (Ω.theory ⊢ᴵ! p) → (p ∈ Ω) := Ω.closed p
lemma disjunctive' {p q : Formula β} : (p ⋎ q ∈ Ω) → (p ∈ Ω) ∨ (q ∈ Ω) := Ω.disjunctive p q

end PrimeTheory

section PrimeExpand

variable [Encodable (Formula β)]
open Encodable

-- variable [∀ (Γ : Theory β) (p : Formula β), Decidable (Γ ⊢ᴵ! p)]

open Classical in
@[simp] def primex_next (Γ : Theory β) (p : Formula β) (n : ℕ) : Theory β :=
  match (decode n) with
  | some (q₁ ⋎ q₂ : Formula β) =>
    if Γ ⊢ᴵ! (q₁ ⋎ q₂)
      then if (insert q₁ Γ) ⊢ᴵ! p then insert q₂ Γ else insert q₁ Γ
      else Γ
  | _ => Γ

def primex_family (Γ : Theory β) (p : Formula β) : ℕ → Theory β
  | 0 => Γ
  | n + 1 => primex_next Γ p n

notation Γ "[" p "," i "]" => primex_family Γ p i

@[simp]
lemma def_primex_family_zero (Γ : Theory β) : Γ[p, 0] = Γ := rfl

lemma primex_family_closed {Γ : Theory β} (h : Closed Γ) {p i} : Closed (Γ[p, i]) := by
  induction i with
  | zero => simp [primex_family]; simpa;
  | succ i ih =>
    simp_all [Closed];
    intro q hq;
    have := h q;
    have := ih q;
    sorry;

lemma primex_family_disjunctive {Γ : Theory β} (h : Disjunctive Γ) {p i} : Disjunctive (Γ[p, i]) := by
  induction i with
  | zero => simp [primex_family]; simpa;
  | succ i ih => sorry;

lemma subset_primex_family_original {Γ : Theory β} {p i} : Γ ⊆ Γ[p, i] := by
  induction i with
  | zero => simp [primex_family]; rfl
  | succ =>
    simp [primex_family];
    split; split; split;
    all_goals (first | simp | rfl);

lemma primex_family_subset_succ {Γ : Theory β} {p i} : Γ[p, i] ⊆ Γ[p, i + 1] := by
  induction i with
  | zero =>
    simp [primex_family];
    split; split; split;
    all_goals (first | simp | rfl);
  | succ k ih => sorry;

lemma primex_family_subset_monotone {Γ : Theory β} {p i j} (h : i ≤ j) : Γ[p, i] ⊆ Γ[p, j] := by
  induction h with
  | refl => rfl
  | step _ ih => exact Set.Subset.trans ih primex_family_subset_succ

lemma primex_family_monotone (Γ : Theory β) (p : Formula β) : Monotone (Γ[p, ·]) := by
  intro _ _ h; exact primex_family_subset_monotone h

def primex_family_sets (Γ : Theory β) (p : Formula β) : Set (Theory β) := { Γ[p, i] | i : ℕ }

lemma exists_primex (Γ : Theory β) (p : Formula β)
  : ∃ m ∈ { Γ[p, i] | i : ℕ }, Γ ⊆ m ∧ ∀ a ∈ { Γ[p, i] | i : ℕ }, m ⊆ a → a = m
  := zorn_subset_nonempty { Γ[p, i] | i : ℕ } (by
    intro c hc chain hnc;
    existsi (⋃₀ c);
    simp;
    constructor;
    . by_contra hC; simp at hC; sorry;
    . intro s a;
      exact Set.subset_sUnion_of_mem a;
  ) Γ (by existsi 0; simp)

noncomputable def primex (Γ : Theory β) (p : Formula β) : Theory β := exists_primex Γ p |>.choose
notation Γ "[" p "]" => primex Γ p

lemma primeExpand {Γ : Theory β} (hp : Γ ⊬ᴵ! p) : ∃ Ω : PrimeTheory β, (Γ ⊆ Ω.theory ∧ Ω.theory ⊬ᴵ! p) := by
  have ⟨Ω, ⟨h₁, ⟨h₂, h₃⟩⟩⟩ := exists_primex Γ ⊥;
  existsi ⟨Ω, (by sorry), (by sorry), (by sorry)⟩
  constructor;
  . exact h₂;
  . sorry; -- exact h₃;

end PrimeExpand

variable [Encodable (Formula β)] -- TODO: remove

def CanonicalModel (β) : Kripke.Model (PrimeTheory β) β where
  frame Ω₁ Ω₂ := Ω₁ ⊆ Ω₂
  val Ω p := atom p ∈ Ω
  trans Ω₁ Ω₂ Ω₃ := Set.Subset.trans
  refl Ω := by simpa using Set.Subset.rfl;
  herditary h p hp := by apply h; exact hp;

@[simp]
lemma CanonicalModel.frame_def {Ω₁ Ω₂ : PrimeTheory β} : (CanonicalModel β).frame Ω₁ Ω₂ ↔ Ω₁ ⊆ Ω₂ := by rfl

@[simp]
lemma CanonicalModel.val_def {a : β} : (CanonicalModel β).val Ω a ↔ (atom a) ∈ Ω := by rfl

variable [DecidableEq β]

lemma truthlemma {Ω : PrimeTheory β} {p : Formula β} : (Ω ⊩[(CanonicalModel β)] p) ↔ (Ω.theory ⊢ᴵ! p) := by
  induction p using rec' generalizing Ω with
  | hatom a =>
    constructor;
    . intro h;
      exact ⟨Deduction.axm (CanonicalModel.val_def.mpr h)⟩;
    . apply PrimeTheory.closed;
  | hfalsum => simp; exact PrimeTheory.undeducible_falsum;
  | hand p q ihp ihq =>
    constructor;
    . intro h;
      obtain ⟨hp, hq⟩ := h;
      have dp : Ω.theory ⊢ᴵ! p := ihp.mp hp;
      have dq : Ω.theory ⊢ᴵ! q := ihq.mp hq;
      exact conj₃'! dp dq;
    . intro h;
      constructor;
      . apply ihp.mpr; exact conj₁'! h;
      . apply ihq.mpr; exact conj₂'! h;
  | hor p q ihp ihq =>
    constructor;
    . intro h; simp at h;
      cases h with
      | inl h => simp [ihp] at h; exact disj₁'! h;
      | inr h => simp [ihq] at h; exact disj₂'! h;
    . intro h;
      cases Ω.disjunctive' (Ω.closed' h) with
      | inl h => left; exact ihp.mpr ⟨.axm h⟩;
      | inr h => right; exact ihq.mpr ⟨.axm h⟩;
  | himp p q ihp ihq =>
    constructor;
    . contrapose;
      intro h;
      simp [KripkeSatisfies.imp_def'];
      have h₁ : insert p Ω.theory ⊬ᴵ! q := dtr_not! h;
      obtain ⟨Ω', hΩ'₁, hΩ'₂⟩ := primeExpand h₁;
      existsi Ω';
      exact ⟨
        ihp.mpr $ axm! (by aesop),
        Set.Subset.trans
          (show Ω.theory ⊆ insert p Ω.theory by aesop)
          (show insert p Ω.theory ⊆ Ω'.theory by aesop),
        ihq.not.mpr hΩ'₂
      ⟩;
    . intro h;
      simp [KripkeSatisfies.imp_def'];
      by_contra hC; simp at hC;
      obtain ⟨Ω', ⟨hp, hΩΩ', hq⟩⟩ := hC;
      have hp : Ω'.theory ⊢ᴵ! p := ihp.mp hp;
      have hq : Ω'.theory ⊬ᴵ! q := ihq.not.mp hq;
      have := modus_ponens'! (weakening! hΩΩ' h) hp;
      contradiction;

lemma Kripke.completes {Γ : Theory β} {p : Formula β} : (Γ ⊨ᴵ p) → (Γ ⊢ᴵ! p) := by
  contrapose;
  intro hnp hp;
  have ⟨Ω, ⟨hsΩ, hnpΩ⟩⟩ := primeExpand hnp;
  have := truthlemma.not.mpr hnpΩ;
  have := hp (CanonicalModel β) Ω (by
    intro q hq;
    exact truthlemma.mpr ⟨(Deduction.axm (hsΩ hq))⟩;
  );
  contradiction;

end LO.Propositional.Intuitionistic
