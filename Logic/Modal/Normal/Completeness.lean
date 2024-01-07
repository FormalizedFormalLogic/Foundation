import Logic.Propositional.Basic.Completeness
import Logic.Modal.Normal.Formula
import Logic.Modal.Normal.HilbertStyle
import Logic.Modal.Normal.Semantics
import Logic.Modal.Normal.Soundness

namespace LO.Modal.Normal

open Formula Context Deduction

variable {α β : Type u}

section

variable (α : Type u) (Λ : Logic β) (Γ : Context β)

def Maximal := ∀ p, p ∈ Γ ∨ ~p ∈ Γ

def Inconsistent := Γ ⊢ᴹ(Λ)! ⊥

def Consistent := ¬(Inconsistent Λ Γ)

def WeakCompleteness := ∀ (f : Frame α) (p : Formula β), (⊧ᴹᶠ[f] p) → (⊢ᴹ(Λ) p)

def Completeness := ∀ f ∈ FrameClass α β Λ, ∀ Γ (p : Formula β), (Γ ⊨ᴹᶠ[f] p) → (Γ ⊢ᴹ(Λ) p)

def FrameClassSatisfiable := ∃ f ∈ FrameClass α β Λ, ∃ V w, w ⊧ᴹˢ[⟨f, V⟩] Γ

end

@[simp]
lemma inconsistent_insert_falsum : Inconsistent Λ (insert ⊥ Γ) := by
  simp [Inconsistent];
  exact ⟨axm (by simp)⟩;

lemma consistent_no_falsum (hConsisΓ : Consistent Λ Γ) : ⊥ ∉ Γ := by
  intro h;
  have h₁ : Γ ⊢ᴹ(Λ) ⊥ := axm h;
  have h₂ : IsEmpty (Γ ⊢ᴹ(Λ) ⊥) := by simpa [Consistent, Inconsistent] using hConsisΓ;
  exact h₂.false h₁;

lemma consistent_neither_provable (hConsisΓ : Consistent Λ Γ) : ¬((Γ ⊢ᴹ(Λ)! p) ∧ (Γ ⊢ᴹ(Λ)! ~p)) := by
  by_contra hC;
  exact hConsisΓ ⟨modus_ponens hC.2.some hC.1.some⟩;

@[simp]
lemma consistent_neg_undeducible (hConsisΓ : Consistent Λ Γ) : (Γ ⊢ᴹ(Λ)! p) → (Γ ⊬ᴹ(Λ)! ~p) := fun h hc => consistent_neither_provable hConsisΓ ⟨h, hc⟩

lemma consistent_neither_included (hConsisΓ : Consistent Λ Γ) : ¬(p ∈ Γ ∧ ~p ∈ Γ) := by
  by_contra hC;
  exact consistent_neither_provable hConsisΓ ⟨⟨axm hC.1⟩, ⟨axm hC.2⟩⟩;

lemma consistent_subset {Γ Δ : Context β} : (Γ ⊆ Δ) → (Consistent Λ Δ) → (Consistent Λ Γ) := by
  intro hs _ hInconsisΓ;
  suffices Δ ⊢ᴹ(Λ)! ⊥ by aesop;
  exact ⟨weakening' _ hs hInconsisΓ.some⟩;

lemma consistent_insert {Γ : Context β} {p : Formula β} : (Consistent Λ (insert p Γ)) → (Consistent Λ Γ) := consistent_subset (by simp)

lemma neg_consistent_intro_undeducible (_ : Consistent Λ (insert (~p) Γ)) : (Γ ⊬ᴹ(Λ)! p) := by
  by_contra hC;
  suffices (insert (~p) Γ ⊢ᴹ(Λ) ⊥) by have : (insert (~p) Γ ⊢ᴹ(Λ)! ⊥) := ⟨this⟩; aesop;
  have h₁ : insert (~p) Γ ⊢ᴹ(Λ) p := Deduction.weakening' _ (by simp) hC.some;
  have h₂ : insert (~p) Γ ⊢ᴹ(Λ) p ⟶ ⊥ := by {
    have : insert (~p) Γ ⊢ᴹ(Λ) ~p := Deduction.axm (by simp);
    simpa [Formula.neg_eq] using this;
  };
  exact Deduction.modus_ponens h₂ h₁;

lemma undeducible_intro_neg_consistent (h : Γ ⊬ᴹ(Λ)! p) : (Consistent Λ (insert (~p) Γ)) := by sorry;

lemma maximal_consistent_modus_ponens (hConsisΓ : Consistent Λ Γ) (hMaximalΓ : Maximal Γ) : (p ∈ Γ) → ((p ⟶ q) ∈ Γ) → (q ∈ Γ) := by
  intro hp hpq; by_contra hnq;
  exact consistent_neither_provable hConsisΓ ⟨
    ⟨modus_ponens (axm hpq) (axm hp)⟩,
    ⟨axm (show ~q ∈ Γ from have := hMaximalΓ q; by simp_all)⟩
  ⟩;

lemma intro_Completeness : (∀ (Γ : Context β), Consistent Λ Γ → FrameClassSatisfiable α Λ Γ) → (Completeness α Λ) := by sorry;
  -- simp [Completeness];
  -- intro hSatisfiable f Γ p h₁ h₂;

structure ConsistentTheory (Λ : Logic β) where
  theory : Context β
  consistent : Consistent Λ theory

structure MaximalConsistentTheory (Λ : Logic β) where
  theory : Context β
  consistent : Consistent Λ theory
  maximal : Maximal theory

lemma lindenbaum (Γ : Context β) (hConsisΓ : Consistent Λ Γ) :
  ∃ (Γ' : Context β), (Consistent Λ Γ') ∧ (Maximal Γ') ∧ (Γ ⊆ Γ') := by sorry;

lemma lindenbaum' (Γ : Context β) (hConsisΓ : Consistent Λ Γ) :
  ∃ (MΓ : MaximalConsistentTheory Λ), (Γ ⊆ MΓ.theory) := by
  have ⟨Γ', ⟨hConsisΓ', hMaximalΓ', hΓΓ'⟩⟩ := lindenbaum Γ hConsisΓ;
  existsi ⟨Γ', hConsisΓ', hMaximalΓ'⟩; assumption;

def CanonicalModel (Λ : Logic β) : Model (MaximalConsistentTheory Λ) β where
  frame (Γ Δ) := ∀ (p : Formula β), (□p ∈ Γ.theory) → (p ∈ Δ.theory)
  val (Γ a) := (atom a) ∈ Γ.theory

@[simp]
lemma CanonicalModel_frame {Λ : Logic β} {MΓ MΔ : MaximalConsistentTheory Λ} :
  (CanonicalModel Λ).frame MΓ MΔ ↔ (∀ (p : Formula β), (□p ∈ MΓ.theory) → (p ∈ MΔ.theory))
  := by rfl

@[simp]
lemma CanonicalModel_val {Λ : Logic β} {MΓ : MaximalConsistentTheory Λ} {a : β} :
  a ∈ (CanonicalModel Λ).val MΓ ↔ (atom a) ∈ MΓ.theory
  := by rfl

attribute [simp] Context.Models

/-- a.k.a. _Truth Lemma_ -/
lemma mem_maximalConsistentTheory_iff
  {MΓ : MaximalConsistentTheory Λ} {p : Formula β} : (MΓ ⊧ᴹˢ[CanonicalModel Λ] p) ↔ (p ∈ MΓ.theory) := by
  induction p using rec' with
  | hatom a => simp;
  | hfalsum => have := consistent_no_falsum MΓ.consistent; aesop;
  | himp p q ihp ihq =>
    simp [ihp, ihq];
    sorry;
  | hbox p ih =>
    simp;
    constructor;
    . sorry;
    . sorry;

lemma mem_maximalConsistentTheory_iff'
  {MΓ : MaximalConsistentTheory Λ} {Γ : Context β} : (MΓ ⊧ᴹˢ[CanonicalModel Λ] Γ) ↔ (Γ ⊆ MΓ.theory) := by
  simp [Set.subset_def];
  constructor;
  . intro h p hp; exact (mem_maximalConsistentTheory_iff).mp (h p hp);
  . intro h p hp; exact (mem_maximalConsistentTheory_iff).mpr (h p hp);

theorem LogicK.Hilbert.completes : Completeness (MaximalConsistentTheory (𝐊 : Logic β)) (𝐊 : Logic β) := by
  apply intro_Completeness;

  intro Γ hConsisΓ;
  let ⟨MΓ, hMΓ⟩ := lindenbaum' Γ hConsisΓ;

  existsi (CanonicalModel 𝐊).frame;
  constructor;
  . apply LogicK.def_FrameClass;
  . existsi (CanonicalModel 𝐊).val, MΓ;
    apply mem_maximalConsistentTheory_iff'.mpr hMΓ;


/-
section

variable {Λ : Logic β} {Γ : Context β} (consisΓ : Consistent Λ Γ)

lemma exists_maximal_consistent_context (consisΓ : Consistent Λ Γ):
  ∃ (Γ' : Context β), (Consistent Λ Γ' ∧ Γ ⊆ Γ' ∧ ∀ Δ, Consistent Λ Δ → Γ' ⊆ Δ → Δ = Γ') := sorry

noncomputable def MaximalConsistentContext : Context β := Classical.choose $ exists_maximal_consistent_context consisΓ

abbrev MCC := MaximalConsistentContext consisΓ

lemma consistent_MCC : (MCC consisΓ).Consistent Λ := (Classical.choose_spec $ exists_maximal_consistent_context consisΓ).1

lemma subset_MCC : Γ ⊆ (MCC consisΓ) := (Classical.choose_spec $ exists_maximal_consistent_context consisΓ).2.1

lemma maximal_MCC : ∀ Δ, (Δ.Consistent Λ) → (MCC consisΓ) ⊆ Δ → Δ = (MCC consisΓ) := (Classical.choose_spec $ exists_maximal_consistent_context consisΓ).2.2

end
-/

/-
section

class ConsistentContext (Λ : Logic β) (Γ : Context β) where
  consistent : Consistent Λ Γ

class MaximalConsistentContext (Λ : Logic β) (Γ : Context β) extends ConsistentContext Λ Γ where
  maximal : Maximal Γ

abbrev CC (Λ : Logic β) := ConsistentContext Λ
abbrev MCC (Λ : Logic β) := MaximalConsistentContext Λ

end

namespace ConsistentContext

open ConsistentContext

variable [CC Λ Γ]

lemma no_falsum : ⊥ ∉ Γ := by
  by_contra hC;
  have h₁ : Γ ⊢ᴹ(Λ) ⊥ := axm hC;
  have h₂ : IsEmpty (Γ ⊢ᴹ(Λ) ⊥) := by simpa [Consistent, Inconsistent] using consistent;
  exact h₂.false h₁;

end ConsistentContext


namespace MaximalConsistentContext

open MaximalConsistentContext

variable [MCC Λ Γ]

lemma closed_modus_ponens : (p ∈ Γ) → ((p ⟶ q) ∈ Γ) → (q ∈ Γ) := by
  intro hp hpq; by_contra hnq;

  have hp : Γ ⊢ᴹ(Λ) p := Deduction.axm hp;
  have hpq : Γ ⊢ᴹ(Λ) (p ⟶ q) := Deduction.axm hpq;
  have hq : Γ ⊢ᴹ(Λ) q := Deduction.modus_ponens hpq hp;

  have hnq : Γ ⊢ᴹ(Λ) ~q := by {
    sorry; -- have : ~q ∈ Γ; have b := maximal; sorry;
    -- exact Deduction.axm this;
  }
  exact consistent ⟨hq⟩ ⟨hnq⟩;

end MaximalConsistentContext

end


section Lemmas

variable {Λ : Logic β}
variable [Encodable β]

lemma def_not_FrameclassSatisfiable {Γ : Context β} {p : Formula β} : ∀ {f : Frame α}, (Γ ⊭ᴹᶠ[f] p) ↔ (FrameSatisfiable f (insert (~p) Γ)) := by
  simp_all [FrameclassSatisfiable, FrameSatisfiable, ModelSatisfiable];
  aesop;

lemma def_not_Consistent {Γ : Context β} {p : Formula β} : (Γ ⊬ᴹ(Λ)! p) ↔ ((insert (~p) Γ).Consistent Λ) := by
  simp_all [Consistent, Inconsistent];
  constructor;
  . intro h;
    by_contra hC; simp at hC;
    have h₁ : insert (~p) Γ ⊢ᴹ(Λ) (p ⟶ ⊥) := by {
      have : insert (~p) Γ ⊢ᴹ(Λ) ~p := Deduction.axm (by simp);
      simpa [Formula.neg] using this;
    };
    sorry;
  . intro h;
    by_contra hC; simp at hC;
    suffices (insert (~p) Γ ⊢ᴹ(Λ) ⊥) by have : (insert (~p) Γ ⊢ᴹ(Λ)! ⊥) := ⟨this⟩; aesop;
    have h₁ : insert (~p) Γ ⊢ᴹ(Λ) p := Deduction.weakening' _ (by simp) hC.some;
    have h₂ : insert (~p) Γ ⊢ᴹ(Λ) p ⟶ ⊥ := by {
      have : insert (~p) Γ ⊢ᴹ(Λ) ~p := Deduction.axm (by simp);
      simpa [Formula.neg_eq] using this;
    };
    exact Deduction.modus_ponens h₂ h₁;

lemma intro_Completeness : (∀ (f : Frame α) (Γ : Context β), Γ.FrameSatisfiable f) → (Completeness α Λ)  := by
  simp only [Completeness];
  intro h f Γ p _ hΓp;
  have h₁ : Γ ⊭ᴹᶠ[f] p := (def_not_FrameclassSatisfiable.mpr $ h f (insert (~p) Γ));
  have := h₁ hΓp;
  contradiction;

section LindenbaumAux

variable (Λ : Logic β) [∀ Γ p, Decidable (Consistent Λ (insert p Γ))] [Encodable α]

def lindenbaum_next (p : Formula β) (Γ : CC Λ) : CC Λ :=
  if h : (insert p Γ.ctx).Consistent Λ then ⟨(insert p Γ.ctx), by assumption;⟩
  else ⟨
    insert (~p) Γ.ctx,
    by
      by_contra hC; sorry;
      -- simp [def_not_Consistent] at h;
  ⟩

def lindenbaum_family (Γ : CC Λ) : ℕ → (CC Λ)
  | 0     => Γ
  | n + 1 =>
    match (Formula.decode n) with
    | none   => lindenbaum_family Γ n
    | some p => lindenbaum_next Λ p (lindenbaum_family Γ n)

notation Γ "[" Λ "," i "]" => lindenbaum_family Λ Γ i

lemma lindenbaum_subset (Γ : CC Λ) (n : ℕ) : (Γ[Λ, n]).ctx ⊆ (Γ[Λ, n + 1]).ctx := by
  simp [lindenbaum_family, lindenbaum_next];
  aesop;

lemma maximal (Γ : CC Λ) (p : Formula β) : (p ∈ Γ[Λ, p.encode + 1].ctx) ∨ (p ∉ Γ[Λ, p.encode + 1].ctx) := by
  induction Formula.encode p with
  | zero =>
    simp [lindenbaum_family, lindenbaum_next, Formula.decode, (show ¬Consistent Λ (insert ⊥ Γ.ctx) by have := Inconsistent.no_falsum_include Λ Γ.ctx; aesop)];
    sorry;
  | succ n ih =>
    sorry;

end LindenbaumAux

lemma lindenbaum (Γ : CC Λ) : ∃ (Γ' : MCC Λ), Γ.ctx ⊆ Γ'.ctx := by sorry;

def CanonicalModel (Λ : Logic β) : Model (MCC Λ) β where
  rel (Γ Δ) := ∀ (p : Formula β), (□p ∈ Γ.ctx) → (p ∈ Δ.ctx)
  val (Γ a) := (atom a) ∈ Γ.ctx

lemma TruthLemma (mΓ : MCC Λ) (p : Formula β) : (mΓ.ctx ⊨ᴹᵐ[CanonicalModel Λ] p) ↔ (p ∈ mΓ.ctx) := by
  induction p using rec' with
  | hatom a => sorry;
  | hfalsum =>
    constructor;
    . intro h; sorry;
    . intro h; have := ConsistentContext.no_falsum mΓ.toConsistentContext h; contradiction;
  | himp p q ihp ihq =>
    constructor;
    . intro h; sorry;
    . intro h; sorry;
  | hbox p ih => sorry;

lemma TruthLemma' (mΓ : MCC Λ) (Δ : CC Λ) : (mΓ.ctx ⊨ᴹᵐ[CanonicalModel Λ] Δ.ctx) ↔ (Δ.ctx ⊆ mΓ.ctx) := by
  simp [Context.ModelConsequence];
  constructor;
  . intro h p hp; exact (TruthLemma mΓ p).mp $ h p hp;
  . intro h p hp;
    have ⟨mΔ, hmΔ⟩ := lindenbaum Δ;
    have h₁ := (TruthLemma mΔ p).mpr $ Set.mem_of_subset_of_mem hmΔ hp;
    intros;
    sorry;

-- lemma model_existence (Γ : Context β) : Γ.consistent Λ ↔ (frameclass_satisfiable (FrameClass.Trivial α) Γ) := by sorry;

lemma tmp1 (p : Formula β) : mΓ ⊧ᴹˢ[CanonicalModel Λ] p := by
  sorry

lemma canonical_satisfiable {Γ : CC Λ} {mΓ : MCC Λ} (h : mΓ.ctx ⊨ᴹᵐ[CanonicalModel Λ] Γ.ctx) : (FrameSatisfiable (CanonicalModel Λ).toFrame Γ.ctx) := by
  simp [FrameSatisfiable];
  existsi (CanonicalModel Λ).val;
  simp [ModelSatisfiable];
  existsi mΓ;
  intro p hp;
  have b := (TruthLemma' mΓ Γ).mp h;

end Lemmas

/-
namespace CanonicalModel

variable (Λ : Set (Formula β))

lemma isReflexive (_ : Λ ⊆ 𝐓) : (@CanonicalModel β Λ).toFrame.Reflexive := by sorry;

lemma isSymmetric (_ : Λ ⊆ 𝐁): (@CanonicalModel β Λ).toFrame.Symmetric := by sorry;

lemma isSerial (_ : Λ ⊆ 𝐃): (@CanonicalModel β Λ).toFrame.Serial := by sorry;

lemma isTransitive (_ : Λ ⊆ 𝟒): (@CanonicalModel β Λ).toFrame.Transitive := by sorry;

lemma isEuclidean (_ : Λ ⊆ 𝟓): (@CanonicalModel β Λ).toFrame.Euclidean := by sorry;

end CanonicalModel
-/

theorem Hilbert.LogicK.completeness : Completeness (MCC (𝐊 : Logic β)) (𝐊 : Logic β) := by
  apply intro_Completeness;
  intro f Γ;
  simp [FrameSatisfiable];
  existsi (CanonicalModel 𝐊).val;
  simp [ModelSatisfiable];

  wlog hC : (Γ.Consistent 𝐊) with H; {
    simp only [Consistent, Inconsistent, not_nonempty_iff, not_isEmpty_iff] at hC;
    have b := LogicK.Hilbert.sounds (CanonicalModel 𝐊).toFrame;
  }

  let ⟨mΓ, hmΓ⟩ := lindenbaum ⟨Γ, hC⟩;
  have h := (TruthLemma' mΓ ⟨Γ, hC⟩).mpr hmΓ;

  apply canonical_satisfiable h;
  trivial;
-/
end LO.Modal.Normal
