import Logic.FirstOrder.Incompleteness.ProvabilityCondition
import Logic.Modal.Standard.Deduction

namespace LO

namespace System

variable {F S : Type*} [LogicalConnective F] [System F S]
lemma Subtheory.prf! {𝓢 𝓣 : S} [𝓢 ≼ 𝓣] {f} : 𝓢 ⊢! f → 𝓣 ⊢! f := λ ⟨p⟩ ↦ ⟨Subtheory.prf p⟩

/-- Negation `~p` is `p ⟶ ⊥` on **system** -/
class NegationDef (𝓢 : S) where
  neg_def {p} : 𝓢 ⊢ ~p ⟷ (p ⟶ ⊥)


section

open NegationDef

variable {𝓢 : S}
         [Minimal 𝓢] [NegationDef 𝓢]
         {p q : F}

lemma NegationDef.neg_def! : 𝓢 ⊢! ~p ⟷ (p ⟶ ⊥) := ⟨NegationDef.neg_def⟩

def NegationDef.neg_def'.mp : 𝓢 ⊢ ~p → 𝓢 ⊢ p ⟶ ⊥ := λ h => (conj₁' neg_def) ⨀ h
def NegationDef.neg_def'.mpr : 𝓢 ⊢ p ⟶ ⊥ → 𝓢 ⊢ ~p := λ h => (conj₂' neg_def) ⨀ h
lemma NegationDef.neg_def'! : 𝓢 ⊢! ~p ↔ 𝓢 ⊢! p ⟶ ⊥ := ⟨λ ⟨h⟩ => ⟨neg_def'.mp h⟩, λ ⟨h⟩ => ⟨neg_def'.mpr h⟩⟩

end

end System


namespace FirstOrder

-- Supplemental
namespace ProvabilityPredicate

section Loeb

variable [Semiterm.Operator.GoedelNumber L (Sentence L)]

class Loeb (β : ProvabilityPredicate L L) (T₀ : Theory L) where
  LT (σ : Sentence L) : T₀ ⊢! ⦍β⦎σ ⟶ σ → T₀ ⊢! σ

class FormalizedLoeb (β : ProvabilityPredicate L L) (T₀ : Theory L) (T : outParam (Theory L)) where
  FLT (σ : Sentence L) : T ⊢! ⦍β⦎(⦍β⦎σ ⟶ σ) ⟶ ⦍β⦎σ

end Loeb


section Fixpoints

variable [Semiterm.Operator.GoedelNumber L₀ (Sentence L)]
         (β : ProvabilityPredicate L L)

def Consistency (β : ProvabilityPredicate L₀ L) : Sentence L₀ := ~⦍β⦎⊥
notation "Con⦍" β "⦎" => Consistency β

end Fixpoints

end ProvabilityPredicate

open System System.NegationDef
variable {L : Language} [Semiterm.Operator.GoedelNumber L (Sentence L)]
                        {β : ProvabilityPredicate L L}
                        {T₀ T : Theory L}

open ProvabilityPredicate

variable [System.Classical T] [System.NegationDef T]
variable [NegDefinition (Semisentence L 0)] [DecidableEq (Semisentence L 0)] -- TODO: 雑に導入したので消す


/-- Second Incompleteness -/
lemma unprovable_consistency_of_Loeb [Loeb β T] : System.Consistent T → T ⊬! ~⦍β⦎⊥ := by
  contrapose;
  intro hC; simp at hC;
  have : T ⊢! ⦍β⦎⊥ ⟶ ⊥ := neg_def'.mp hC;
  have : T ⊢! ⊥ := Loeb.LT _ this;
  apply System.not_consistent_iff_inconsistent.mpr;
  apply System.inconsistent_of_provable this;

-- TODO: Remove H
lemma formalized2nd [l : Loeb β T] (H : T ⊬! ~Con⦍β⦎) : T ⊬! Con⦍β⦎ ⟶ ~⦍β⦎(~Con⦍β⦎) := by
  by_contra hC;
  have : T ⊢! ~Con⦍β⦎ := l.LT _ (System.contra₁'! hC);
  contradiction;

end FirstOrder


namespace Modal.Standard.Provability

open LO.FirstOrder

variable {α : Type*} [DecidableEq α]

/-- Mapping modal prop vars to first-order sentence -/
def Realization (L) (α : Type u) := α → FirstOrder.Sentence L

/-- Mapping modal formulae to first-order sentence -/
def Interpretation
  [Semiterm.Operator.GoedelNumber L (FirstOrder.Sentence L)]
  (f : Realization L α) (β : ProvabilityPredicate L L) : Formula α → FirstOrder.Sentence L
  | .atom a => f a
  | .box p => ⦍β⦎(Interpretation f β p)
  | ⊤ => ⊤
  | ⊥ => ⊥
  | p ⟶ q => (Interpretation f β p) ⟶ (Interpretation f β q)
  | p ⋏ q => (Interpretation f β p) ⋏ (Interpretation f β q)
  | p ⋎ q => (Interpretation f β p) ⋎ (Interpretation f β q)
notation f "[" β "] " p => Interpretation f β p

section

variable {L : FirstOrder.Language} [Semiterm.Operator.GoedelNumber L (Sentence L)]
variable (β : ProvabilityPredicate L L)

class ArithmeticalSoundness (𝓓 : DeductionParameter α) (T : FirstOrder.Theory L) where
  sound : ∀ {p}, (𝓓 ⊢! p) → (∀ f, T ⊢! f[β] p)

class ArithmeticalCompleteness (𝓓 : DeductionParameter α) (T : FirstOrder.Theory L) where
  complete : ∀ {p}, (∀ f, T ⊢! f[β] p) → (𝓓 ⊢! p)

class ProvabilityLogic (𝓓 : DeductionParameter α) (T : FirstOrder.Theory L)where
  is : System.theory 𝓓 = { p | ∀ f, T ⊢! f[β] p }

variable {β} {𝓓 : DeductionParameter α} {T : FirstOrder.Theory L}

instance [ArithmeticalSoundness β 𝓓 T] [ArithmeticalCompleteness β 𝓓 T] : ProvabilityLogic β 𝓓 T where
  is := by
    apply Set.eq_of_subset_of_subset;
    . intro p hp;
      simp only [Set.mem_setOf_eq];
      exact ArithmeticalSoundness.sound hp;
    . intro p hp;
      simp at hp;
      exact ArithmeticalCompleteness.complete hp;

end

section ArithmeticalSoundness

open System
open ProvabilityPredicate

variable {L : FirstOrder.Language} [Semiterm.Operator.GoedelNumber L (Sentence L)]
         (β : ProvabilityPredicate L L)
         (T₀ T : FirstOrder.Theory L) [T₀ ≼ T]
         [β.HilbertBernays T T] -- MEMO: `β.HilbertBernays T₀ T`にするとメタ変数的な問題が発生して困る
         [β.Loeb T] -- TODO: Remove
variable [Classical T] [NegationDef T]

lemma arithmetical_soundness_K4Loeb (h : 𝐊𝟒(𝐋) ⊢! p) : ∀ {f : Realization L α}, T ⊢! (f[β] p) := by
  intro f;
  induction h using Deduction.inducition! with
  | @hNec _ p h ih =>
    exact (HilbertBernays₁.D1 _) ih;
  | hMaxm hp =>
    rcases hp with (hK | hFour)
    . obtain ⟨p, q, e⟩ := hK; subst_vars;
      apply HilbertBernays₂.D2;
    . obtain ⟨p, e⟩ := hFour; subst_vars;
      apply HilbertBernays₃.D3 _;
  | hLoeb _ ih => apply (Loeb.LT _) ih;
  | hHenkin => simp_all only [Bool.false_eq_true];
  | hMdp ihpq ihp =>
    simp [Interpretation] at ihpq;
    exact ihpq ⨀ ihp;
  | hDne =>
    dsimp [NegDefinition.neg, Interpretation]; -- TODO: 単なる二重否定除去であるので直ちに成り立ってほしいが上手く出来ない．
    sorry; -- apply System.dne!;
  | _ =>
    dsimp;
    first
    | apply System.verum!;
    | apply System.imply₁!;
    | apply System.imply₂!;
    | apply System.conj₁!;
    | apply System.conj₂!;
    | apply System.conj₃!;
    | apply System.disj₁!;
    | apply System.disj₂!;
    | apply System.disj₃!;

theorem arithmetical_soundness_GL (h : 𝐆𝐋 ⊢! p) : ∀ {f : Realization L α}, T ⊢! (f[β] p) := by
  apply arithmetical_soundness_K4Loeb;
  exact (System.reducible_iff.mp reducible_GL_K4Loeb) h;

instance : ArithmeticalSoundness (α := α) β 𝐆𝐋 T := ⟨arithmetical_soundness_GL β _⟩

end ArithmeticalSoundness

end Modal.Standard.Provability

end LO
