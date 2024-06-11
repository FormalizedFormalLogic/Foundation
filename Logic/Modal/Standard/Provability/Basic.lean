import Logic.FirstOrder.Incompleteness.ProvabilityCondition
import Logic.Modal.Standard.Deduction

namespace LO

namespace System

variable {F S : Type*} [LogicalConnective F] [System F S]
lemma Subtheory.prf! {𝓢 𝓣 : S} [𝓢 ≼ 𝓣] {f} : 𝓢 ⊢! f → 𝓣 ⊢! f := λ ⟨p⟩ ↦ ⟨Subtheory.prf p⟩

end System


namespace FirstOrder

-- Supplemental
namespace ProvabilityPredicate

section Loeb

variable [Semiterm.Operator.GoedelNumber L (Sentence L)]

def HilbertBernays₁.D1s [T₀ ≼ T] [HilbertBernays₁ β T₀ T] {σ : Sentence L} : T ⊢! σ → T ⊢! ⦍β⦎σ := by
  intro h;
  apply System.Subtheory.prf! (𝓢 := T₀);
  apply HilbertBernays₁.D1 h;

def HilbertBernays₂.D2s [T₀ ≼ T] [HilbertBernays₂ β T₀ T] {σ τ : Sentence L} : T ⊢! ⦍β⦎(σ ⟶ τ) ⟶ ⦍β⦎σ ⟶ ⦍β⦎τ := by
  apply System.Subtheory.prf! (𝓢 := T₀);
  apply HilbertBernays₂.D2;

def HilbertBernays₃.D3s [T₀ ≼ T] [HilbertBernays₃ β T₀ T] {σ : Sentence L} : T ⊢! ⦍β⦎σ ⟶ ⦍β⦎⦍β⦎σ := by
  apply System.Subtheory.prf! (𝓢 := T₀);
  apply HilbertBernays₃.D3;

def HilbertBernays.D2' [T₀ ≼ T] [HilbertBernays β T₀ T] {σ τ : Sentence L} [System.ModusPonens T] : T ⊢! ⦍β⦎(σ ⟶ τ) → T ⊢! ⦍β⦎σ ⟶ ⦍β⦎τ := by
  intro h;
  exact (HilbertBernays₂.D2s (T₀ := T₀)) ⨀ h;

class Loeb (β : ProvabilityPredicate L L) (T₀ : Theory L) (T : outParam (Theory L)) where
  LT {σ : Sentence L} : T ⊢! ⦍β⦎σ ⟶ σ → T ⊢! σ

def Loeb.LT' [Loeb β T₀ T] {σ : Sentence L} : T ⊢! ⦍β⦎σ ⟶ σ → T ⊢! σ := Loeb.LT T₀

class FormalizedLoeb (β : ProvabilityPredicate L L) (T₀ : Theory L) (T : outParam (Theory L)) where
  FLT {σ : Sentence L} : T₀ ⊢! ⦍β⦎(⦍β⦎σ ⟶ σ) ⟶ ⦍β⦎σ

/-
  TODO:
  単にsorryを消すためだけに導入しただけ．
  `(⦍β⦎· ⟶ σ)`への特殊な不動点(Kriesel sentence)が取れるというだけで，より一般的に示すことが出来るはず．
-/
class KreiselDiagonalizable (β : ProvabilityPredicate L L) (T₀ : Theory L) (T : Theory L) where
  diag : ∀ σ, ∃ (θ : Sentence L), T₀ ⊢! θ ⟷ (⦍β⦎θ ⟶ σ)

end Loeb


section Fixpoints

variable [Semiterm.Operator.GoedelNumber L₀ (Sentence L)]
         (β : ProvabilityPredicate L L)

def Consistency (β : ProvabilityPredicate L₀ L) : Sentence L₀ := ~⦍β⦎⊥
notation "Con⦍" β "⦎" => Consistency β

end Fixpoints

end ProvabilityPredicate

open System System.NegationEquiv
variable {L : Language} [Semiterm.Operator.GoedelNumber L (Sentence L)]
                        {β : ProvabilityPredicate L L}
                        {T₀ T : Theory L}

open ProvabilityPredicate

open LO.System

variable [DecidableEq (Sentence L)]

section

variable (T₀ T : Theory L) [T₀ ≼ T] [System.Classical T₀] [System.Classical T] [HilbertBernays β T₀ T]
         [KreiselDiagonalizable β T₀ T] -- TODO: 消す

open HilbertBernays₁ HilbertBernays₂ HilbertBernays₃ HilbertBernays

private lemma loeb_fixpoint
  [KreiselDiagonalizable β T₀ T]
  (σ) : ∃ (θ : Sentence L), T₀ ⊢! ⦍β⦎θ ⟶ ⦍β⦎σ ∧ T₀ ⊢! (⦍β⦎θ ⟶ σ) ⟶ θ := by
  have : ∃ (θ : Sentence L), T₀ ⊢! θ ⟷ (⦍β⦎θ ⟶ σ) := KreiselDiagonalizable.diag T σ;
  obtain ⟨θ, hθ⟩ := this;
  have hθ₁ : T₀ ⊢! θ ⟶ (⦍β⦎θ ⟶ σ) := conj₁'! hθ;
  have hθ₂ : T₀ ⊢! (⦍β⦎θ ⟶ σ) ⟶ θ := conj₂'! hθ;
  clear hθ;

  use θ;
  constructor;
  . exact (imp_trans! (D2 ⨀ D1 (Subtheory.prf! hθ₁)) D2) ⨀₁ D3;
  . exact hθ₂;

lemma LoebTheorm (H : T ⊢! ⦍β⦎σ ⟶ σ) : T ⊢! σ := by
  obtain ⟨θ, hθ₁, hθ₂⟩ := loeb_fixpoint (β := β) T₀ T σ;
  have d₂ : T ⊢! ⦍β⦎θ ⟶ σ := imp_trans! (Subtheory.prf! hθ₁) H;
  have d₃ : T ⊢! θ := Subtheory.prf! hθ₂ ⨀ d₂;
  have d₄ : T₀ ⊢! ⦍β⦎θ := D1 d₃;
  have d₅ : T ⊢! ⦍β⦎θ := Subtheory.prf! d₄;
  exact d₂ ⨀ d₅;

lemma FormalizedLoebTheorem : T₀ ⊢! ⦍β⦎(⦍β⦎σ ⟶ σ) ⟶ ⦍β⦎σ := by
  obtain ⟨θ, hθ₁, hθ₂⟩ := loeb_fixpoint (β := β) T₀ T σ;
  have : T₀ ⊢! (⦍β⦎σ ⟶ σ) ⟶ (⦍β⦎θ ⟶ σ) := by
    apply FiniteContext.deduct'!;
    apply FiniteContext.deduct!;
    have : [⦍β⦎θ, ⦍β⦎σ ⟶ σ] ⊢[T₀]! ⦍β⦎θ := FiniteContext.by_axm!;
    exact (FiniteContext.by_axm!) ⨀ ((FiniteContext.of'! hθ₁) ⨀ this);
  have : T ⊢! (⦍β⦎σ ⟶ σ) ⟶ θ := Subtheory.prf! $ imp_trans! this hθ₂;
  exact imp_trans! (D2 ⨀ (D1 this)) hθ₁;

instance
  [T₀ ≼ T] [System.Classical T₀] [System.Classical T] [HilbertBernays β T₀ T]
  [KreiselDiagonalizable β T₀ T] -- TODO: 消す
  : Loeb β T₀ T := ⟨LoebTheorm T₀ T⟩

instance
  [System.Classical T] [HilbertBernays β T T]
  [KreiselDiagonalizable β T T] -- TODO: 消す
  : Loeb β T T := inferInstance

end

variable [System.Classical T₀] [System.Classical T] [System.NegationEquiv T]

/-- Second Incompleteness -/
lemma unprovable_consistency_of_Loeb [Loeb β T₀ T] : System.Consistent T → T ⊬! ~⦍β⦎⊥ := by
  contrapose;
  intro hC; simp [neg_equiv'!] at hC;
  have : T ⊢! ⊥ := Loeb.LT T₀ hC;
  apply System.not_consistent_iff_inconsistent.mpr;
  apply System.inconsistent_of_provable this;

-- TODO: Remove H since this is 2nd incompleteness theorem consequence
lemma formalized2nd [Loeb β T₀ T] (H : T ⊬! ~Con⦍β⦎) : T ⊬! Con⦍β⦎ ⟶ ~⦍β⦎(~Con⦍β⦎) := by
  by_contra hC;
  have : T ⊢! ~Con⦍β⦎ := Loeb.LT T₀ (System.contra₁'! hC);
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

/-
  TODO:
  `ArithmeticalSoundness`と`ArithmeticalCompleteness`を単純にinstance化する際には大抵`T₀`に依存してしまうため型推論が壊れてしまう．
  もう少し良いやり方がありそうな気もするので一旦コメントアウト
section

variable {L : FirstOrder.Language} [Semiterm.Operator.GoedelNumber L (Sentence L)]
variable (α) (β : ProvabilityPredicate L L)

class ArithmeticalSoundness (𝓓 : DeductionParameter α) (T : FirstOrder.Theory L) where
  sound : ∀ {p}, (𝓓 ⊢! p) → (∀ f, T ⊢! f[β] p)

class ArithmeticalCompleteness (𝓓 : DeductionParameter α) (T : FirstOrder.Theory L) where
  complete : ∀ {p}, (∀ f, T ⊢! f[β] p) → (𝓓 ⊢! p)

class ProvabilityLogic (𝓓 : DeductionParameter α) (T : FirstOrder.Theory L)where
  is : System.theory 𝓓 = { p | ∀ f, T ⊢! f[β] p }

variable {α β} {𝓓 : DeductionParameter α} {T : FirstOrder.Theory L}

instance [ArithmeticalSoundness α β 𝓓 T] [ArithmeticalCompleteness α β 𝓓 T] : ProvabilityLogic α β 𝓓 T where
  is := by
    apply Set.eq_of_subset_of_subset;
    . intro p hp;
      simp only [Set.mem_setOf_eq];
      exact ArithmeticalSoundness.sound hp;
    . intro p hp;
      simp at hp;
      exact ArithmeticalCompleteness.complete hp;

end
-/

section ArithmeticalSoundness

open System
open ProvabilityPredicate

variable {L : FirstOrder.Language} [Semiterm.Operator.GoedelNumber L (Sentence L)]
         [DecidableEq (Sentence L)]
         (T₀ : FirstOrder.Theory L) (T : FirstOrder.Theory L) [T₀ ≼ T]
         (β : ProvabilityPredicate L L)
         [β.HilbertBernays T₀ T] [β.KreiselDiagonalizable T₀ T] -- TODO: 消す
variable [System.Classical T₀] [System.Classical T] [System.NegationEquiv T]
-- TODO: `T₀ ≼ T`で`T₀`が`System.Classical`なら`T`も`System.Classical`であると思われる．

lemma arithmetical_soundness_K4Loeb (h : 𝐊𝟒(𝐋) ⊢! p) : ∀ {f : Realization L α}, T ⊢! (f[β] p) := by
  intro f;
  induction h using Deduction.inducition! with
  | hNec _ ih => exact HilbertBernays₁.D1s (T₀ := T₀) ih;
  | hMaxm hp =>
    rcases hp with (hK | hFour)
    . obtain ⟨p, q, e⟩ := hK; subst_vars; apply HilbertBernays₂.D2s (T₀ := T₀);
    . obtain ⟨p, e⟩ := hFour; subst_vars; apply HilbertBernays₃.D3s (T₀ := T₀);
  | hLoeb _ ih => exact Loeb.LT T₀ ih;
  | hHenkin => simp_all only [Bool.false_eq_true];
  | hMdp ihpq ihp =>
    simp [Interpretation] at ihpq;
    exact ihpq ⨀ ihp;
  | hDne =>
    dsimp [Interpretation];
    exact imp_trans! (conj₁'! $ iffComm'! NegationEquiv.negneg_equiv!) dne!;
  | _ =>
    dsimp;
    first
    | apply verum!;
    | apply imply₁!;
    | apply imply₂!;
    | apply conj₁!;
    | apply conj₂!;
    | apply conj₃!;
    | apply disj₁!;
    | apply disj₂!;
    | apply disj₃!;

theorem arithmetical_soundness_GL (h : 𝐆𝐋 ⊢! p) : ∀ {f : Realization L α}, T ⊢! (f[β] p) := by
  apply arithmetical_soundness_K4Loeb (T₀ := T₀);
  exact (System.reducible_iff.mp reducible_GL_K4Loeb) h;

end ArithmeticalSoundness

end Modal.Standard.Provability

end LO
