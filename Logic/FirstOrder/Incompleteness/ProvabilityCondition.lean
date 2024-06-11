import Logic.FirstOrder.Arith.Theory
import Logic.Logic.HilbertStyle.Gentzen
import Logic.Logic.HilbertStyle.Supplemental

namespace LO.FirstOrder

structure ProvabilityPredicate (L₀ L : Language) where
  prov : Semisentence L₀ 1

namespace ProvabilityPredicate

section

variable [Semiterm.Operator.GoedelNumber L₀ (Sentence L)]

def pr (β : ProvabilityPredicate L₀ L) (σ : Sentence L) : Semisentence L₀ n := β.prov/[⸢σ⸣]

notation "⦍" β "⦎" σ:80 => pr β σ

class Conservative (β : ProvabilityPredicate L₀ L) (T₀ : Theory L₀) (T : outParam (Theory L)) where
  iff (σ : Sentence L) : T ⊢! σ ↔ T₀ ⊢! ⦍β⦎ σ

def consistency (β : ProvabilityPredicate L₀ L) : Sentence L₀ := ~⦍β⦎⊥
notation "Con⦍" β "⦎" => consistency β

end

section Conditions

variable [Semiterm.Operator.GoedelNumber L (Sentence L)]

class HilbertBernays₁ (β : ProvabilityPredicate L L) (T₀ : Theory L) (T : outParam (Theory L)) where
  D1 {σ : Sentence L} : T ⊢! σ → T₀ ⊢! ⦍β⦎σ


class HilbertBernays₂ (β : ProvabilityPredicate L L) (T₀ : Theory L) (T : outParam (Theory L)) where
  D2 {σ τ : Sentence L} : T₀ ⊢! ⦍β⦎(σ ⟶ τ) ⟶ ⦍β⦎σ ⟶ ⦍β⦎τ


class HilbertBernays₃ (β : ProvabilityPredicate L L) (T₀ : Theory L) (T : outParam (Theory L)) where
  D3 {σ : Sentence L} : T₀ ⊢! ⦍β⦎σ ⟶ ⦍β⦎⦍β⦎σ


class HilbertBernays (β : ProvabilityPredicate L L) (T₀ : Theory L) (T : outParam (Theory L))
  extends β.HilbertBernays₁ T₀ T, β.HilbertBernays₂ T₀ T, β.HilbertBernays₃ T₀ T

class Diagonalization (T : Theory L) where
  fixpoint : Semisentence L 1 → Sentence L
  diag (θ) : T ⊢! fixpoint θ ⟷ θ/[⸢fixpoint θ⸣]


class Loeb (β : ProvabilityPredicate L L) (T₀ : Theory L) (T : outParam (Theory L)) where
  LT {σ : Sentence L} : T ⊢! ⦍β⦎σ ⟶ σ → T ⊢! σ

class FormalizedLoeb (β : ProvabilityPredicate L L) (T₀ : Theory L) (T : outParam (Theory L)) where
  FLT {σ : Sentence L} : T₀ ⊢! ⦍β⦎(⦍β⦎σ ⟶ σ) ⟶ ⦍β⦎σ


section

variable {T₀ T : Theory L}
variable [T₀ ≼ T] {σ τ : Sentence L}

def HilbertBernays₁.D1s [HilbertBernays₁ β T₀ T]: T ⊢! σ → T ⊢! ⦍β⦎σ := by
  intro h;
  apply System.Subtheory.prf! (𝓢 := T₀);
  apply HilbertBernays₁.D1 h;

def HilbertBernays₂.D2s [HilbertBernays₂ β T₀ T] : T ⊢! ⦍β⦎(σ ⟶ τ) ⟶ ⦍β⦎σ ⟶ ⦍β⦎τ := by
  apply System.Subtheory.prf! (𝓢 := T₀);
  apply HilbertBernays₂.D2;

def HilbertBernays₂.D2' [HilbertBernays β T₀ T] [System.ModusPonens T] : T ⊢! ⦍β⦎(σ ⟶ τ) → T ⊢! ⦍β⦎σ ⟶ ⦍β⦎τ := by
  intro h;
  exact (HilbertBernays₂.D2s (T₀ := T₀)) ⨀ h;

def HilbertBernays₃.D3s [HilbertBernays₃ β T₀ T] : T ⊢! ⦍β⦎σ ⟶ ⦍β⦎⦍β⦎σ := by
  apply System.Subtheory.prf! (𝓢 := T₀);
  apply HilbertBernays₃.D3;

def Loeb.LT' [Loeb β T₀ T] {σ : Sentence L} : T ⊢! ⦍β⦎σ ⟶ σ → T ⊢! σ := Loeb.LT T₀

end

end Conditions


section LoebTheorem

variable [DecidableEq (Sentence L)]
         [Semiterm.Operator.GoedelNumber L (Sentence L)]
         (T₀ T : Theory L) [T₀ ≼ T] [Diagonalization T₀]
open LO.System
open HilbertBernays₁ HilbertBernays₂ HilbertBernays₃
open Diagonalization

private lemma loeb_fixpoint
  (β : ProvabilityPredicate L L) [β.HilbertBernays T₀ T]
  (σ : Sentence L) : ∃ (θ : Sentence L), T₀ ⊢! ⦍β⦎θ ⟶ ⦍β⦎σ ∧ T₀ ⊢! (⦍β⦎θ ⟶ σ) ⟶ θ := by
  have hθ := diag (T := T₀) “x | !β.prov x → !σ”;
  generalize (fixpoint T₀ “x | !β.prov x → !σ”) = θ at hθ;

  have eθ : θ ⟷ (β.prov/[#0] ⟶ σ/[])/[⸢θ⸣] = θ ⟷ (⦍β⦎θ ⟶ σ) := by
    simp [←Rew.hom_comp_app, Rew.substs_comp_substs]; rfl;
  replace hθ : T₀ ⊢! θ ⟷ (⦍β⦎θ ⟶ σ) := by simpa [←eθ] using hθ;

  existsi θ;
  constructor;
  . exact (imp_trans! (D2 ⨀ (D1 (Subtheory.prf! $ conj₁'! hθ))) D2) ⨀₁ D3;
  . exact conj₂'! hθ;

variable {β : ProvabilityPredicate L L} [β.HilbertBernays T₀ T]

theorem loeb_theorm (H : T ⊢! ⦍β⦎σ ⟶ σ) : T ⊢! σ := by
  obtain ⟨θ, hθ₁, hθ₂⟩ := loeb_fixpoint T₀ T β σ;

  have d₁ : T  ⊢! ⦍β⦎θ ⟶ σ := imp_trans! (Subtheory.prf! hθ₁) H;
  have    : T₀ ⊢! ⦍β⦎θ      := D1 $ Subtheory.prf! hθ₂ ⨀ d₁;
  have d₂ : T  ⊢! ⦍β⦎θ      := Subtheory.prf! this;
  exact d₁ ⨀ d₂;

instance : Loeb β T₀ T := ⟨loeb_theorm T₀ T⟩

theorem formalized_loeb_theorem : T₀ ⊢! ⦍β⦎(⦍β⦎σ ⟶ σ) ⟶ ⦍β⦎σ := by
  obtain ⟨θ, hθ₁, hθ₂⟩ := loeb_fixpoint T₀ T β σ;

  have : T₀ ⊢! (⦍β⦎σ ⟶ σ) ⟶ (⦍β⦎θ ⟶ σ) := imply_left_replace! hθ₁
  have : T ⊢! (⦍β⦎σ ⟶ σ) ⟶ θ := Subtheory.prf! $ imp_trans! this hθ₂;
  exact imp_trans! (D2 ⨀ (D1 this)) hθ₁;

instance : FormalizedLoeb β T₀ T := ⟨formalized_loeb_theorem T₀ T⟩

end LoebTheorem

section Second

variable [DecidableEq (Sentence L)]
         [Semiterm.Operator.GoedelNumber L (Sentence L)]
         (T₀ T : Theory L) [T₀ ≼ T] [Diagonalization T₀]
         {β : ProvabilityPredicate L L} [β.Loeb T₀ T]
open LO.System LO.System.NegationEquiv
open HilbertBernays₁ HilbertBernays₂ HilbertBernays₃
open Diagonalization

/-- Second Incompleteness Theorem -/
lemma unprovable_consistency_of_Loeb : System.Consistent T → T ⊬! ~⦍β⦎⊥ := by
  contrapose;
  intro hC; simp [neg_equiv'!] at hC;
  have : T ⊢! ⊥ := Loeb.LT T₀ hC;
  apply System.not_consistent_iff_inconsistent.mpr;
  apply System.inconsistent_of_provable this;

/-- Formalized Second Incompleteness Theorem -/
lemma formalized_second (H : T ⊬! ~Con⦍β⦎) : T ⊬! Con⦍β⦎ ⟶ ~⦍β⦎(~Con⦍β⦎) := by
  by_contra hC;
  have : T ⊢! ~Con⦍β⦎ := Loeb.LT T₀ $ contra₁'! hC;
  contradiction;

end Second

end ProvabilityPredicate

end LO.FirstOrder
