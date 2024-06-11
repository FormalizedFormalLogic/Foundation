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

def HilbertBernays₂.D2' [HilbertBernays β T₀ T] [System.ModusPonens T] : T₀ ⊢! ⦍β⦎(σ ⟶ τ) → T₀ ⊢! ⦍β⦎σ ⟶ ⦍β⦎τ := by
  intro h;
  exact HilbertBernays₂.D2 ⨀ h;

def HilbertBernays₃.D3s [HilbertBernays₃ β T₀ T] : T ⊢! ⦍β⦎σ ⟶ ⦍β⦎⦍β⦎σ := by
  apply System.Subtheory.prf! (𝓢 := T₀);
  apply HilbertBernays₃.D3;

def Loeb.LT' [Loeb β T₀ T] {σ : Sentence L} : T ⊢! ⦍β⦎σ ⟶ σ → T ⊢! σ := Loeb.LT T₀

end

end Conditions

section FirstIncompleteness

variable [DecidableEq (Sentence L)]
         [Semiterm.Operator.GoedelNumber L (Sentence L)]
         (β : ProvabilityPredicate L L)
         (T₀ T : Theory L) [T₀ ≼ T] [Diagonalization T₀]
open LO.System LO.System.NegationEquiv
open HilbertBernays₁ HilbertBernays₂ HilbertBernays₃
open Diagonalization

lemma existence_goedel_sentence : ∃ (θ : Sentence L), T ⊢! θ ⟷ ~⦍β⦎θ := by
  have hθ := diag (T := T₀) “x | ¬!β.prov x”;
  generalize (fixpoint T₀ “x | ¬!β.prov x”) = θ at hθ;

  have eθ : θ ⟷ (~β.prov/[#0])/[⸢θ⸣] = θ ⟷ ~(⦍β⦎θ) := by
    simp [←Rew.hom_comp_app, Rew.substs_comp_substs]; rfl;

  use θ;
  apply Subtheory.prf! (𝓢 := T₀);
  simpa [←eθ] using hθ;

noncomputable abbrev goedel := (existence_goedel_sentence β T₀ T).choose
local notation "G" => goedel β T₀ T

lemma goedel_spec : T ⊢! G ⟷ ~⦍β⦎G := (existence_goedel_sentence β T₀ T).choose_spec


lemma unprovable_goedel [β.HilbertBernays₁ T₀ T] : System.Consistent T → T ⊬! G := by
  contrapose;
  intro h; simp at h;
  have h₁ : T ⊢! ⦍β⦎G := D1s (T₀ := T₀) h;
  have h₂ : T ⊢! ~⦍β⦎G := (conj₁'! (goedel_spec β T₀ T)) ⨀ h;

  apply System.not_consistent_iff_inconsistent.mpr;
  apply System.inconsistent_of_provable;
  exact (neg_equiv'!.mp h₂) ⨀ h₁;

lemma unrefutable_goedel [β.Conservative T T] : System.Consistent T → T ⊬! ~G := by
  contrapose;
  intro h; simp at h;
  have : T ⊢! ⦍β⦎G := dne'! $ (conj₁'! $ neg_iff'! $ goedel_spec β T₀ T) ⨀ h;
  have : T ⊢! G := Conservative.iff (T := T) _ |>.mpr this;
  apply System.not_consistent_iff_inconsistent.mpr;
  apply System.inconsistent_of_provable;
  exact (neg_equiv'!.mp h) ⨀ this;

lemma goedel_independent
  [β.HilbertBernays₁ T₀ T] [β.Conservative T T] [System.Consistent T]
  : System.Undecidable T G := by
  suffices T ⊬! G ∧ T ⊬! ~G by simpa [System.Undecidable, not_or] using this;
  constructor;
  . apply unprovable_goedel β T₀ T; assumption;
  . apply unrefutable_goedel β T₀ T; assumption;

lemma first_incompleteness
  [β.HilbertBernays₁ T₀ T] [β.Conservative T T] [System.Consistent T]
  : ¬System.Complete T := System.incomplete_iff_exists_undecidable.mpr ⟨G, goedel_independent β T₀ T⟩

end FirstIncompleteness


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


section

variable [DecidableEq (Sentence L)]
         [Semiterm.Operator.GoedelNumber L (Sentence L)]
         {T₀ T : Theory L} [T₀ ≼ T] [Diagonalization T₀]
         {β : ProvabilityPredicate L L} [β.HilbertBernays T₀ T]
open LO.System LO.System.NegationEquiv
open HilbertBernays₁ HilbertBernays₂ HilbertBernays₃
open Diagonalization

/-- Second Incompleteness Theorem -/
lemma lemma4_2_3 : T₀ ⊢! ~⦍β⦎σ ⟶ Con⦍β⦎ := contra₀'! $ D2 ⨀ (D1 efq!)

lemma lemma4_2_4 [T₀ ≼ U] [β.HilbertBernays T₀ U] : (U ⊢! Con⦍β⦎ ⟶ ~⦍β⦎σ) ↔ (U ⊢! ⦍β⦎σ ⟶ ⦍β⦎(~σ)) := by
  constructor;
  . intro H;
    exact contra₃'! $ imp_trans! (Subtheory.prf! (𝓢 := T₀) lemma4_2_3) H;
  . intro H;
    apply contra₀'!;
    exact imp_trans! H $ (by
      have : U ⊢! (σ ⋏ ~σ) ⟶ ⊥ := by sorry;
      have : T₀ ⊢! ⦍β⦎((σ ⋏ ~σ) ⟶ ⊥) := D1 this;
      have : T₀ ⊢! ⦍β⦎(σ ⋏ ~σ) ⟶ ⦍β⦎⊥ := D2 ⨀ this;
      have : U ⊢! ⦍β⦎(σ ⋏ ~σ) ⟶ ⦍β⦎⊥ := Subtheory.prf! (𝓢 := T₀) this
      exact imp_trans! (by sorry) this;
    );

end


section Second

variable [DecidableEq (Sentence L)]
         [Semiterm.Operator.GoedelNumber L (Sentence L)]
         (T₀ T : Theory L) [T₀ ≼ T] [Diagonalization T₀]
         {β : ProvabilityPredicate L L} [β.Loeb T₀ T]
open LO.System LO.System.NegationEquiv
open HilbertBernays₁ HilbertBernays₂ HilbertBernays₃
open Diagonalization

/-- Second Incompleteness Theorem -/
lemma unprovable_consistency_of_Loeb : System.Consistent T → T ⊬! Con⦍β⦎ := by
  contrapose;
  intro hC; simp at hC;
  have : T ⊢! ⊥ := Loeb.LT T₀ $ neg_equiv'!.mp hC;
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
