import Logic.FirstOrder.Arith.Theory
import Logic.Logic.HilbertStyle.Gentzen
import Logic.Logic.HilbertStyle.Supplemental

namespace LO.FirstOrder

namespace DerivabilityCondition

structure ProvabilityPredicate (L₀ L : Language) where
  prov : Semisentence L₀ 1


namespace ProvabilityPredicate

variable [Semiterm.Operator.GoedelNumber L₀ (Sentence L)]

def pr (β : ProvabilityPredicate L₀ L) (σ : Sentence L) : Semisentence L₀ n := β.prov/[⸢σ⸣]

notation "⦍" β "⦎" σ:80 => pr β σ

end ProvabilityPredicate


class Diagonalization
  [Semiterm.Operator.GoedelNumber L (Sentence L)]
  (T : Theory L) where
  fixpoint : Semisentence L 1 → Sentence L
  diag (θ) : T ⊢! fixpoint θ ⟷ θ/[⸢fixpoint θ⸣]


section Consistency

def consistency [Semiterm.Operator.GoedelNumber L₀ (Sentence L)] (β : ProvabilityPredicate L₀ L) : Sentence L₀ := ~⦍β⦎⊥
notation "Con⦍" β "⦎" => consistency β

end Consistency


namespace ProvabilityPredicate

class Conservative
  [Semiterm.Operator.GoedelNumber L₀ (Sentence L)]
  (β : ProvabilityPredicate L₀ L) (T₀ : Theory L₀) (T : outParam (Theory L)) where
  iff (σ : Sentence L) : T ⊢! σ ↔ T₀ ⊢! ⦍β⦎σ

variable [Semiterm.Operator.GoedelNumber L (Sentence L)]

class HilbertBernays₁ (β : ProvabilityPredicate L L) (T₀ : Theory L) (T : outParam (Theory L)) where
  D1 {σ : Sentence L} : T ⊢! σ → T₀ ⊢! ⦍β⦎σ

class HilbertBernays₂ (β : ProvabilityPredicate L L) (T₀ : Theory L) (T : outParam (Theory L)) where
  D2 {σ τ : Sentence L} : T₀ ⊢! ⦍β⦎(σ ⟶ τ) ⟶ ⦍β⦎σ ⟶ ⦍β⦎τ

class HilbertBernays₃ (β : ProvabilityPredicate L L) (T₀ : Theory L) (T : outParam (Theory L)) where
  D3 {σ : Sentence L} : T₀ ⊢! ⦍β⦎σ ⟶ ⦍β⦎⦍β⦎σ

class HilbertBernays (β : ProvabilityPredicate L L) (T₀ : Theory L) (T : outParam (Theory L)) extends
  β.HilbertBernays₁ T₀ T, β.HilbertBernays₂ T₀ T, β.HilbertBernays₃ T₀ T

class Loeb (β : ProvabilityPredicate L L) (T₀ : Theory L) (T : outParam (Theory L)) where
  LT {σ : Sentence L} : T ⊢! ⦍β⦎σ ⟶ σ → T ⊢! σ

class FormalizedLoeb (β : ProvabilityPredicate L L) (T₀ : Theory L) (T : outParam (Theory L)) where
  FLT {σ : Sentence L} : T₀ ⊢! ⦍β⦎(⦍β⦎σ ⟶ σ) ⟶ ⦍β⦎σ

class Rosser (β : ProvabilityPredicate L L) (T₀ : Theory L) (T : outParam (Theory L)) where
  Ro {σ : Sentence L} : T ⊢! ~σ → T₀ ⊢! ~⦍β⦎(σ)


section

open LO.System

variable [DecidableEq (Sentence L)] [Semiterm.Operator.GoedelNumber L (Sentence L)]
         {β : ProvabilityPredicate L L}
         {T₀ T : Theory L} [T₀ ≼ T]
         [β.HilbertBernays T₀ T]
         {σ τ : Sentence L}

alias D1 := HilbertBernays₁.D1
alias D2 := HilbertBernays₂.D2
alias D3 := HilbertBernays₃.D3
alias LT := Loeb.LT
alias FLT := FormalizedLoeb.FLT
alias Ro := Rosser.Ro

def D1s [HilbertBernays₁ β T₀ T]: T ⊢! σ → T ⊢! ⦍β⦎σ := by
  intro h;
  apply System.Subtheory.prf! (𝓢 := T₀);
  apply HilbertBernays₁.D1 h;

def D2s [HilbertBernays₂ β T₀ T] : T ⊢! ⦍β⦎(σ ⟶ τ) ⟶ ⦍β⦎σ ⟶ ⦍β⦎τ := by
  apply System.Subtheory.prf! (𝓢 := T₀);
  apply HilbertBernays₂.D2;

def D2' [HilbertBernays β T₀ T] [System.ModusPonens T] : T₀ ⊢! ⦍β⦎(σ ⟶ τ) → T₀ ⊢! ⦍β⦎σ ⟶ ⦍β⦎τ := by
  intro h;
  exact HilbertBernays₂.D2 ⨀ h;

def D3s [HilbertBernays₃ β T₀ T] : T ⊢! ⦍β⦎σ ⟶ ⦍β⦎⦍β⦎σ := by
  apply System.Subtheory.prf! (𝓢 := T₀);
  apply HilbertBernays₃.D3;

def prov_distribute_imply (h : T ⊢! σ ⟶ τ) : T₀ ⊢! ⦍β⦎σ ⟶ ⦍β⦎τ := D2' $ D1 h

def prov_distribute_iff (h : T ⊢! σ ⟷ τ) : T₀ ⊢! ⦍β⦎σ ⟷ ⦍β⦎τ := by
  apply iff_intro!;
  . exact prov_distribute_imply $ and₁'! h;
  . exact prov_distribute_imply $ and₂'! h;

def prov_distribute_and : T₀ ⊢! ⦍β⦎(σ ⋏ τ) ⟶ ⦍β⦎σ ⋏ ⦍β⦎τ := by
  have h₁ : T₀ ⊢! ⦍β⦎(σ ⋏ τ) ⟶ ⦍β⦎σ := D2' <| D1 and₁!;
  have h₂ : T₀ ⊢! ⦍β⦎(σ ⋏ τ) ⟶ ⦍β⦎τ := D2' <| D1 and₂!;
  exact imply_right_and! h₁ h₂;

def prov_distribute_and! : T₀ ⊢! ⦍β⦎(σ ⋏ τ) → T₀ ⊢! ⦍β⦎σ ⋏ ⦍β⦎τ := λ h => prov_distribute_and ⨀ h

def prov_collect_and : T₀ ⊢! ⦍β⦎σ ⋏ ⦍β⦎τ ⟶ ⦍β⦎(σ ⋏ τ) := by
  have h₁ : T₀ ⊢! ⦍β⦎σ ⟶ ⦍β⦎(τ ⟶ σ ⋏ τ) := prov_distribute_imply $ and₃!;
  have h₂ : T₀ ⊢! ⦍β⦎(τ ⟶ σ ⋏ τ) ⟶ ⦍β⦎τ ⟶ ⦍β⦎(σ ⋏ τ) := D2;
  apply and_imply_iff_imply_imply'!.mpr;
  exact imp_trans''! h₁ h₂;

end

end ProvabilityPredicate


variable [DecidableEq (Sentence L)] [Semiterm.Operator.GoedelNumber L (Sentence L)]
         {β : ProvabilityPredicate L L}
         {T₀ T : Theory L} [T₀ ≼ T] [Diagonalization T₀]
         [β.HilbertBernays T₀ T]
         {σ τ : Sentence L}

open LO.System
open Diagonalization
open ProvabilityPredicate

abbrev goedel
  (T₀ T : Theory L) [Diagonalization T₀]
  (β : ProvabilityPredicate L L) [β.HilbertBernays₁ T₀ T] : Sentence L
  := fixpoint T₀ “x | ¬!β.prov x”
local notation "γ" => goedel T₀ T β

section GoedelSentence

variable [β.HilbertBernays₁ T₀ T]

lemma goedel_spec : T₀ ⊢! γ ⟷ ~⦍β⦎γ := by
  convert (diag (T := T₀) “x | ¬!β.prov x”);
  simp [goedel, ←Rew.hom_comp_app, Rew.substs_comp_substs];
  rfl;

private lemma goedel_specAux₁ : T ⊢! γ ⟷ ~⦍β⦎γ := Subtheory.prf! (𝓢 := T₀) goedel_spec

private lemma goedel_specAux₂ : T ⊢! ~γ ⟶ ⦍β⦎γ := contra₂'! $ and₂'! goedel_specAux₁

end GoedelSentence


class ProvabilityPredicate.GoedelSound (β : ProvabilityPredicate L L) (T₀ T) [Diagonalization T₀] [β.HilbertBernays₁ T₀ T] where
  γ_sound : T ⊢! ⦍β⦎(goedel T₀ T β) → T ⊢! (goedel T₀ T β)

open GoedelSound


section First

variable [System.Consistent T] [β.HilbertBernays₁ T₀ T]

theorem unprovable_goedel : T ⊬! γ := by
  intro h;
  have h₁ : T ⊢! ⦍β⦎γ := D1s (T₀ := T₀) h;
  have h₂ : T ⊢! ~⦍β⦎γ := (and₁'! goedel_specAux₁) ⨀ h;
  have : T ⊢! ⊥ := (neg_equiv'!.mp h₂) ⨀ h₁;

  have := not_consistent_iff_inconsistent.mpr $ inconsistent_iff_provable_bot.mpr this;
  contradiction;

theorem unrefutable_goedel [β.GoedelSound T₀ T] : T ⊬! ~γ := by
  intro h₂;
  have h₁ : T ⊢! γ := γ_sound $ goedel_specAux₂ ⨀ h₂;
  have : T ⊢! ⊥ := (neg_equiv'!.mp h₂) ⨀ h₁;

  have := not_consistent_iff_inconsistent.mpr $ inconsistent_iff_provable_bot.mpr this;
  contradiction;

theorem goedel_independent [β.GoedelSound T₀ T] : System.Undecidable T γ := by
  suffices T ⊬! γ ∧ T ⊬! ~γ by simpa [System.Undecidable, not_or] using this;
  constructor;
  . apply unprovable_goedel;
  . apply unrefutable_goedel;

theorem first_incompleteness [β.GoedelSound T₀ T]
  : ¬System.Complete T := System.incomplete_iff_exists_undecidable.mpr ⟨γ, goedel_independent⟩

end First


section Second

variable [Diagonalization T] [β.HilbertBernays T₀ T]

lemma formalized_consistent_of_existance_unprovable : T₀ ⊢! ~⦍β⦎σ ⟶ Con⦍β⦎ := contra₀'! $ D2 ⨀ (D1 efq!)

private lemma consistency_lemma_1 [T₀ ≼ U] [β.HilbertBernays T₀ U] : (U ⊢! Con⦍β⦎ ⟶ ~⦍β⦎σ) ↔ (U ⊢! ⦍β⦎σ ⟶ ⦍β⦎(~σ)) := by
  constructor;
  . intro H;
    exact contra₃'! $ imp_trans''! (Subtheory.prf! (𝓢 := T₀) formalized_consistent_of_existance_unprovable) H;
  . intro H;
    apply contra₀'!;
    have : T₀ ⊢! ⦍β⦎σ ⋏ ⦍β⦎(~σ) ⟶ ⦍β⦎⊥ := imp_trans''! prov_collect_and $ prov_distribute_imply lac!;
    have : U ⊢! ⦍β⦎σ ⟶ ⦍β⦎(~σ) ⟶ ⦍β⦎⊥ := Subtheory.prf! $ and_imply_iff_imply_imply'!.mp $ this;
    exact this ⨀₁ H;

private lemma consistency_lemma_2 : T₀ ⊢! (⦍β⦎σ ⟶ ⦍β⦎(~σ)) ⟶ ⦍β⦎σ ⟶ ⦍β⦎⊥ := by
  have : T ⊢! σ ⟶ ~σ ⟶ ⊥ := and_imply_iff_imply_imply'!.mp lac!
  have : T₀ ⊢! ⦍β⦎σ ⟶ ⦍β⦎(~σ ⟶ ⊥)  := prov_distribute_imply this;
  have : T₀ ⊢! ⦍β⦎σ ⟶ (⦍β⦎(~σ) ⟶ ⦍β⦎⊥) := imp_trans''! this D2;

  -- TODO: more simple proof
  apply FiniteContext.deduct'!;
  apply FiniteContext.deduct!;
  have d₁ : [⦍β⦎σ, ⦍β⦎σ ⟶ ⦍β⦎(~σ)] ⊢[T₀]! ⦍β⦎σ := FiniteContext.by_axm!;
  have d₂ : [⦍β⦎σ, ⦍β⦎σ ⟶ ⦍β⦎(~σ)] ⊢[T₀]! ⦍β⦎σ ⟶ ⦍β⦎(~σ) := FiniteContext.by_axm!;
  have d₃ : [⦍β⦎σ, ⦍β⦎σ ⟶ ⦍β⦎(~σ)] ⊢[T₀]! ⦍β⦎(~σ) := d₂ ⨀ d₁;
  exact ((FiniteContext.of'! this) ⨀ d₁) ⨀ d₃;

/-- Formalized First Incompleteness Theorem -/
theorem formalized_unprovable_goedel : T ⊢! Con⦍β⦎ ⟶ ~⦍β⦎γ := by
  have h₁ : T₀ ⊢! ⦍β⦎γ ⟶ ⦍β⦎⦍β⦎γ := D3;
  have h₂ : T ⊢! ⦍β⦎γ ⟶ ~γ := Subtheory.prf! $ contra₁'! $ and₁'! goedel_spec;
  have h₃ : T₀ ⊢! ⦍β⦎⦍β⦎γ ⟶ ⦍β⦎(~γ) := prov_distribute_imply h₂;
  exact Subtheory.prf! $ contra₀'! $ consistency_lemma_2 ⨀ (imp_trans''! h₁ h₃);

theorem iff_goedel_consistency : T ⊢! γ ⟷ Con⦍β⦎
  := iff_trans''! goedel_specAux₁ $ iff_intro! (Subtheory.prf! (𝓢 := T₀) formalized_consistent_of_existance_unprovable) formalized_unprovable_goedel

theorem unprovable_consistency [System.Consistent T] : T ⊬! Con⦍β⦎
  := unprovable_iff! iff_goedel_consistency |>.mp $ unprovable_goedel (T₀ := T₀)

theorem unrefutable_consistency [System.Consistent T] [β.GoedelSound T₀ T] : T ⊬! ~Con⦍β⦎
  := unprovable_iff! (neg_replace_iff'! $ iff_goedel_consistency) |>.mp $ unrefutable_goedel (T₀ := T₀)

end Second


section Loeb

def kreisel
  (T₀ T : Theory L) [Diagonalization T₀]
  (β : ProvabilityPredicate L L) [β.HilbertBernays T₀ T]
  (σ : Sentence L) : Sentence L := fixpoint T₀ “x | !β.prov x → !σ”
local notation "κ(" σ ")" => kreisel T₀ T β σ

section KrieselSentence

variable [β.HilbertBernays T₀ T]

lemma kreisel_spec (σ : Sentence L) : T₀ ⊢! κ(σ) ⟷ (⦍β⦎(κ(σ)) ⟶ σ) := by
  convert (diag (T := T₀) “x | !β.prov x → !σ”);
  simp [kreisel, ←Rew.hom_comp_app, Rew.substs_comp_substs];
  rfl;

private lemma kreisel_specAux₁ (σ : Sentence L) : T₀ ⊢! ⦍β⦎κ(σ) ⟶ ⦍β⦎σ := (imp_trans''! (D2 ⨀ (D1 (Subtheory.prf! $ and₁'! (kreisel_spec σ)))) D2) ⨀₁ D3

private lemma kreisel_specAux₂ (σ : Sentence L) : T₀ ⊢! (⦍β⦎κ(σ) ⟶ σ) ⟶ κ(σ) := and₂'! (kreisel_spec σ)

end KrieselSentence

theorem loeb_theorm [β.HilbertBernays T₀ T] (H : T ⊢! ⦍β⦎σ ⟶ σ) : T ⊢! σ := by
  have d₁ : T ⊢! ⦍β⦎κ(σ) ⟶ σ := imp_trans''! (Subtheory.prf! (kreisel_specAux₁ σ)) H;
  have d₂ : T ⊢! ⦍β⦎κ(σ)      := Subtheory.prf! (𝓢 := T₀) (D1 $ Subtheory.prf! (kreisel_specAux₂ σ) ⨀ d₁);
  exact d₁ ⨀ d₂;

instance [β.HilbertBernays T₀ T] : Loeb β T₀ T := ⟨loeb_theorm (T₀ := T₀) (T := T)⟩


theorem formalized_loeb_theorem [β.HilbertBernays T₀ T] : T₀ ⊢! ⦍β⦎(⦍β⦎σ ⟶ σ) ⟶ ⦍β⦎σ := by
  have hκ₁ : T₀ ⊢! ⦍β⦎(κ(σ)) ⟶ ⦍β⦎σ := kreisel_specAux₁ σ;
  have : T₀ ⊢! (⦍β⦎σ ⟶ σ) ⟶ (⦍β⦎κ(σ) ⟶ σ) := replace_imply_left! hκ₁;
  have : T ⊢! (⦍β⦎σ ⟶ σ) ⟶ κ(σ) := Subtheory.prf! (𝓢 := T₀) $ imp_trans''! this (kreisel_specAux₂ σ);
  exact imp_trans''! (D2 ⨀ (D1 this)) hκ₁;

instance [β.HilbertBernays T₀ T] : FormalizedLoeb β T₀ T := ⟨formalized_loeb_theorem (T₀ := T₀) (T := T)⟩


variable [System.Consistent T]

lemma unprovable_consistency_via_loeb [β.Loeb T₀ T] : T ⊬! Con⦍β⦎ := by
  by_contra hC;
  have : T ⊢! ⊥ := Loeb.LT T₀ $ neg_equiv'!.mp hC;
  have := not_consistent_iff_inconsistent.mpr $ inconsistent_iff_provable_bot.mpr this;
  contradiction;

lemma formalized_unprovable_not_consistency [β.HilbertBernays T₀ T] [β.GoedelSound T₀ T]
  : T ⊬! Con⦍β⦎ ⟶ ~⦍β⦎(~Con⦍β⦎) := by
  by_contra hC;
  have : T ⊢! ~Con⦍β⦎ := Loeb.LT T₀ $ contra₁'! hC;
  have : T ⊬! ~Con⦍β⦎ := unrefutable_consistency (T₀ := T₀);
  contradiction;

lemma formalized_unrefutable_goedel [β.HilbertBernays T₀ T] [β.GoedelSound T₀ T]
  : T ⊬! Con⦍β⦎ ⟶ ~⦍β⦎(~γ) := by
  by_contra hC;
  have : T ⊬! Con⦍β⦎ ⟶ ~⦍β⦎(~Con⦍β⦎)  := formalized_unprovable_not_consistency (T₀ := T₀);
  have : T ⊢! Con⦍β⦎ ⟶ ~⦍β⦎(~Con⦍β⦎) := imp_trans''! hC $ Subtheory.prf! $ and₁'! $ neg_replace_iff'! $ prov_distribute_iff (T₀ := T₀) $ neg_replace_iff'! $ iff_goedel_consistency;
  contradiction;

end Loeb


abbrev rosser
  (T₀ T : Theory L) [Diagonalization T₀]
  (β : ProvabilityPredicate L L) [β.HilbertBernays₁ T₀ T] [β.Rosser T₀ T] : Sentence L
  := fixpoint T₀ “x | ¬!β.prov x”
local notation "ρ" => rosser T₀ T β

section RosserSentence

variable [β.HilbertBernays₁ T₀ T] [β.Rosser T₀ T]

lemma rosser_spec : T₀ ⊢! ρ ⟷ ~⦍β⦎ρ := goedel_spec

private lemma rosser_specAux₁ : T ⊢! ρ ⟷ ~⦍β⦎ρ := goedel_specAux₁

end RosserSentence

section

variable [System.Consistent T] [β.HilbertBernays₁ T₀ T] [β.Rosser T₀ T]

lemma unprovable_rosser : T ⊬! ρ := unprovable_goedel

theorem unrefutable_rosser : T ⊬! ~ρ := by
  intro hnρ;
  have hρ : T ⊢! ρ := Subtheory.prf! $ (and₂'! rosser_spec) ⨀ (Ro hnρ);
  have := not_consistent_iff_inconsistent.mpr $ inconsistent_iff_provable_bot.mpr $ (neg_equiv'!.mp hnρ) ⨀ hρ;
  contradiction;

theorem rosser_independent : System.Undecidable T ρ := by
  suffices T ⊬! ρ ∧ T ⊬! ~ρ by simpa [System.Undecidable, not_or] using this;
  constructor;
  . apply unprovable_rosser;
  . apply unrefutable_rosser;

theorem rosser_first_incompleteness : ¬System.Complete T
  := System.incomplete_iff_exists_undecidable.mpr ⟨ρ, rosser_independent⟩

/-- If `β` satisfies Rosser provability condition, then `Con⦍β⦎` is provable in `T`. -/
theorem kriesel_remark : T ⊢! Con⦍β⦎ := by
  have : T₀ ⊢! ~⦍β⦎(⊥) := Ro (neg_equiv'!.mpr (by simp));
  exact Subtheory.prf! $ this;

end


end DerivabilityCondition

end LO.FirstOrder
