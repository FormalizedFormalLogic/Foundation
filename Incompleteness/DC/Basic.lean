import Logic.FirstOrder.Arith.Theory
import Logic.Logic.HilbertStyle.Supplemental

namespace LO.FirstOrder

namespace Theory.Alt

variable {L : Language} {T U : Theory L}

instance [s : T ≼ U] : T ≼ U.alt.thy := s

instance [s : T ≼ U] : T.alt ≼ U.alt := ⟨fun b ↦ s.prf b⟩

end Theory.Alt

namespace DerivabilityCondition

structure ProvabilityPredicate (L₀ L : Language) where
  prov : Semisentence L₀ 1

namespace ProvabilityPredicate

variable [Semiterm.Operator.GoedelNumber L₀ (Sentence L)]

def pr (𝔟 : ProvabilityPredicate L₀ L) (σ : Sentence L) : Semisentence L₀ n := 𝔟.prov/[⌜σ⌝]

notation "⦍" 𝔟 "⦎" σ:80 => pr 𝔟 σ

end ProvabilityPredicate

class Diagonalization
  [Semiterm.Operator.GoedelNumber L (Sentence L)]
  (T : Theory L) where
  fixpoint : Semisentence L 1 → Sentence L
  diag (θ) : T ⊢!. fixpoint θ ⟷ θ/[⌜fixpoint θ⌝]

section Consistency

def consistency [Semiterm.Operator.GoedelNumber L₀ (Sentence L)] (𝔟 : ProvabilityPredicate L₀ L) : Sentence L₀ := ~⦍𝔟⦎⊥
notation "Con⦍" 𝔟 "⦎" => consistency 𝔟

end Consistency

namespace ProvabilityPredicate

class Conservative
  [Semiterm.Operator.GoedelNumber L₀ (Sentence L)]
  (𝔟 : ProvabilityPredicate L₀ L) (T₀ : Theory L₀) (T : outParam (Theory L)) where
  iff (σ : Sentence L) : T ⊢!. σ ↔ T₀ ⊢!. ⦍𝔟⦎σ

variable [Semiterm.Operator.GoedelNumber L (Sentence L)]

class HBL1 (𝔟 : ProvabilityPredicate L L) (T₀ : Theory L) (T : outParam (Theory L)) where
  D1 {σ : Sentence L} : T ⊢!. σ → T₀ ⊢!. ⦍𝔟⦎σ

class HBL2 (𝔟 : ProvabilityPredicate L L) (T₀ : Theory L) (T : outParam (Theory L)) where
  D2 {σ τ : Sentence L} : T₀ ⊢!. ⦍𝔟⦎(σ ⟶ τ) ⟶ ⦍𝔟⦎σ ⟶ ⦍𝔟⦎τ

class HBL3 (𝔟 : ProvabilityPredicate L L) (T₀ : Theory L) (T : outParam (Theory L)) where
  D3 {σ : Sentence L} : T₀ ⊢!. ⦍𝔟⦎σ ⟶ ⦍𝔟⦎⦍𝔟⦎σ

class HBL (𝔟 : ProvabilityPredicate L L) (T₀ : Theory L) (T : outParam (Theory L)) extends
  𝔟.HBL1 T₀ T, 𝔟.HBL2 T₀ T, 𝔟.HBL3 T₀ T

class Loeb (𝔟 : ProvabilityPredicate L L) (T₀ : Theory L) (T : outParam (Theory L)) where
  LT {σ : Sentence L} : T ⊢!. ⦍𝔟⦎σ ⟶ σ → T ⊢!. σ

class FormalizedLoeb (𝔟 : ProvabilityPredicate L L) (T₀ : Theory L) (T : outParam (Theory L)) where
  FLT {σ : Sentence L} : T₀ ⊢!. ⦍𝔟⦎(⦍𝔟⦎σ ⟶ σ) ⟶ ⦍𝔟⦎σ

class Rosser (𝔟 : ProvabilityPredicate L L) (T₀ : Theory L) (T : outParam (Theory L)) where
  Ro {σ : Sentence L} : T ⊢!. ~σ → T₀ ⊢!. ~⦍𝔟⦎(σ)

section

open LO.System

variable [DecidableEq (Sentence L)] [Semiterm.Operator.GoedelNumber L (Sentence L)]
         {𝔟 : ProvabilityPredicate L L}
         {T₀ T : Theory L} [T₀ ≼ T]
         [𝔟.HBL T₀ T]
         {σ τ : Sentence L}

alias D1 := HBL1.D1
alias D2 := HBL2.D2
alias D3 := HBL3.D3
alias LT := Loeb.LT
alias FLT := FormalizedLoeb.FLT
alias Ro := Rosser.Ro

def D1s [HBL1 𝔟 T₀ T]: T ⊢!. σ → T ⊢!. ⦍𝔟⦎σ := by
  intro h;
  apply System.Subtheory.prf! (𝓢 := T₀);
  apply D1 h;

def D2s [HBL2 𝔟 T₀ T] : T ⊢!. ⦍𝔟⦎(σ ⟶ τ) ⟶ ⦍𝔟⦎σ ⟶ ⦍𝔟⦎τ := by
  apply System.Subtheory.prf! (𝓢 := T₀);
  apply D2;

def D2' [HBL 𝔟 T₀ T] [System.ModusPonens T] : T₀ ⊢!. ⦍𝔟⦎(σ ⟶ τ) → T₀ ⊢!. ⦍𝔟⦎σ ⟶ ⦍𝔟⦎τ := by
  intro h;
  exact D2 ⨀ h;

def D3s [HBL3 𝔟 T₀ T] : T ⊢!. ⦍𝔟⦎σ ⟶ ⦍𝔟⦎⦍𝔟⦎σ := by
  apply System.Subtheory.prf! (𝓢 := T₀);
  apply D3;

def prov_distribute_imply (h : T ⊢!. σ ⟶ τ) : T₀ ⊢!. ⦍𝔟⦎σ ⟶ ⦍𝔟⦎τ := D2' $ D1 h

def prov_distribute_iff (h : T ⊢!. σ ⟷ τ) : T₀ ⊢!. ⦍𝔟⦎σ ⟷ ⦍𝔟⦎τ := by
  apply iff_intro!;
  . exact prov_distribute_imply $ and₁'! h;
  . exact prov_distribute_imply $ and₂'! h;

def prov_distribute_and : T₀ ⊢!. ⦍𝔟⦎(σ ⋏ τ) ⟶ ⦍𝔟⦎σ ⋏ ⦍𝔟⦎τ := by
  have h₁ : T₀ ⊢!. ⦍𝔟⦎(σ ⋏ τ) ⟶ ⦍𝔟⦎σ := D2' <| D1 and₁!;
  have h₂ : T₀ ⊢!. ⦍𝔟⦎(σ ⋏ τ) ⟶ ⦍𝔟⦎τ := D2' <| D1 and₂!;
  exact imply_right_and! h₁ h₂;

def prov_distribute_and! : T₀ ⊢!. ⦍𝔟⦎(σ ⋏ τ) → T₀ ⊢!. ⦍𝔟⦎σ ⋏ ⦍𝔟⦎τ := λ h => prov_distribute_and ⨀ h

def prov_collect_and : T₀ ⊢!. ⦍𝔟⦎σ ⋏ ⦍𝔟⦎τ ⟶ ⦍𝔟⦎(σ ⋏ τ) := by
  have h₁ : T₀ ⊢!. ⦍𝔟⦎σ ⟶ ⦍𝔟⦎(τ ⟶ σ ⋏ τ) := prov_distribute_imply $ and₃!;
  have h₂ : T₀ ⊢!. ⦍𝔟⦎(τ ⟶ σ ⋏ τ) ⟶ ⦍𝔟⦎τ ⟶ ⦍𝔟⦎(σ ⋏ τ) := D2;
  apply and_imply_iff_imply_imply'!.mpr;
  exact imp_trans''! h₁ h₂;

end

end ProvabilityPredicate

variable [DecidableEq (Sentence L)] [Semiterm.Operator.GoedelNumber L (Sentence L)]
         {𝔟 : ProvabilityPredicate L L}
         {T₀ T : Theory L} [T₀ ≼ T] [Diagonalization T₀]
         [𝔟.HBL T₀ T]
         {σ τ : Sentence L}

open LO.System
open Diagonalization
open ProvabilityPredicate

abbrev goedel
  (T₀ T : Theory L) [Diagonalization T₀]
  (𝔟 : ProvabilityPredicate L L) [𝔟.HBL1 T₀ T] : Sentence L
  := fixpoint T₀ “x. ¬!𝔟.prov x”
local notation "γ" => goedel T₀ T 𝔟

section GoedelSentence

variable [𝔟.HBL1 T₀ T]

lemma goedel_spec : T₀ ⊢!. γ ⟷ ~⦍𝔟⦎γ := by
  convert (diag (T := T₀) “x. ¬!𝔟.prov x”);
  simp [goedel, ←Rew.hom_comp_app, Rew.substs_comp_substs];
  rfl;

private lemma goedel_specAux₁ : T ⊢!. γ ⟷ ~⦍𝔟⦎γ := Subtheory.prf! (𝓢 := T₀) goedel_spec

private lemma goedel_specAux₂ : T ⊢!. ~γ ⟶ ⦍𝔟⦎γ := contra₂'! $ and₂'! goedel_specAux₁

end GoedelSentence

class ProvabilityPredicate.GoedelSound (𝔟 : ProvabilityPredicate L L) (T₀ T) [Diagonalization T₀] [𝔟.HBL1 T₀ T] where
  γ_sound : T ⊢!. ⦍𝔟⦎(goedel T₀ T 𝔟) → T ⊢!. (goedel T₀ T 𝔟)

open GoedelSound


section First

variable [System.Consistent T] [𝔟.HBL1 T₀ T]

theorem unprovable_goedel : T ⊬!. γ := by
  intro h;
  have h₁ : T ⊢!. ⦍𝔟⦎γ := D1s (T₀ := T₀) h;
  have h₂ : T ⊢!. ~⦍𝔟⦎γ := (and₁'! goedel_specAux₁) ⨀ h;
  have : T ⊢!. ⊥ := (neg_equiv'!.mp h₂) ⨀ h₁;
  have : ¬Consistent T := not_consistent_iff_inconsistent.mpr <|
    inconsistent_iff_provable_bot.mpr (by simpa [provable₀_iff] using this)
  contradiction;

theorem unrefutable_goedel [𝔟.GoedelSound T₀ T] : T ⊬!. ~γ := by
  intro h₂;
  have h₁ : T ⊢!. γ := γ_sound $ goedel_specAux₂ ⨀ h₂;
  have : T ⊢!. ⊥ := (neg_equiv'!.mp h₂) ⨀ h₁;
  have : ¬Consistent T := not_consistent_iff_inconsistent.mpr <|
    inconsistent_iff_provable_bot.mpr (by simpa [provable₀_iff] using this);
  contradiction;

theorem goedel_independent [𝔟.GoedelSound T₀ T] : System.Undecidable T ↑γ := by
  suffices T ⊬!. γ ∧ T ⊬!. ~γ by simpa [System.Undecidable, not_or, unprovable₀_iff] using this
  constructor
  . apply unprovable_goedel
  . apply unrefutable_goedel

theorem first_incompleteness [𝔟.GoedelSound T₀ T]
  : ¬System.Complete T := System.incomplete_iff_exists_undecidable.mpr ⟨γ, goedel_independent⟩

end First


section Second

variable [Diagonalization T] [𝔟.HBL T₀ T]

lemma formalized_consistent_of_existance_unprovable : T₀ ⊢!. ~⦍𝔟⦎σ ⟶ Con⦍𝔟⦎ := contra₀'! $ D2 ⨀ (D1 efq!)

private lemma consistency_lemma_1 [T₀ ≼ U] [𝔟.HBL T₀ U] : (U ⊢!. Con⦍𝔟⦎ ⟶ ~⦍𝔟⦎σ) ↔ (U ⊢!. ⦍𝔟⦎σ ⟶ ⦍𝔟⦎(~σ)) := by
  constructor;
  . intro H;
    exact contra₃'! $ imp_trans''! (Subtheory.prf! (𝓢 := T₀) formalized_consistent_of_existance_unprovable) H;
  . intro H
    apply contra₀'!
    have : T₀ ⊢!. ⦍𝔟⦎σ ⋏ ⦍𝔟⦎(~σ) ⟶ ⦍𝔟⦎⊥ := imp_trans''! prov_collect_and $ prov_distribute_imply lac!;
    have : U ⊢!. ⦍𝔟⦎σ ⟶ ⦍𝔟⦎(~σ) ⟶ ⦍𝔟⦎⊥ := Subtheory.prf! $ and_imply_iff_imply_imply'!.mp $ this;
    exact this ⨀₁ H;

private lemma consistency_lemma_2 : T₀ ⊢!. (⦍𝔟⦎σ ⟶ ⦍𝔟⦎(~σ)) ⟶ ⦍𝔟⦎σ ⟶ ⦍𝔟⦎⊥ := by
  have : T ⊢!. σ ⟶ ~σ ⟶ ⊥ := and_imply_iff_imply_imply'!.mp lac!
  have : T₀ ⊢!. ⦍𝔟⦎σ ⟶ ⦍𝔟⦎(~σ ⟶ ⊥)  := prov_distribute_imply this;
  have : T₀ ⊢!. ⦍𝔟⦎σ ⟶ (⦍𝔟⦎(~σ) ⟶ ⦍𝔟⦎⊥) := imp_trans''! this D2;

  -- TODO: more simple proof
  apply FiniteContext.deduct'!;
  apply FiniteContext.deduct!;
  have d₁ : [⦍𝔟⦎σ, ⦍𝔟⦎σ ⟶ ⦍𝔟⦎(~σ)] ⊢[T₀.alt]! ⦍𝔟⦎σ := FiniteContext.by_axm!;
  have d₂ : [⦍𝔟⦎σ, ⦍𝔟⦎σ ⟶ ⦍𝔟⦎(~σ)] ⊢[T₀.alt]! ⦍𝔟⦎σ ⟶ ⦍𝔟⦎(~σ) := FiniteContext.by_axm!;
  have d₃ : [⦍𝔟⦎σ, ⦍𝔟⦎σ ⟶ ⦍𝔟⦎(~σ)] ⊢[T₀.alt]! ⦍𝔟⦎(~σ) := d₂ ⨀ d₁;
  exact ((FiniteContext.of'! this) ⨀ d₁) ⨀ d₃;

/-- Formalized First Incompleteness Theorem -/
theorem formalized_unprovable_goedel : T ⊢!. Con⦍𝔟⦎ ⟶ ~⦍𝔟⦎γ := by
  have h₁ : T₀ ⊢!. ⦍𝔟⦎γ ⟶ ⦍𝔟⦎⦍𝔟⦎γ := D3;
  have h₂ : T ⊢!. ⦍𝔟⦎γ ⟶ ~γ := Subtheory.prf! $ contra₁'! $ and₁'! goedel_spec;
  have h₃ : T₀ ⊢!. ⦍𝔟⦎⦍𝔟⦎γ ⟶ ⦍𝔟⦎(~γ) := prov_distribute_imply h₂;
  exact Subtheory.prf! $ contra₀'! $ consistency_lemma_2 ⨀ (imp_trans''! h₁ h₃);

theorem iff_goedel_consistency : T ⊢!. γ ⟷ Con⦍𝔟⦎
  := iff_trans''! goedel_specAux₁ $ iff_intro! (Subtheory.prf! (𝓢 := T₀) formalized_consistent_of_existance_unprovable) formalized_unprovable_goedel

theorem unprovable_consistency [System.Consistent T] : T ⊬!. Con⦍𝔟⦎
  := unprovable_iff! iff_goedel_consistency |>.mp $ unprovable_goedel (T₀ := T₀)

theorem unrefutable_consistency [System.Consistent T] [𝔟.GoedelSound T₀ T] : T ⊬!. ~Con⦍𝔟⦎
  := unprovable_iff! (neg_replace_iff'! $ iff_goedel_consistency) |>.mp $ unrefutable_goedel (T₀ := T₀)

end Second


section Loeb

def kreisel
  (T₀ T : Theory L) [Diagonalization T₀]
  (𝔟 : ProvabilityPredicate L L) [𝔟.HBL T₀ T]
  (σ : Sentence L) : Sentence L := fixpoint T₀ “x. !𝔟.prov x → !σ”
local notation "κ(" σ ")" => kreisel T₀ T 𝔟 σ

section KrieselSentence

variable [𝔟.HBL T₀ T]

lemma kreisel_spec (σ : Sentence L) : T₀ ⊢!. κ(σ) ⟷ (⦍𝔟⦎(κ(σ)) ⟶ σ) := by
  convert (diag (T := T₀) “x. !𝔟.prov x → !σ”);
  simp [kreisel, ←Rew.hom_comp_app, Rew.substs_comp_substs];
  rfl;

private lemma kreisel_specAux₁ (σ : Sentence L) : T₀ ⊢!. ⦍𝔟⦎κ(σ) ⟶ ⦍𝔟⦎σ := (imp_trans''! (D2 ⨀ (D1 (Subtheory.prf! $ and₁'! (kreisel_spec σ)))) D2) ⨀₁ D3

private lemma kreisel_specAux₂ (σ : Sentence L) : T₀ ⊢!. (⦍𝔟⦎κ(σ) ⟶ σ) ⟶ κ(σ) := and₂'! (kreisel_spec σ)

end KrieselSentence

theorem loeb_theorm [𝔟.HBL T₀ T] (H : T ⊢!. ⦍𝔟⦎σ ⟶ σ) : T ⊢!. σ := by
  have d₁ : T ⊢!. ⦍𝔟⦎κ(σ) ⟶ σ := imp_trans''! (Subtheory.prf! (kreisel_specAux₁ σ)) H;
  have d₂ : T ⊢!. ⦍𝔟⦎κ(σ)      := Subtheory.prf! (𝓢 := T₀) (D1 $ Subtheory.prf! (kreisel_specAux₂ σ) ⨀ d₁);
  exact d₁ ⨀ d₂;

instance [𝔟.HBL T₀ T] : Loeb 𝔟 T₀ T := ⟨loeb_theorm (T₀ := T₀) (T := T)⟩


theorem formalized_loeb_theorem [𝔟.HBL T₀ T] : T₀ ⊢!. ⦍𝔟⦎(⦍𝔟⦎σ ⟶ σ) ⟶ ⦍𝔟⦎σ := by
  have hκ₁ : T₀ ⊢!. ⦍𝔟⦎(κ(σ)) ⟶ ⦍𝔟⦎σ := kreisel_specAux₁ σ;
  have : T₀ ⊢!. (⦍𝔟⦎σ ⟶ σ) ⟶ (⦍𝔟⦎κ(σ) ⟶ σ) := replace_imply_left! hκ₁;
  have : T ⊢!. (⦍𝔟⦎σ ⟶ σ) ⟶ κ(σ) := Subtheory.prf! (𝓢 := T₀) $ imp_trans''! this (kreisel_specAux₂ σ);
  exact imp_trans''! (D2 ⨀ (D1 this)) hκ₁;

instance [𝔟.HBL T₀ T] : FormalizedLoeb 𝔟 T₀ T := ⟨formalized_loeb_theorem (T₀ := T₀) (T := T)⟩


variable [System.Consistent T]

lemma unprovable_consistency_via_loeb [𝔟.Loeb T₀ T] : T ⊬!. Con⦍𝔟⦎ := by
  by_contra hC;
  have : T ⊢!. ⊥ := Loeb.LT T₀ $ neg_equiv'!.mp hC;
  have : ¬Consistent T := not_consistent_iff_inconsistent.mpr $ inconsistent_iff_provable_bot.mpr (by simpa [provable₀_iff] using this)
  contradiction

lemma formalized_unprovable_not_consistency [𝔟.HBL T₀ T] [𝔟.GoedelSound T₀ T]
  : T ⊬!. Con⦍𝔟⦎ ⟶ ~⦍𝔟⦎(~Con⦍𝔟⦎) := by
  by_contra hC;
  have : T ⊢!. ~Con⦍𝔟⦎ := Loeb.LT T₀ $ contra₁'! hC;
  have : T ⊬!. ~Con⦍𝔟⦎ := unrefutable_consistency (T₀ := T₀);
  contradiction;

lemma formalized_unrefutable_goedel [𝔟.HBL T₀ T] [𝔟.GoedelSound T₀ T]
  : T ⊬!. Con⦍𝔟⦎ ⟶ ~⦍𝔟⦎(~γ) := by
  by_contra hC;
  have : T ⊬!. Con⦍𝔟⦎ ⟶ ~⦍𝔟⦎(~Con⦍𝔟⦎)  := formalized_unprovable_not_consistency (T₀ := T₀);
  have : T ⊢!. Con⦍𝔟⦎ ⟶ ~⦍𝔟⦎(~Con⦍𝔟⦎) := imp_trans''! hC $ Subtheory.prf! $ and₁'! $ neg_replace_iff'! $ prov_distribute_iff (T₀ := T₀) $ neg_replace_iff'! $ iff_goedel_consistency;
  contradiction;

end Loeb


abbrev rosser
  (T₀ T : Theory L) [Diagonalization T₀]
  (𝔟 : ProvabilityPredicate L L) [𝔟.HBL1 T₀ T] [𝔟.Rosser T₀ T] : Sentence L
  := fixpoint T₀ “x. ¬!𝔟.prov x”
local notation "ρ" => rosser T₀ T 𝔟

section RosserSentence

variable [𝔟.HBL1 T₀ T] [𝔟.Rosser T₀ T]

lemma rosser_spec : T₀ ⊢!. ρ ⟷ ~⦍𝔟⦎ρ := goedel_spec

private lemma rosser_specAux₁ : T ⊢!. ρ ⟷ ~⦍𝔟⦎ρ := goedel_specAux₁

end RosserSentence

section

variable [System.Consistent T] [𝔟.HBL1 T₀ T] [𝔟.Rosser T₀ T]

lemma unprovable_rosser : T ⊬!. ρ := unprovable_goedel

theorem unrefutable_rosser : T ⊬!. ~ρ := by
  intro hnρ;
  have hρ : T ⊢!. ρ := Subtheory.prf! $ (and₂'! rosser_spec) ⨀ (Ro hnρ);
  have : ¬Consistent T := not_consistent_iff_inconsistent.mpr $ inconsistent_iff_provable_bot.mpr <|
    by simpa [provable₀_iff] using (neg_equiv'!.mp hnρ) ⨀ hρ;
  contradiction

theorem rosser_independent : System.Undecidable T ↑ρ := by
  suffices T ⊬!. ρ ∧ T ⊬!. ~ρ by simpa [System.Undecidable, not_or, unprovable₀_iff] using this;
  constructor
  . apply unprovable_rosser
  . apply unrefutable_rosser

theorem rosser_first_incompleteness : ¬System.Complete T
  := System.incomplete_iff_exists_undecidable.mpr ⟨ρ, rosser_independent⟩

/-- If `𝔟` satisfies Rosser provability condition, then `Con⦍𝔟⦎` is provable in `T`. -/
theorem kriesel_remark : T ⊢!. Con⦍𝔟⦎ := by
  have : T₀ ⊢!. ~⦍𝔟⦎(⊥) := Ro (neg_equiv'!.mpr (by simp));
  exact Subtheory.prf! $ this;

end


end DerivabilityCondition

end LO.FirstOrder
