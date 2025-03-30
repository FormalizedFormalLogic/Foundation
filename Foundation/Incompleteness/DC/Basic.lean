import Foundation.FirstOrder.Arith.Theory
import Foundation.Logic.HilbertStyle.Supplemental
import Foundation.Incompleteness.ToFoundation.Basic

namespace LO.FirstOrder

namespace Theory.Alt

variable {L : Language} {T U : Theory L}

instance [s : T ⪯ U] : T ⪯ U.alt.thy := s

instance [s : T ⪯ U] : T.alt ⪯ U.alt := ⟨fun _ b ↦ s.pbl b⟩

end Theory.Alt


namespace DerivabilityCondition

variable [Semiterm.Operator.GoedelNumber L (Sentence L)]

structure ProvabilityPredicate (T₀ : Theory L) (T : Theory L) where
  prov : Semisentence L 1
  protected D1 {σ : Sentence L} : T ⊢!. σ → T₀ ⊢!. prov/[⌜σ⌝]

namespace ProvabilityPredicate

variable {T₀ T : Theory L}

@[coe] def pr (𝔅 : ProvabilityPredicate T₀ T) (σ : Sentence L) : Sentence L := 𝔅.prov/[⌜σ⌝]

instance : CoeFun (ProvabilityPredicate T₀ T) (fun _ => Sentence L → Sentence L) := ⟨pr⟩

def con (𝔅 : ProvabilityPredicate T₀ T) : Sentence L := ∼(𝔅 ⊥)

end ProvabilityPredicate

class Diagonalization (T : Theory L) where
  fixpoint : Semisentence L 1 → Sentence L
  diag (θ) : T ⊢!. fixpoint θ ⭤ θ/[⌜fixpoint θ⌝]

namespace ProvabilityPredicate

variable {T₀ T : Theory L}

class HBL2 (𝔅 : ProvabilityPredicate T₀ T) where
  protected D2 {σ τ : Sentence L} : T₀ ⊢!. 𝔅 (σ ➝ τ) ➝ (𝔅 σ) ➝ (𝔅 τ)

class HBL3 (𝔅 : ProvabilityPredicate T₀ T) where
  protected D3 {σ : Sentence L} : T₀ ⊢!. (𝔅 σ) ➝ 𝔅 (𝔅 σ)

class HBL (𝔅 : ProvabilityPredicate T₀ T) extends 𝔅.HBL2, 𝔅.HBL3

class Loeb (𝔅 : ProvabilityPredicate T₀ T) where
  protected LT {σ : Sentence L} : T ⊢!. (𝔅 σ) ➝ σ → T ⊢!. σ

class FormalizedLoeb (𝔅 : ProvabilityPredicate T₀ T) where
  protected FLT {σ : Sentence L} : T₀ ⊢!. 𝔅 ((𝔅 σ) ➝ σ) ➝ (𝔅 σ)

class Rosser (𝔅 : ProvabilityPredicate T₀ T) where
  protected Ro {σ : Sentence L} : T ⊢!. ∼σ → T₀ ⊢!. ∼(𝔅 σ)

section

open LO.Entailment

variable {T₀ T : Theory L}
         {𝔅 : ProvabilityPredicate T₀ T}
         {σ τ : Sentence L}

protected alias D2 := HBL2.D2
protected alias D3 := HBL3.D3
protected alias LT := Loeb.LT
protected alias FLT := FormalizedLoeb.FLT
protected alias Ro := Rosser.Ro

lemma D1_shift [T₀ ⪯ T] : T ⊢!. σ → T ⊢!. (𝔅 σ) := by
  intro h;
  apply Entailment.WeakerThan.pbl (𝓢 := T₀.alt);
  apply 𝔅.D1 h;

lemma D2_shift [T₀ ⪯ T] [𝔅.HBL2] : T ⊢!. 𝔅 (σ ➝ τ) ➝ (𝔅 σ) ➝ (𝔅 τ) := by
  apply Entailment.WeakerThan.pbl (𝓢 := T₀.alt);
  apply 𝔅.D2;

lemma D3_shift [T₀ ⪯ T] [𝔅.HBL3] : T ⊢!. (𝔅 σ) ➝ 𝔅 (𝔅 σ) := by
  apply Entailment.WeakerThan.pbl (𝓢 := T₀.alt);
  apply 𝔅.D3;

lemma FLT_shift [T₀ ⪯ T] [𝔅.FormalizedLoeb] : T ⊢!. 𝔅 ((𝔅 σ) ➝ σ) ➝ (𝔅 σ) := by
  apply Entailment.WeakerThan.pbl (𝓢 := T₀.alt);
  apply 𝔅.FLT;

lemma D2' [𝔅.HBL2] [Entailment.ModusPonens T] : T₀ ⊢!. 𝔅 (σ ➝ τ) → T₀ ⊢!. (𝔅 σ) ➝ (𝔅 τ) := by
  intro h;
  exact 𝔅.D2 ⨀ h;

lemma prov_distribute_imply [𝔅.HBL2] (h : T ⊢!. σ ➝ τ) : T₀ ⊢!. (𝔅 σ) ➝ (𝔅 τ) := 𝔅.D2' $ 𝔅.D1 h

lemma prov_distribute_imply' [T₀ ⪯ T] [𝔅.HBL2] (h : T₀ ⊢!. σ ➝ τ) : T₀ ⊢!. (𝔅 σ) ➝ (𝔅 τ) := prov_distribute_imply $ WeakerThan.pbl h

lemma prov_distribute_iff [𝔅.HBL2] (h : T ⊢!. σ ⭤ τ) : T₀ ⊢!. (𝔅 σ) ⭤ (𝔅 τ) := by
  apply e!_intro;
  . exact prov_distribute_imply $ of_k!_left h;
  . exact prov_distribute_imply $ of_k_right h;

lemma prov_distribute_and  [𝔅.HBL2] [DecidableEq (Sentence L)] : T₀ ⊢!. 𝔅 (σ ⋏ τ) ➝ (𝔅 σ) ⋏ (𝔅 τ) := by
  have h₁ : T₀ ⊢!. 𝔅 (σ ⋏ τ) ➝ (𝔅 σ) := 𝔅.D2' <| 𝔅.D1 and₁!;
  have h₂ : T₀ ⊢!. 𝔅 (σ ⋏ τ) ➝ (𝔅 τ) := 𝔅.D2' <| 𝔅.D1 and₂!;
  exact imply_right_and! h₁ h₂;

def prov_distribute_and' [𝔅.HBL2] [DecidableEq (Sentence L)] : T₀ ⊢!. 𝔅 (σ ⋏ τ) → T₀ ⊢!. (𝔅 σ) ⋏ (𝔅 τ) := λ h => prov_distribute_and ⨀ h

def prov_collect_and [𝔅.HBL2] [DecidableEq (Sentence L)] : T₀ ⊢!. (𝔅 σ) ⋏ (𝔅 τ) ➝ 𝔅 (σ ⋏ τ) := by
  have h₁ : T₀ ⊢!. (𝔅 σ) ➝ 𝔅 (τ ➝ σ ⋏ τ) := prov_distribute_imply $ and₃!;
  have h₂ : T₀ ⊢!. 𝔅 (τ ➝ σ ⋏ τ) ➝ (𝔅 τ) ➝ 𝔅 (σ ⋏ τ) := 𝔅.D2;
  apply cK!_iff_cC!.mpr;
  exact c!_trans h₁ h₂;

end

end ProvabilityPredicate

variable {T₀ T : Theory L} {𝔅 : ProvabilityPredicate T₀ T}

open LO.Entailment
open Diagonalization
open ProvabilityPredicate

def ProvabilityPredicate.goedel [Diagonalization T₀] (𝔅 : ProvabilityPredicate T₀ T) : Sentence L :=
  fixpoint T₀ “x. ¬!𝔅.prov x”

section GoedelSentence

variable [Diagonalization T₀]

local notation "γ" => 𝔅.goedel

lemma goedel_spec : T₀ ⊢!. γ ⭤ ∼𝔅 γ := by
  convert (diag (T := T₀) “x. ¬!𝔅.prov x”);
  simp [goedel, ← TransitiveRewriting.comp_app, Rew.substs_comp_substs];
  rfl;

variable [T₀ ⪯ T]

private lemma goedel_specAux₁ : T ⊢!. γ ⭤ ∼𝔅 γ := WeakerThan.pbl (𝓢 := T₀.alt) goedel_spec

private lemma goedel_specAux₂ [L.DecidableEq] : T ⊢!. ∼γ ➝ 𝔅 γ := contra₂'! $ of_k_right goedel_specAux₁

end GoedelSentence

class ProvabilityPredicate.GoedelSound (𝔅 : ProvabilityPredicate T₀ T) [Diagonalization T₀] where
  γ_sound : T ⊢!. 𝔅 𝔅.goedel → T ⊢!. 𝔅.goedel

open GoedelSound

section First

variable [T₀ ⪯ T] [Diagonalization T₀]

local notation "γ" => 𝔅.goedel

variable [Entailment.Consistent T]

theorem unprovable_goedel : T ⊬. γ := by
  intro h;
  have h₁ : T ⊢!. 𝔅 γ := D1_shift h;
  have h₂ : T ⊢!. ∼𝔅 γ := (of_k!_left goedel_specAux₁) ⨀ h;
  have : T ⊢!. ⊥ := (n!_iff_cO!.mp h₂) ⨀ h₁;
  have : ¬Consistent T := not_consistent_iff_inconsistent.mpr <|
    inconsistent_iff_provable_bot.mpr (by simpa [provable₀_iff] using this)
  contradiction;

theorem unrefutable_goedel [(k : ℕ) → DecidableEq (L.Func k)] [(k : ℕ) → DecidableEq (L.Rel k)] [𝔅.GoedelSound] : T ⊬. ∼γ := by
  intro h₂;
  have h₁ : T ⊢!. γ := γ_sound $ goedel_specAux₂ ⨀ h₂;
  have : T ⊢!. ⊥ := (n!_iff_cO!.mp h₂) ⨀ h₁;
  have : ¬Consistent T := not_consistent_iff_inconsistent.mpr <|
    inconsistent_iff_provable_bot.mpr (by simpa [provable₀_iff] using this);
  contradiction;

theorem goedel_independent [L.DecidableEq] [𝔅.GoedelSound] : Entailment.Undecidable T ↑γ := by
  suffices T ⊬. γ ∧ T ⊬. ∼γ by simpa [Entailment.Undecidable, not_or, unprovable₀_iff] using this
  constructor
  . apply unprovable_goedel
  . apply unrefutable_goedel

theorem first_incompleteness [L.DecidableEq] [𝔅.GoedelSound]
  : ¬Entailment.Complete T := Entailment.incomplete_iff_exists_undecidable.mpr ⟨γ, goedel_independent⟩

end First

section Second

variable [L.DecidableEq] [𝔅.HBL]

local notation "γ" => 𝔅.goedel

lemma formalized_consistent_of_existance_unprovable : T₀ ⊢!. ∼(𝔅 σ) ➝ 𝔅.con := contra₀'! $ 𝔅.D2 ⨀ (𝔅.D1 efq!)

private lemma consistency_lemma_1 [T₀ ⪯ U] : (U ⊢!. 𝔅.con ➝ ∼(𝔅 σ)) ↔ (U ⊢!. (𝔅 σ) ➝ 𝔅 (∼σ)) := by
  constructor;
  . intro H;
    exact contra₃'! $ c!_trans (WeakerThan.pbl (𝓢 := T₀.alt) formalized_consistent_of_existance_unprovable) H;
  . intro H
    apply contra₀'!
    have : T₀ ⊢!. (𝔅 σ) ⋏ 𝔅 (∼σ) ➝ 𝔅 ⊥ := c!_trans prov_collect_and $ prov_distribute_imply lac!;
    have : U ⊢!. (𝔅 σ) ➝ 𝔅 (∼σ) ➝ 𝔅 ⊥ := WeakerThan.pbl $ cK!_iff_cC!.mp $ this;
    exact this ⨀₁ H;

private lemma consistency_lemma_2 : T₀ ⊢!. ((𝔅 σ) ➝ 𝔅 (∼σ)) ➝ (𝔅 σ) ➝ 𝔅 ⊥ := by
  have : T ⊢!. σ ➝ ∼σ ➝ ⊥ := cK!_iff_cC!.mp lac!
  have : T₀ ⊢!. (𝔅 σ) ➝ 𝔅 (∼σ ➝ ⊥)  := prov_distribute_imply this;
  have : T₀ ⊢!. (𝔅 σ) ➝ (𝔅 (∼σ) ➝ 𝔅 ⊥) := c!_trans this 𝔅.D2;
  -- TODO: more simple proof
  apply FiniteContext.deduct'!;
  apply FiniteContext.deduct!;
  have d₁ : [(𝔅 σ), (𝔅 σ) ➝ 𝔅 (∼σ)] ⊢[T₀.alt]! (𝔅 σ) := FiniteContext.by_axm!;
  have d₂ : [(𝔅 σ), (𝔅 σ) ➝ 𝔅 (∼σ)] ⊢[T₀.alt]! (𝔅 σ) ➝ 𝔅 (∼σ) := FiniteContext.by_axm!;
  have d₃ : [(𝔅 σ), (𝔅 σ) ➝ 𝔅 (∼σ)] ⊢[T₀.alt]! 𝔅 (∼σ) := d₂ ⨀ d₁;
  exact ((FiniteContext.of'! this) ⨀ d₁) ⨀ d₃;

variable [T₀ ⪯ T] [Diagonalization T₀]

/-- Formalized First Incompleteness Theorem -/
theorem formalized_unprovable_goedel : T ⊢!. 𝔅.con ➝ ∼𝔅 γ := by
  have h₁ : T₀ ⊢!. 𝔅 γ ➝ 𝔅 (𝔅 γ) := 𝔅.D3;
  have h₂ : T ⊢!. 𝔅 γ ➝ ∼γ := WeakerThan.pbl $ contra₁'! $ of_k!_left goedel_spec;
  have h₃ : T₀ ⊢!. 𝔅 (𝔅 γ) ➝ 𝔅 (∼γ) := prov_distribute_imply h₂;
  exact WeakerThan.pbl $ contra₀'! $ consistency_lemma_2 ⨀ (c!_trans h₁ h₃);

theorem iff_goedel_consistency : T ⊢!. γ ⭤ 𝔅.con :=
  e!_trans goedel_specAux₁ $ e!_intro (WeakerThan.pbl (𝓢 := T₀.alt) formalized_consistent_of_existance_unprovable) formalized_unprovable_goedel

theorem unprovable_consistency [Entailment.Consistent T] : T ⊬. 𝔅.con :=
  unprovable_iff_of_e! iff_goedel_consistency |>.mp $ unprovable_goedel

theorem unrefutable_consistency [Entailment.Consistent T] [𝔅.GoedelSound] : T ⊬. ∼𝔅.con :=
  unprovable_iff_of_e! (neg_replace_iff'! $ iff_goedel_consistency) |>.mp $ unrefutable_goedel

end Second


section Loeb

def ProvabilityPredicate.kreisel [Diagonalization T₀]
    (𝔅 : ProvabilityPredicate T₀ T) [𝔅.HBL]
    (σ : Sentence L) : Sentence L := fixpoint T₀ “x. !𝔅.prov x → !σ”

section KrieselSentence

variable {𝔅 : ProvabilityPredicate T₀ T} [𝔅.HBL] [Diagonalization T₀]

local prefix:80 "κ" => 𝔅.kreisel

lemma kreisel_spec (σ : Sentence L) : T₀ ⊢!. κ(σ) ⭤ (𝔅 (κ(σ)) ➝ σ) := by
  convert (diag (T := T₀) “x. !𝔅.prov x → !σ”);
  simp [kreisel, ← TransitiveRewriting.comp_app, Rew.substs_comp_substs];
  rfl;

private lemma kreisel_specAux₁ [T₀ ⪯ T] (σ : Sentence L) : T₀ ⊢!. 𝔅 (κ σ) ➝ (𝔅 σ) := (c!_trans (𝔅.D2 ⨀ (𝔅.D1 (WeakerThan.pbl <| of_k!_left (kreisel_spec σ)))) 𝔅.D2) ⨀₁ 𝔅.D3

private lemma kreisel_specAux₂ (σ : Sentence L) : T₀ ⊢!. (𝔅 (κ σ) ➝ σ) ➝ κ(σ) := of_k_right (kreisel_spec σ)

end KrieselSentence


section LoebTheorem

variable [T₀ ⪯ T] [Diagonalization T₀] [𝔅.HBL]

local notation "κ(" σ ")" => 𝔅.kreisel σ

theorem loeb_theorm (H : T ⊢!. (𝔅 σ) ➝ σ) : T ⊢!. σ := by
  have d₁ : T ⊢!. 𝔅 (𝔅.kreisel σ) ➝ σ := c!_trans (WeakerThan.pbl (kreisel_specAux₁ σ)) H;
  have d₂ : T ⊢!. 𝔅 (𝔅.kreisel σ)     := WeakerThan.pbl (𝓢 := T₀.alt) (𝔅.D1 $ WeakerThan.pbl (kreisel_specAux₂ σ) ⨀ d₁);
  exact d₁ ⨀ d₂;

instance : 𝔅.Loeb := ⟨loeb_theorm (T := T)⟩

theorem formalized_loeb_theorem [L.DecidableEq] : T₀ ⊢!. 𝔅 ((𝔅 σ) ➝ σ) ➝ (𝔅 σ) := by
  have hκ₁ : T₀ ⊢!. 𝔅 (κ(σ)) ➝ (𝔅 σ) := kreisel_specAux₁ σ;
  have : T₀ ⊢!. ((𝔅 σ) ➝ σ) ➝ (𝔅 κ(σ) ➝ σ) := replace_imply_left! hκ₁;
  have : T ⊢!. ((𝔅 σ) ➝ σ) ➝ κ(σ) := WeakerThan.pbl (𝓢 := T₀.alt) $ c!_trans this (kreisel_specAux₂ σ);
  exact c!_trans (𝔅.D2 ⨀ (𝔅.D1 this)) hκ₁;

instance [L.DecidableEq] : 𝔅.FormalizedLoeb := ⟨formalized_loeb_theorem (T := T)⟩

end LoebTheorem


variable [Entailment.Consistent T]

lemma unprovable_consistency_via_loeb [𝔅.Loeb] : T ⊬. 𝔅.con := by
  by_contra hC;
  have : T ⊢!. ⊥ := Loeb.LT $ n!_iff_cO!.mp hC;
  have : ¬Consistent T := not_consistent_iff_inconsistent.mpr $ inconsistent_iff_provable_bot.mpr (by simpa [provable₀_iff] using this)
  contradiction

variable [L.DecidableEq] [Diagonalization T₀] [T₀ ⪯ T] [𝔅.HBL] [𝔅.GoedelSound]

lemma formalized_unprovable_not_consistency
  : T ⊬. 𝔅.con ➝ ∼𝔅 (∼𝔅.con) := by
  by_contra hC;
  have : T ⊢!. ∼𝔅.con := Loeb.LT $ contra₁'! hC;
  have : T ⊬. ∼𝔅.con := unrefutable_consistency;
  contradiction;

lemma formalized_unrefutable_goedel
  : T ⊬. 𝔅.con ➝ ∼𝔅 (∼𝔅.goedel) := by
  by_contra hC;
  have : T ⊬. 𝔅.con ➝ ∼𝔅 (∼𝔅.con)  := formalized_unprovable_not_consistency;
  have : T ⊢!. 𝔅.con ➝ ∼𝔅 (∼𝔅.con) := c!_trans hC $ WeakerThan.pbl $ of_k!_left $ neg_replace_iff'! $ prov_distribute_iff $ neg_replace_iff'! iff_goedel_consistency;
  contradiction;

end Loeb

abbrev ProvabilityPredicate.rosser
    [Diagonalization T₀]
    (𝔅 : ProvabilityPredicate T₀ T) [𝔅.Rosser] : Sentence L :=
  fixpoint T₀ “x. ¬!𝔅.prov x”

section RosserSentence

local notation "ρ" => 𝔅.rosser

variable [Diagonalization T₀] [𝔅.Rosser]

lemma rosser_spec : T₀ ⊢!. ρ ⭤ ∼(𝔅 ρ) := goedel_spec

private lemma rosser_specAux₁ [T₀ ⪯ T] : T ⊢!. ρ ⭤ ∼(𝔅 ρ) := goedel_specAux₁

end RosserSentence

section

variable [Diagonalization T₀] [T₀ ⪯ T] [Entailment.Consistent T] [𝔅.Rosser]

local notation "ρ" => 𝔅.rosser

lemma unprovable_rosser : T ⊬. ρ := unprovable_goedel

theorem unrefutable_rosser : T ⊬. ∼ρ := by
  intro hnρ;
  have hρ : T ⊢!. ρ := WeakerThan.pbl $ (of_k_right rosser_spec) ⨀ (𝔅.Ro hnρ);
  have : ¬Consistent T := not_consistent_iff_inconsistent.mpr $ inconsistent_iff_provable_bot.mpr <|
    by simpa [provable₀_iff] using (n!_iff_cO!.mp hnρ) ⨀ hρ;
  contradiction

theorem rosser_independent : Entailment.Undecidable T ↑ρ := by
  suffices T ⊬. ρ ∧ T ⊬. ∼ρ by simpa [Entailment.Undecidable, not_or, unprovable₀_iff] using this;
  constructor
  . apply unprovable_rosser
  . apply unrefutable_rosser

theorem rosser_first_incompleteness (𝔅 : ProvabilityPredicate T₀ T) [𝔅.Rosser] : ¬Entailment.Complete T :=
  Entailment.incomplete_iff_exists_undecidable.mpr ⟨𝔅.rosser, rosser_independent  ⟩

omit [Diagonalization T₀] [Consistent T] in
/-- If `𝔅` satisfies Rosser provability condition, then `𝔅.con` is provable in `T`. -/
theorem kriesel_remark : T ⊢!. 𝔅.con := by
  have : T₀ ⊢!. ∼𝔅 ⊥ := 𝔅.Ro (n!_iff_cO!.mpr (by simp));
  exact WeakerThan.pbl $ this;

end

end DerivabilityCondition

end LO.FirstOrder
