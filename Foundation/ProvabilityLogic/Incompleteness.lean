import Foundation.FirstOrder.Arith.Basic
import Foundation.Logic.HilbertStyle.Supplemental
import Foundation.Meta.ClProver

/-!
# Abstract incompleteness theorems and related results
-/

namespace LO.ProvabilityLogic

open FirstOrder

variable {L : Language} [Semiterm.Operator.GoedelNumber L (Sentence L)]

structure ProvabilityPredicate (T₀ : Theory L) (T : Theory L) where
  prov : Semisentence L 1
  protected D1 {σ : Sentence L} : T ⊢!. σ → T₀ ⊢!. prov/[⌜σ⌝]

namespace ProvabilityPredicate

variable {T₀ T : Theory L}

@[coe] def pr (𝔅 : ProvabilityPredicate T₀ T) (σ : Sentence L) : Sentence L := 𝔅.prov/[⌜σ⌝]

instance : CoeFun (ProvabilityPredicate T₀ T) (fun _ ↦ Sentence L → Sentence L) := ⟨pr⟩

def con (𝔅 : ProvabilityPredicate T₀ T) : Sentence L := ∼𝔅 ⊥

end ProvabilityPredicate

class Diagonalization (T : Theory L) where
  fixpoint : Semisentence L 1 → Sentence L
  diag (θ) : T ⊢!. fixpoint θ ⭤ θ/[⌜fixpoint θ⌝]

namespace ProvabilityPredicate

variable {T₀ T : Theory L}

class HBL2 (𝔅 : ProvabilityPredicate T₀ T) where
  protected D2 (σ τ : Sentence L) : T₀ ⊢!. 𝔅 (σ ➝ τ) ➝ 𝔅 σ ➝ 𝔅 τ

class HBL3 (𝔅 : ProvabilityPredicate T₀ T) where
  protected D3 (σ : Sentence L) : T₀ ⊢!. 𝔅 σ ➝ 𝔅 (𝔅 σ)

class HBL (𝔅 : ProvabilityPredicate T₀ T) extends 𝔅.HBL2, 𝔅.HBL3

class Loeb (𝔅 : ProvabilityPredicate T₀ T) where
  protected LT {σ : Sentence L} : T ⊢!. 𝔅 σ ➝ σ → T ⊢!. σ

class FormalizedLoeb (𝔅 : ProvabilityPredicate T₀ T) where
  protected FLT (σ : Sentence L) : T₀ ⊢!. 𝔅 (𝔅 σ ➝ σ) ➝ 𝔅 σ

class Rosser (𝔅 : ProvabilityPredicate T₀ T) where
  protected Ro {σ : Sentence L} : T ⊢!. ∼σ → T₀ ⊢!. ∼𝔅 σ

class Sound (𝔅 : ProvabilityPredicate T₀ T) (N : outParam Type*) [Nonempty N] [Structure L N] where
  protected sound {σ : Sentence L} : N ⊧ₘ₀ 𝔅 σ ↔ T ⊢!. σ

protected alias sound := Sound.sound

attribute [simp] sound

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

lemma D1_shift [L.DecidableEq] [T₀ ⪯ T] : T ⊢!. σ → T ⊢!. 𝔅 σ := by
  intro h;
  apply Entailment.WeakerThan.pbl (𝓢 := T₀.toAxiom);
  apply 𝔅.D1 h;

lemma D2_shift [L.DecidableEq] [T₀ ⪯ T] [𝔅.HBL2] : T ⊢!. 𝔅 (σ ➝ τ) ➝ 𝔅 σ ➝ 𝔅 τ := by
  apply Entailment.WeakerThan.pbl (𝓢 := T₀.toAxiom);
  apply 𝔅.D2;

lemma D3_shift [L.DecidableEq] [T₀ ⪯ T] [𝔅.HBL3] : T ⊢!. 𝔅 σ ➝ 𝔅 (𝔅 σ) := by
  apply Entailment.WeakerThan.pbl (𝓢 := T₀.toAxiom);
  apply 𝔅.D3;

lemma FLT_shift [L.DecidableEq] [T₀ ⪯ T] [𝔅.FormalizedLoeb] : T ⊢!. 𝔅 (𝔅 σ ➝ σ) ➝ 𝔅 σ := by
  apply Entailment.WeakerThan.pbl (𝓢 := T₀.toAxiom);
  apply 𝔅.FLT;

lemma D2' [𝔅.HBL2] (σ τ) : T₀ ⊢!. 𝔅 (σ ➝ τ) → T₀ ⊢!. 𝔅 σ ➝ 𝔅 τ := by
  intro h;
  exact 𝔅.D2 σ τ ⨀ h;

lemma prov_distribute_imply [𝔅.HBL2] (h : T ⊢!. σ ➝ τ) : T₀ ⊢!. 𝔅 σ ➝ 𝔅 τ := 𝔅.D2' σ τ <| 𝔅.D1 h

lemma prov_distribute_imply' [L.DecidableEq] [T₀ ⪯ T] [𝔅.HBL2] (h : T₀ ⊢!. σ ➝ τ) :
    T₀ ⊢!. 𝔅 σ ➝ 𝔅 τ := prov_distribute_imply $ WeakerThan.pbl h

lemma prov_distribute_imply'' [L.DecidableEq] [T₀ ⪯ T] [𝔅.HBL2] (h : T ⊢!. σ ➝ τ) :
    T ⊢!. 𝔅 σ ➝ 𝔅 τ := WeakerThan.pbl $ prov_distribute_imply h

lemma prov_distribute_iff [𝔅.HBL2] (h : T ⊢!. σ ⭤ τ) : T₀ ⊢!. 𝔅 σ ⭤ 𝔅 τ := by
  apply E!_intro;
  . exact prov_distribute_imply $ K!_left h;
  . exact prov_distribute_imply $ K!_right h;

lemma prov_distribute_and  [𝔅.HBL2] [DecidableEq (Sentence L)] : T₀ ⊢!. 𝔅 (σ ⋏ τ) ➝ 𝔅 σ ⋏ 𝔅 τ := by
  have h₁ : T₀ ⊢!. 𝔅 (σ ⋏ τ) ➝ 𝔅 σ := 𝔅.D2' _ _ <| 𝔅.D1 and₁!;
  have h₂ : T₀ ⊢!. 𝔅 (σ ⋏ τ) ➝ 𝔅 τ := 𝔅.D2' _ _ <| 𝔅.D1 and₂!;
  exact right_K!_intro h₁ h₂;

def prov_distribute_and' [𝔅.HBL2] [DecidableEq (Sentence L)] : T₀ ⊢!. 𝔅 (σ ⋏ τ) → T₀ ⊢!. 𝔅 σ ⋏ 𝔅 τ := λ h => prov_distribute_and ⨀ h

def prov_collect_and [𝔅.HBL2] [DecidableEq (Sentence L)] : T₀ ⊢!. 𝔅 σ ⋏ 𝔅 τ ➝ 𝔅 (σ ⋏ τ) := by
  have : T₀ ⊢!. 𝔅 σ ➝ 𝔅 (τ ➝ σ ⋏ τ) := prov_distribute_imply (by cl_prover)
  cl_prover [this, 𝔅.D2 τ (σ ⋏ τ)]

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

local notation "𝗚" => 𝔅.goedel

variable (𝔅)

lemma ProvabilityPredicate.goedel_spec : T₀ ⊢!. 𝗚 ⭤ ∼𝔅 𝗚 := by
  convert (diag (T := T₀) “x. ¬!𝔅.prov x”);
  simp [goedel, ← TransitiveRewriting.comp_app, Rew.substs_comp_substs];
  rfl;

variable {𝔅}

end GoedelSentence

class ProvabilityPredicate.GoedelSound (𝔅 : ProvabilityPredicate T₀ T) [Diagonalization T₀] where
  goedel_sound : T ⊢!. 𝔅 𝔅.goedel → T ⊢!. 𝔅.goedel

section First

variable [T₀ ⪯ T] [Diagonalization T₀] [L.DecidableEq] [Entailment.Consistent T]

local notation "𝗚" => 𝔅.goedel

theorem unprovable_goedel : T ⊬. 𝗚 := by
  intro h;
  have h₁ : T ⊢!. 𝔅 𝗚 := D1_shift h
  have : T ⊢!. ⊥ := by cl_prover [h₁, 𝔅.goedel_spec, h]
  have : ¬Consistent T := not_consistent_iff_inconsistent.mpr <|
    inconsistent_iff_provable_bot.mpr (by simpa [Axiom.provable_iff] using this)
  contradiction

theorem unrefutable_goedel [𝔅.GoedelSound] : T ⊬. ∼𝗚 := by
  intro h₂;
  have h₁ : T ⊢!. 𝗚 := GoedelSound.goedel_sound <| by cl_prover [𝔅.goedel_spec, h₂]
  have : T ⊢!. ⊥ := (N!_iff_CO!.mp h₂) ⨀ h₁;
  have : ¬Consistent T := not_consistent_iff_inconsistent.mpr <|
    inconsistent_iff_provable_bot.mpr (by simpa [Axiom.provable_iff] using this);
  contradiction;

theorem goedel_independent [𝔅.GoedelSound] : Entailment.Undecidable (T : Axiom L) 𝗚 := by
  constructor
  . apply unprovable_goedel
  . apply unrefutable_goedel

theorem first_incompleteness [𝔅.GoedelSound] :
    ¬Entailment.Complete (T : Axiom L) :=
  incomplete_iff_exists_undecidable.mpr ⟨𝗚, goedel_independent⟩

end First

section Second

variable [L.DecidableEq] [𝔅.HBL]

lemma formalized_consistent_of_existance_unprovable (σ) : T₀ ⊢!. ∼𝔅 σ ➝ 𝔅.con := contra! $ 𝔅.D2 _ _ ⨀ (𝔅.D1 efq!)

variable [T₀ ⪯ T] [Diagonalization T₀]

local notation "𝗚" => 𝔅.goedel

/-- Formalized First Incompleteness Theorem -/
theorem formalized_unprovable_goedel : T₀ ⊢!. 𝔅.con ➝ ∼𝔅 𝗚 := by
  suffices T₀ ⊢!. ∼𝔅 ⊥ ➝ ∼𝔅 𝗚 from this
  have h₁ : T₀ ⊢!. 𝔅 𝗚 ➝ 𝔅 (𝔅 𝗚) := 𝔅.D3 𝗚
  have h₂ : T₀ ⊢!. 𝔅 𝗚 ➝ 𝔅 (𝔅 𝗚 ➝ ⊥) := prov_distribute_imply <| by cl_prover [𝔅.goedel_spec]
  have h₃ : T₀ ⊢!. 𝔅 (𝔅 𝗚 ➝ ⊥) ➝ 𝔅 (𝔅 𝗚) ➝ 𝔅 ⊥ := 𝔅.D2 (𝔅 𝗚) ⊥
  cl_prover [h₁, h₂, h₃]

theorem goedel_iff_consistency : T₀ ⊢!. 𝗚 ⭤ 𝔅.con := by
  have h₁ : T₀ ⊢!. ∼𝔅 𝗚 ➝ 𝔅.con := formalized_consistent_of_existance_unprovable 𝗚
  have h₂ : T₀ ⊢!. 𝔅.con ➝ ∼𝔅 𝗚 := formalized_unprovable_goedel
  have h₃ : T₀ ⊢!. 𝗚 ⭤ ∼𝔅 𝗚 := 𝔅.goedel_spec
  cl_prover [h₁, h₂, h₃]

theorem unprovable_consistency [Consistent T] : T ⊬. 𝔅.con := by
  intro h
  have : T₀ ⊢!. 𝗚 ⭤ 𝔅.con := goedel_iff_consistency
  have : T ⊢!. 𝗚 := by cl_prover [h, this]
  exact unprovable_goedel this

theorem unrefutable_consistency [Consistent T] [𝔅.GoedelSound] : T ⊬. ∼𝔅.con := by
  intro h
  have : T₀ ⊢!. 𝗚 ⭤ 𝔅.con := goedel_iff_consistency
  have : T ⊢!. ∼𝗚 := by cl_prover [h, this]
  exact unrefutable_goedel this

theorem consistency_independent [Consistent T] [𝔅.GoedelSound] : Undecidable (T : Axiom L) 𝔅.con := by
  constructor
  . apply unprovable_consistency
  . apply unrefutable_consistency

end Second

section Loeb

def ProvabilityPredicate.kreisel [Diagonalization T₀]
    (𝔅 : ProvabilityPredicate T₀ T) [𝔅.HBL]
    (σ : Sentence L) : Sentence L := fixpoint T₀ “x. !𝔅.prov x → !σ”

section KrieselSentence

variable {𝔅 : ProvabilityPredicate T₀ T} [𝔅.HBL] [Diagonalization T₀]

local prefix:80 "𝗞" => 𝔅.kreisel

variable (𝔅)

lemma ProvabilityPredicate.kreisel_spec (σ : Sentence L) : T₀ ⊢!. 𝗞 σ ⭤ (𝔅 (𝗞 σ) ➝ σ) := by
  convert (diag (T := T₀) “x. !𝔅.prov x → !σ”);
  simp [kreisel, ← TransitiveRewriting.comp_app, Rew.substs_comp_substs];
  rfl;

variable {𝔅}

private lemma kreisel_specAux₁ [L.DecidableEq] [T₀ ⪯ T] (σ : Sentence L) :
    T₀ ⊢!. 𝔅 (𝗞 σ) ➝ 𝔅 σ :=
  Entailment.mdp₁! (C!_trans (𝔅.D2 _ _ ⨀! (𝔅.D1 (WeakerThan.pbl <| K!_left (𝔅.kreisel_spec σ)))) (𝔅.D2 _ _)) (𝔅.D3 _)

private lemma kreisel_specAux₂ (σ : Sentence L) : T₀ ⊢!. (𝔅 (𝗞 σ) ➝ σ) ➝ 𝗞 σ := K!_right (𝔅.kreisel_spec σ)

end KrieselSentence


section LoebTheorem

variable [L.DecidableEq] [T₀ ⪯ T] [Diagonalization T₀] [𝔅.HBL]

local notation "𝗞" => 𝔅.kreisel

theorem loeb_theorm (H : T ⊢!. 𝔅 σ ➝ σ) : T ⊢!. σ := by
  have d₁ : T ⊢!. 𝔅 (𝗞 σ) ➝ σ := C!_trans (WeakerThan.pbl (kreisel_specAux₁ σ)) H;
  have d₂ : T ⊢!. 𝔅 (𝗞 σ)     := WeakerThan.pbl (𝓢 := T₀.toAxiom) (𝔅.D1 $ WeakerThan.pbl (kreisel_specAux₂ σ) ⨀ d₁);
  exact d₁ ⨀ d₂;

instance : 𝔅.Loeb := ⟨loeb_theorm⟩

theorem formalized_loeb_theorem (σ) : T₀ ⊢!. 𝔅 (𝔅 σ ➝ σ) ➝ 𝔅 σ := by
  have hκ₁ : T₀ ⊢!. 𝔅 (𝗞 σ) ➝ 𝔅 σ := kreisel_specAux₁ σ;
  have : T₀ ⊢!. (𝔅 σ ➝ σ) ➝ (𝔅 (𝗞 σ) ➝ σ) := CCC!_of_C!_left hκ₁;
  have : T ⊢!. (𝔅 σ ➝ σ) ➝ 𝗞 σ := WeakerThan.pbl (𝓢 := T₀.toAxiom) $ C!_trans this (kreisel_specAux₂ σ);
  exact C!_trans (𝔅.D2 _ _ ⨀ (𝔅.D1 this)) hκ₁;

instance [L.DecidableEq] : 𝔅.FormalizedLoeb := ⟨formalized_loeb_theorem (T := T)⟩

end LoebTheorem

variable [Entailment.Consistent T]

lemma unprovable_consistency_via_loeb [L.DecidableEq] [𝔅.Loeb] : T ⊬. 𝔅.con := by
  by_contra hC;
  have : T ⊢!. ⊥ := Loeb.LT $ N!_iff_CO!.mp hC;
  have : ¬Consistent T := not_consistent_iff_inconsistent.mpr
    <| inconsistent_iff_provable_bot.mpr (by simpa [Axiom.provable_iff] using this)
  contradiction

variable [L.DecidableEq] [Diagonalization T₀] [T₀ ⪯ T] [𝔅.HBL] [𝔅.GoedelSound]

lemma formalized_unprovable_not_consistency :
    T ⊬. 𝔅.con ➝ ∼𝔅 (∼𝔅.con) := by
  by_contra hC;
  have : T ⊢!. ∼𝔅.con := Loeb.LT $ CN!_of_CN!_right hC;
  have : T ⊬. ∼𝔅.con := unrefutable_consistency;
  contradiction;

lemma formalized_unrefutable_goedel : T ⊬. 𝔅.con ➝ ∼𝔅 (∼𝔅.goedel) := by
  by_contra hC;
  have : T ⊬. 𝔅.con ➝ ∼𝔅 (∼𝔅.con)  := formalized_unprovable_not_consistency;
  have : T ⊢!. 𝔅.con ➝ ∼𝔅 (∼𝔅.con) :=
    C!_trans hC $ WeakerThan.pbl <| K!_left <| ENN!_of_E!
      <| prov_distribute_iff <| ENN!_of_E! <| WeakerThan.pbl goedel_iff_consistency;
  contradiction;

end Loeb

section Rosser

variable [L.DecidableEq] [Diagonalization T₀] [T₀ ⪯ T] [Entailment.Consistent T]

local notation "𝗥" => 𝔅.goedel

lemma unprovable_rosser : T ⊬. 𝗥 := unprovable_goedel

variable [𝔅.Rosser]

theorem unrefutable_rosser : T ⊬. ∼𝗥 := by
  intro hnρ;
  have hρ : T ⊢!. 𝗥 := WeakerThan.pbl $ (K!_right 𝔅.goedel_spec) ⨀ (𝔅.Ro hnρ);
  have : ¬Consistent T := not_consistent_iff_inconsistent.mpr $ inconsistent_iff_provable_bot.mpr <|
    by simpa [Axiom.provable_iff] using (N!_iff_CO!.mp hnρ) ⨀ hρ;
  contradiction

theorem rosser_independent : Entailment.Undecidable T ↑𝗥 := by
  suffices T ⊬. 𝗥 ∧ T ⊬. ∼𝗥 by simpa [Entailment.Undecidable, not_or, Axiom.unprovable_iff] using this;
  constructor
  . apply unprovable_rosser
  . apply unrefutable_rosser

theorem rosser_first_incompleteness (𝔅 : ProvabilityPredicate T₀ T) [𝔅.Rosser] : ¬Entailment.Complete T :=
  Entailment.incomplete_iff_exists_undecidable.mpr ⟨𝔅.goedel, rosser_independent⟩

omit [Diagonalization T₀] [Consistent T] in
/-- If `𝔅` satisfies Rosser provability condition, then `𝔅.con` is provable from `T`. -/
theorem kriesel_remark : T ⊢!. 𝔅.con := by
  have : T₀ ⊢!. ∼𝔅 ⊥ := 𝔅.Ro (N!_iff_CO!.mpr (by simp));
  exact WeakerThan.pbl $ this;

end Rosser

end LO.ProvabilityLogic
