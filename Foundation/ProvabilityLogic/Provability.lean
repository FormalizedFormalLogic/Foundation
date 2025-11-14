import Foundation.FirstOrder.Arithmetic.Basic
import Foundation.Propositional.Entailment.Cl.Basic
import Foundation.Meta.ClProver

/-!
# Abstract incompleteness theorems and related results
-/

namespace LO

abbrev FirstOrder.Language.ReferenceableBy (L L₀ : Language) := Semiterm.Operator.GödelNumber L₀ (Sentence L)

namespace ProvabilityLogic

open FirstOrder

variable {L₀ L : Language}

structure Provability [L.ReferenceableBy L₀] (T₀ : Theory L₀) (T : Theory L) where
  prov : Semisentence L₀ 1
  protected D1 {σ : Sentence L} : T ⊢ σ → T₀ ⊢ prov/[⌜σ⌝]

namespace Provability

variable [L.ReferenceableBy L₀] {T₀ : Theory L₀} {T : Theory L}

@[coe] def pr (𝔅 : Provability T₀ T) (σ : Sentence L) : Sentence L₀ := 𝔅.prov/[⌜σ⌝]

instance : CoeFun (Provability T₀ T) (fun _ ↦ Sentence L → Sentence L₀) := ⟨pr⟩

def con (𝔅 : Provability T₀ T) : Sentence L₀ := ∼𝔅 ⊥

abbrev dia (𝔅 : Provability T₀ T) (φ : Sentence L) : Sentence L₀ := ∼𝔅 (∼φ)

end Provability

class Diagonalization [L.ReferenceableBy L] (T : Theory L) where
  fixedpoint : Semisentence L 1 → Sentence L
  diag (θ) : T ⊢ fixedpoint θ ⭤ θ/[⌜fixedpoint θ⌝]

namespace Provability

class HBL2 [L.ReferenceableBy L₀] {T₀ : Theory L₀} {T : Theory L} (𝔅 : Provability T₀ T) where
  protected D2 (σ τ : Sentence L) : T₀ ⊢ 𝔅 (σ ➝ τ) ➝ 𝔅 σ ➝ 𝔅 τ

class HBL3 [L.ReferenceableBy L] {T₀ T : Theory L} (𝔅 : Provability T₀ T) where
  protected D3 (σ : Sentence L) : T₀ ⊢ 𝔅 σ ➝ 𝔅 (𝔅 σ)

class HBL [L.ReferenceableBy L] {T₀ T : Theory L} (𝔅 : Provability T₀ T) extends 𝔅.HBL2, 𝔅.HBL3

class Loeb [L.ReferenceableBy L] {T₀ T : Theory L} (𝔅 : Provability T₀ T) where
  protected LT {σ : Sentence L} : T ⊢ 𝔅 σ ➝ σ → T ⊢ σ

class FormalizedLoeb [L.ReferenceableBy L] {T₀ T : Theory L} (𝔅 : Provability T₀ T) where
  protected FLT (σ : Sentence L) : T₀ ⊢ 𝔅 (𝔅 σ ➝ σ) ➝ 𝔅 σ

class Rosser [L.ReferenceableBy L₀] {T₀ : Theory L₀} {T : Theory L} (𝔅 : Provability T₀ T) where
  protected Ro {σ : Sentence L} : T ⊢ ∼σ → T₀ ⊢ ∼𝔅 σ

class SoundOnModel [L.ReferenceableBy L₀] {T₀ : Theory L₀} {T : Theory L}
    (𝔅 : Provability T₀ T) (N : outParam Type*) [Nonempty N] [Structure L₀ N] where
  protected sound {σ : Sentence L} : N ⊧ₘ 𝔅 σ ↔ T ⊢ σ

class Sound₀ [L.ReferenceableBy L₀] {T₀ : Theory L₀} {T : Theory L} (𝔅 : Provability T₀ T) where
  protected sound₀ {σ : Sentence L} : T₀ ⊢ 𝔅 σ → T ⊢ σ

class Sound [L.ReferenceableBy L] {T₀ T : Theory L} (𝔅 : Provability T₀ T) where
  protected sound {σ : Sentence L} : T ⊢ 𝔅 σ → T ⊢ σ

protected alias sound := Sound.sound

attribute [simp] sound

section

open LO.Entailment

protected alias D2 := HBL2.D2
protected alias D3 := HBL3.D3
protected alias LT := Loeb.LT
protected alias FLT := FormalizedLoeb.FLT
protected alias Ro := Rosser.Ro

section irreflexsive_syntactic_language

variable [L.ReferenceableBy L₀] {T₀ : Theory L₀} {T : Theory L} {𝔅 : Provability T₀ T}

lemma D2' [𝔅.HBL2] (σ τ) : T₀ ⊢ 𝔅 (σ ➝ τ) → T₀ ⊢ 𝔅 σ ➝ 𝔅 τ := by
  intro h;
  exact 𝔅.D2 σ τ ⨀ h;

lemma prov_distribute_imply [𝔅.HBL2] (h : T ⊢ σ ➝ τ) : T₀ ⊢ 𝔅 σ ➝ 𝔅 τ := 𝔅.D2' σ τ <| 𝔅.D1 h

lemma prov_distribute_iff [𝔅.HBL2] (h : T ⊢ σ ⭤ τ) : T₀ ⊢ 𝔅 σ ⭤ 𝔅 τ := by
  apply E!_intro;
  . exact prov_distribute_imply $ K!_left h;
  . exact prov_distribute_imply $ K!_right h;

lemma dia_distribute_imply [L₀.DecidableEq] [L.DecidableEq] [𝔅.HBL2]
    (h : T ⊢ σ ➝ τ) : T₀ ⊢ 𝔅.dia σ ➝ 𝔅.dia τ := by
  unfold dia
  have : T ⊢ ∼τ ➝ ∼σ := by cl_prover [h]
  have := 𝔅.prov_distribute_imply this
  cl_prover [this]

lemma prov_distribute_and [𝔅.HBL2] [L₀.DecidableEq] : T₀ ⊢ 𝔅 (σ ⋏ τ) ➝ 𝔅 σ ⋏ 𝔅 τ := by
  have h₁ : T₀ ⊢ 𝔅 (σ ⋏ τ) ➝ 𝔅 σ := 𝔅.D2' _ _ <| 𝔅.D1 and₁!;
  have h₂ : T₀ ⊢ 𝔅 (σ ⋏ τ) ➝ 𝔅 τ := 𝔅.D2' _ _ <| 𝔅.D1 and₂!;
  exact right_K!_intro h₁ h₂;

lemma prov_distribute_and' [𝔅.HBL2] [L₀.DecidableEq] : T₀ ⊢ 𝔅 (σ ⋏ τ) → T₀ ⊢ 𝔅 σ ⋏ 𝔅 τ := λ h => prov_distribute_and ⨀ h

lemma prov_collect_and [𝔅.HBL2] [L₀.DecidableEq] [L.DecidableEq] : T₀ ⊢ 𝔅 σ ⋏ 𝔅 τ ➝ 𝔅 (σ ⋏ τ) := by
  have : T₀ ⊢ 𝔅 σ ➝ 𝔅 (τ ➝ σ ⋏ τ) := prov_distribute_imply (by cl_prover)
  cl_prover [this, 𝔅.D2 τ (σ ⋏ τ)]

lemma sound_iff₀ [𝔅.Sound₀] : T₀ ⊢ 𝔅 σ ↔ T ⊢ σ := ⟨Sound₀.sound₀, 𝔅.D1⟩

end irreflexsive_syntactic_language
section reflexive_syntactic_language

variable [L.ReferenceableBy L] {T₀ T : Theory L} [T₀ ⪯ T] {𝔅 : Provability T₀ T}

lemma D1_shift : T ⊢ σ → T ⊢ 𝔅 σ := by
  intro h;
  apply Entailment.WeakerThan.pbl (𝓢 := T₀);
  apply 𝔅.D1 h;

lemma D2_shift [𝔅.HBL2] : T ⊢ 𝔅 (σ ➝ τ) ➝ 𝔅 σ ➝ 𝔅 τ := by
  apply Entailment.WeakerThan.pbl (𝓢 := T₀);
  apply 𝔅.D2;

lemma D3_shift [𝔅.HBL3] : T ⊢ 𝔅 σ ➝ 𝔅 (𝔅 σ) := by
  apply Entailment.WeakerThan.pbl (𝓢 := T₀);
  apply 𝔅.D3;

lemma FLT_shift [𝔅.FormalizedLoeb] : T ⊢ 𝔅 (𝔅 σ ➝ σ) ➝ 𝔅 σ := by
  apply Entailment.WeakerThan.pbl (𝓢 := T₀);
  apply 𝔅.FLT;

lemma prov_distribute_imply' [𝔅.HBL2] (h : T₀ ⊢ σ ➝ τ) :
    T₀ ⊢ 𝔅 σ ➝ 𝔅 τ := prov_distribute_imply $ WeakerThan.pbl h

lemma prov_distribute_imply'' [𝔅.HBL2] (h : T ⊢ σ ➝ τ) :
    T ⊢ 𝔅 σ ➝ 𝔅 τ := WeakerThan.pbl $ prov_distribute_imply h

lemma sound_iff [𝔅.Sound] : T ⊢ 𝔅 σ ↔ T ⊢ σ := ⟨Sound.sound, fun h ↦ WeakerThan.pbl (𝔅.D1 h)⟩

end reflexive_syntactic_language

end

open LO.Entailment Diagonalization Provability

def gödel [L.ReferenceableBy L] {T₀ T : Theory L} [Diagonalization T₀] (𝔅 : Provability T₀ T) : Sentence L :=
  fixedpoint T₀ “x. ¬!𝔅.prov x”

section GödelSentence

variable [L.ReferenceableBy L] {T₀ T : Theory L} [Diagonalization T₀] {𝔅 : Provability T₀ T}

local notation "𝗚" => 𝔅.gödel

variable (𝔅)

lemma gödel_spec : T₀ ⊢ 𝗚 ⭤ ∼𝔅 𝗚 := by
  convert (diag (T := T₀) “x. ¬!𝔅.prov x”);
  simp [gödel];
  rfl;

variable {𝔅}

end GödelSentence

class GödelSound [L.ReferenceableBy L] {T₀ T : Theory L} (𝔅 : Provability T₀ T) [Diagonalization T₀] where
  gödel_sound : T ⊢ 𝔅 𝔅.gödel → T ⊢ 𝔅.gödel

section First

variable [L.DecidableEq] [L.ReferenceableBy L] {T₀ T : Theory L} [T₀ ⪯ T] [Diagonalization T₀] [Consistent T]

variable (𝔅 : Provability T₀ T)

local notation "𝗚" => 𝔅.gödel

theorem unprovable_gödel : T ⊬ 𝗚 := by
  intro h;
  have h₁ : T ⊢ 𝔅 𝗚 := D1_shift h
  have : T ⊢ ⊥ := by cl_prover [h₁, 𝔅.gödel_spec, h]
  have : ¬Consistent T := not_consistent_iff_inconsistent.mpr <|
    inconsistent_iff_provable_bot.mpr this
  contradiction

theorem unrefutable_gödel [𝔅.GödelSound] : T ⊬ ∼𝗚 := by
  intro h₂;
  have h₁ : T ⊢ 𝗚 := GödelSound.gödel_sound <| by cl_prover [𝔅.gödel_spec, h₂]
  have : T ⊢ ⊥ := (N!_iff_CO!.mp h₂) ⨀ h₁;
  have : ¬Consistent T := not_consistent_iff_inconsistent.mpr <|
    inconsistent_iff_provable_bot.mpr this
  contradiction;

theorem gödel_independent [𝔅.GödelSound] : Independent T 𝗚 := by
  constructor
  . apply unprovable_gödel
  . apply unrefutable_gödel

theorem first_incompleteness [𝔅.GödelSound] : Incomplete T :=
  incomplete_def.mpr ⟨𝗚, 𝔅.gödel_independent⟩

end First

section Second

variable [L.DecidableEq] [L.ReferenceableBy L] {T₀ T : Theory L} {𝔅 : Provability T₀ T} [𝔅.HBL]

lemma formalized_consistent_of_existance_unprovable (σ) : T₀ ⊢ ∼𝔅 σ ➝ 𝔅.con := contra! $ 𝔅.D2 _ _ ⨀ (𝔅.D1 efq!)

variable [T₀ ⪯ T] [Diagonalization T₀] (𝔅)

local notation "𝗚" => 𝔅.gödel

/-- Formalized First Incompleteness Theorem -/
theorem formalized_unprovable_gödel : T₀ ⊢ 𝔅.con ➝ ∼𝔅 𝗚 := by
  suffices T₀ ⊢ ∼𝔅 ⊥ ➝ ∼𝔅 𝗚 from this
  have h₁ : T₀ ⊢ 𝔅 𝗚 ➝ 𝔅 (𝔅 𝗚) := 𝔅.D3 𝗚
  have h₂ : T₀ ⊢ 𝔅 𝗚 ➝ 𝔅 (𝔅 𝗚 ➝ ⊥) := prov_distribute_imply <| by cl_prover [𝔅.gödel_spec]
  have h₃ : T₀ ⊢ 𝔅 (𝔅 𝗚 ➝ ⊥) ➝ 𝔅 (𝔅 𝗚) ➝ 𝔅 ⊥ := 𝔅.D2 (𝔅 𝗚) ⊥
  cl_prover [h₁, h₂, h₃]

theorem gödel_iff_con : T₀ ⊢ 𝗚 ⭤ 𝔅.con := by
  have h₁ : T₀ ⊢ ∼𝔅 𝗚 ➝ 𝔅.con := formalized_consistent_of_existance_unprovable 𝗚
  have h₂ : T₀ ⊢ 𝔅.con ➝ ∼𝔅 𝗚 := 𝔅.formalized_unprovable_gödel
  have h₃ : T₀ ⊢ 𝗚 ⭤ ∼𝔅 𝗚 := 𝔅.gödel_spec
  cl_prover [h₁, h₂, h₃]

theorem con_unprovable [Consistent T] : T ⊬ 𝔅.con := by
  intro h
  have : T₀ ⊢ 𝗚 ⭤ 𝔅.con := 𝔅.gödel_iff_con
  have : T ⊢ 𝗚 := by cl_prover [h, this]
  exact 𝔅.unprovable_gödel this

theorem con_unrefutable [Consistent T] [𝔅.GödelSound] : T ⊬ ∼𝔅.con := by
  intro h
  have : T₀ ⊢ 𝗚 ⭤ 𝔅.con := 𝔅.gödel_iff_con
  have : T ⊢ ∼𝗚 := by cl_prover [h, this]
  exact 𝔅.unrefutable_gödel this

theorem con_independent [Consistent T] [𝔅.GödelSound] : Independent T 𝔅.con := by
  constructor
  . apply con_unprovable
  . apply con_unrefutable

end Second

section Loeb

variable [L.ReferenceableBy L] {T₀ T : Theory L}

def kreisel [Diagonalization T₀] (𝔅 : Provability T₀ T) [𝔅.HBL] (σ : Sentence L) : Sentence L := fixedpoint T₀ “x. !𝔅.prov x → !σ”

section KrieselSentence

variable [Diagonalization T₀] {𝔅 : Provability T₀ T} [𝔅.HBL]

local prefix:80 "𝗞" => 𝔅.kreisel

variable (𝔅)

lemma kreisel_spec (σ : Sentence L) : T₀ ⊢ 𝗞 σ ⭤ (𝔅 (𝗞 σ) ➝ σ) := by
  convert (diag (T := T₀) “x. !𝔅.prov x → !σ”);
  simp [kreisel, ← TransitiveRewriting.comp_app, Rew.subst_comp_subst];
  rfl;

variable {𝔅}

private lemma kreisel_specAux₁ [L.DecidableEq] [T₀ ⪯ T] (σ : Sentence L) :
    T₀ ⊢ 𝔅 (𝗞 σ) ➝ 𝔅 σ :=
  Entailment.mdp₁! (C!_trans (𝔅.D2 _ _ ⨀! (𝔅.D1 (WeakerThan.pbl <| K!_left (𝔅.kreisel_spec σ)))) (𝔅.D2 _ _)) (𝔅.D3 _)

private lemma kreisel_specAux₂ (σ : Sentence L) : T₀ ⊢ (𝔅 (𝗞 σ) ➝ σ) ➝ 𝗞 σ := K!_right (𝔅.kreisel_spec σ)

end KrieselSentence

section LoebTheorem

variable [L.DecidableEq] [Diagonalization T₀] [T₀ ⪯ T] {𝔅 : Provability T₀ T} [𝔅.HBL]

local notation "𝗞" => 𝔅.kreisel

theorem loeb_theorm (H : T ⊢ 𝔅 σ ➝ σ) : T ⊢ σ := by
  have d₁ : T ⊢ 𝔅 (𝗞 σ) ➝ σ := C!_trans (WeakerThan.pbl (kreisel_specAux₁ σ)) H;
  have d₂ : T ⊢ 𝔅 (𝗞 σ)     := WeakerThan.pbl (𝓢 := T₀) (𝔅.D1 $ WeakerThan.pbl (kreisel_specAux₂ σ) ⨀ d₁);
  exact d₁ ⨀ d₂;

instance : 𝔅.Loeb := ⟨loeb_theorm⟩

theorem formalized_loeb_theorem (σ) : T₀ ⊢ 𝔅 (𝔅 σ ➝ σ) ➝ 𝔅 σ := by
  have hκ₁ : T₀ ⊢ 𝔅 (𝗞 σ) ➝ 𝔅 σ := kreisel_specAux₁ σ;
  have : T₀ ⊢ (𝔅 σ ➝ σ) ➝ (𝔅 (𝗞 σ) ➝ σ) := CCC!_of_C!_left hκ₁;
  have : T ⊢ (𝔅 σ ➝ σ) ➝ 𝗞 σ := WeakerThan.pbl (𝓢 := T₀) $ C!_trans this (kreisel_specAux₂ σ);
  exact C!_trans (𝔅.D2 _ _ ⨀ (𝔅.D1 this)) hκ₁;

instance [L.DecidableEq] : 𝔅.FormalizedLoeb := ⟨formalized_loeb_theorem (T := T)⟩

end LoebTheorem

variable  {𝔅 : Provability T₀ T} [Consistent T]

lemma unprovable_con_via_loeb [L.DecidableEq] [𝔅.Loeb] : T ⊬ 𝔅.con := by
  by_contra hC;
  have : T ⊢ ⊥ := Loeb.LT $ N!_iff_CO!.mp hC;
  have : ¬Consistent T := not_consistent_iff_inconsistent.mpr
    <| inconsistent_iff_provable_bot.mpr this
  contradiction

variable [L.DecidableEq] [Diagonalization T₀] [T₀ ⪯ T] [𝔅.HBL] [𝔅.GödelSound]

lemma formalized_unprovable_not_con :
    T ⊬ 𝔅.con ➝ ∼𝔅 (∼𝔅.con) := by
  by_contra hC;
  have : T ⊢ ∼𝔅.con := Loeb.LT $ CN!_of_CN!_right hC;
  have : T ⊬ ∼𝔅.con := con_unrefutable 𝔅;
  contradiction;

lemma formalized_unrefutable_gödel : T ⊬ 𝔅.con ➝ ∼𝔅 (∼𝔅.gödel) := by
  by_contra hC;
  have : T ⊬ 𝔅.con ➝ ∼𝔅 (∼𝔅.con)  := formalized_unprovable_not_con;
  have : T ⊢ 𝔅.con ➝ ∼𝔅 (∼𝔅.con) :=
    C!_trans hC $ WeakerThan.pbl <| K!_left <| ENN!_of_E!
      <| prov_distribute_iff <| ENN!_of_E! <| WeakerThan.pbl (𝔅.gödel_iff_con);
  contradiction;

end Loeb

section Rosser

variable [L.ReferenceableBy L] {T₀ T : Theory L} [Diagonalization T₀] [T₀ ⪯ T] [Consistent T] {𝔅 : Provability T₀ T}

local notation "𝗥" => 𝔅.gödel

variable [𝔅.Rosser]

theorem unrefutable_rosser : T ⊬ ∼𝗥 := by
  intro hnρ;
  have hρ : T ⊢ 𝗥 := WeakerThan.pbl $ (K!_right 𝔅.gödel_spec) ⨀ (𝔅.Ro hnρ);
  have : ¬Consistent T := not_consistent_iff_inconsistent.mpr $ inconsistent_iff_provable_bot.mpr <|
    (N!_iff_CO!.mp hnρ) ⨀ hρ;
  contradiction

theorem rosser_independent [L.DecidableEq] : Independent T 𝗥 := by
  constructor
  . apply unprovable_gödel
  . apply unrefutable_rosser

theorem rosser_first_incompleteness [L.DecidableEq] (𝔅 : Provability T₀ T) [𝔅.Rosser] : Incomplete T :=
  incomplete_def.mpr ⟨𝔅.gödel, rosser_independent⟩

variable (𝔅)

omit [Diagonalization T₀] [Consistent T] in
/-- If `𝔅` satisfies Rosser provability condition, then `𝔅.con` is provable from `T`. -/
theorem kriesel_remark : T ⊢ 𝔅.con := by
  have : T₀ ⊢ ∼𝔅 ⊥ := 𝔅.Ro (N!_iff_CO!.mpr (by simp));
  exact WeakerThan.pbl $ this;

end Rosser

end LO.ProvabilityLogic.Provability
