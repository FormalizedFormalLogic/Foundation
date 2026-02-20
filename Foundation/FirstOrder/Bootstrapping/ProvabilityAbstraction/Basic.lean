module

public import Foundation.FirstOrder.Arithmetic.Basic
public import Foundation.Meta.ClProver

@[expose] public section
/-!
# Abstract incompleteness theorems and related results
-/

namespace LO


namespace FirstOrder

variable {L₀ L : Language}

abbrev Language.ReferenceableBy (L L₀ : Language) := Semiterm.Operator.GödelNumber L₀ (Sentence L)

namespace ProvabilityAbstraction

structure Provability [L.ReferenceableBy L₀] (T₀ : Theory L₀) (T : Theory L) where
  prov : Semisentence L₀ 1
  /-- Derivability condition `D1` -/
  prov_def {σ : Sentence L} : T ⊢ σ → T₀ ⊢ prov/[⌜σ⌝]

namespace Provability

variable [L.ReferenceableBy L₀] {T₀ : Theory L₀} {T : Theory L}

@[coe] def pr (𝔅 : Provability T₀ T) (σ : Sentence L) : Sentence L₀ := 𝔅.prov/[⌜σ⌝]
instance : CoeFun (Provability T₀ T) (fun _ ↦ Sentence L → Sentence L₀) := ⟨pr⟩

def con (𝔅 : Provability T₀ T) : Sentence L₀ := ∼𝔅 ⊥

abbrev dia (𝔅 : Provability T₀ T) (φ : Sentence L) : Sentence L₀ := ∼𝔅 (∼φ)

end Provability


section

variable
  {L₀ L : Language} [L.ReferenceableBy L₀]
  {T₀ : Theory L₀} {T : Theory L}

lemma D1 {𝔅 : Provability T₀ T} {σ : Sentence L} : T ⊢ σ → T₀ ⊢ 𝔅 σ := fun h ↦ 𝔅.prov_def h

namespace Provability

class HBL2 [L.ReferenceableBy L₀] {T₀ : Theory L₀} {T : Theory L} (𝔅 : Provability T₀ T) where
  D2 {σ τ : Sentence L} : T₀ ⊢ 𝔅 (σ ➝ τ) ➝ 𝔅 σ ➝ 𝔅 τ
export HBL2 (D2)

variable [L.ReferenceableBy L] {T₀ T : Theory L} (𝔅 : Provability T₀ T)

class HBL3 where
  D3 {σ : Sentence L} : T₀ ⊢ 𝔅 σ ➝ 𝔅 (𝔅 σ)
export HBL3 (D3)

class HBL extends 𝔅.HBL2, 𝔅.HBL3

class Mono [L.ReferenceableBy L₀] {T₀ : Theory L₀} {T : Theory L} (𝔅 : Provability T₀ T) where
  mono {σ τ : Sentence L} : T ⊢ σ ➝ τ → T₀ ⊢ 𝔅 σ ➝ 𝔅 τ

class Equiv [L.ReferenceableBy L₀] {T₀ : Theory L₀} {T : Theory L} (𝔅 : Provability T₀ T) where
  equiv {σ τ : Sentence L} : T ⊢ σ ⭤ τ → T₀ ⊢ 𝔅 σ ⭤ 𝔅 τ

class Löb where
  LT {σ : Sentence L} : T ⊢ 𝔅 σ ➝ σ → T ⊢ σ
export Löb (LT)

class FormalizedLöb where
  FLT {σ : Sentence L} : T₀ ⊢ 𝔅 (𝔅 σ ➝ σ) ➝ 𝔅 σ
export FormalizedLöb (FLT)

class Rosser [L.ReferenceableBy L₀] {T₀ : Theory L₀} {T : Theory L} (𝔅 : Provability T₀ T) where
  Ros {σ : Sentence L} : T ⊢ ∼σ → T₀ ⊢ ∼𝔅 σ
export Rosser (Ros)


/--
  Abstract version of formalized `Γ`-completeness for provability `𝔅`

  example: `[∀ σ ∈ 𝚺₁, 𝔅.FormalizedCompleteOn σ]` for formalized `𝚺₁`-completeness
-/
class FormalizedCompleteOn (𝔅 : Provability T₀ T) (σ) where
  formalized_complete_on : T ⊢ σ ➝ 𝔅 σ
export FormalizedCompleteOn (formalized_complete_on)
attribute [simp, grind .] formalized_complete_on

/--
  NOTE: Named after [Vis21].
-/
class Kreisel [L.ReferenceableBy L] {T₀ T : Theory L} (𝔅 : Provability T₀ T) (σ) where
  KR : T ⊢ 𝔅 σ → T ⊢ σ
export Kreisel (KR)
attribute [simp, grind .] KR

class WeakKreisel [L.ReferenceableBy L] {T₀ T : Theory L} (𝔅 : Provability T₀ T) (σ) where
  WKR : T₀ ⊢ 𝔅 σ → T ⊢ σ
export WeakKreisel (WKR)
attribute [simp, grind .] WKR


class SoundOn
  [L.ReferenceableBy L₀] {T₀ : Theory L₀} {T : Theory L}
  (𝔅 : Provability T₀ T)
  (M : outParam Type*) [Nonempty M] [Structure L₀ M]
  (σ)
  where
  sound_on : M ⊧ₘ 𝔅 σ → T ⊢ σ
export SoundOn (sound_on)
attribute [simp, grind .] sound_on


instance [Nonempty M] [Structure L M] [𝔅.SoundOn M σ] [M ⊧ₘ* T₀] : 𝔅.WeakKreisel σ where
  WKR h := SoundOn.sound_on $ models_of_provable inferInstance h;

end Provability


end


open LO.Entailment
open Provability

section

variable
  [L.ReferenceableBy L₀]
  {T₀ : Theory L₀} {T : Theory L}
  {𝔅 : Provability T₀ T}
  {σ τ : Sentence L}

lemma D2' [𝔅.HBL2] : T₀ ⊢ 𝔅 (σ ➝ τ) → T₀ ⊢ 𝔅 σ ➝ 𝔅 τ := by
  intro h;
  exact D2 ⨀ h;

lemma prov_distribute_imply [𝔅.HBL2] (h : T ⊢ σ ➝ τ) : T₀ ⊢ 𝔅 σ ➝ 𝔅 τ := D2' $ D1 h

lemma prov_distribute_iff [𝔅.HBL2] (h : T ⊢ σ ⭤ τ) : T₀ ⊢ 𝔅 σ ⭤ 𝔅 τ := by
  apply E!_intro;
  . exact prov_distribute_imply $ K!_left h;
  . exact prov_distribute_imply $ K!_right h;

lemma dia_distribute_imply [L₀.DecidableEq] [L.DecidableEq] [𝔅.HBL2]
  (h : T ⊢ σ ➝ τ) : T₀ ⊢ 𝔅.dia σ ➝ 𝔅.dia τ := by
  have : T₀ ⊢ 𝔅 (∼τ) ➝ 𝔅 (∼σ) := prov_distribute_imply $ by cl_prover [h];
  cl_prover [this]

lemma prov_distribute_and [𝔅.HBL2] [L₀.DecidableEq] : T₀ ⊢ 𝔅 (σ ⋏ τ) ➝ 𝔅 σ ⋏ 𝔅 τ := by
  have h₁ : T₀ ⊢ 𝔅 (σ ⋏ τ) ➝ 𝔅 σ := D2' $ D1 and₁!;
  have h₂ : T₀ ⊢ 𝔅 (σ ⋏ τ) ➝ 𝔅 τ := D2' $ D1 and₂!;
  cl_prover [h₁, h₂];

lemma prov_distribute_and' [𝔅.HBL2] [L₀.DecidableEq] : T₀ ⊢ 𝔅 (σ ⋏ τ) → T₀ ⊢ 𝔅 σ ⋏ 𝔅 τ := λ h => prov_distribute_and ⨀ h

lemma prov_collect_and [𝔅.HBL2] [L₀.DecidableEq] [L.DecidableEq] : T₀ ⊢ 𝔅 σ ⋏ 𝔅 τ ➝ 𝔅 (σ ⋏ τ) := by
  have h₁ : T₀ ⊢ 𝔅 σ ➝ 𝔅 (τ ➝ σ ⋏ τ) := prov_distribute_imply $ by cl_prover
  have h₂ : T₀ ⊢ 𝔅 (τ ➝ σ ⋏ τ) ➝ 𝔅 τ ➝ 𝔅 (σ ⋏ τ) := D2;
  cl_prover [h₁, h₂];

end

section

variable
  [L.ReferenceableBy L] {T₀ T : Theory L} [T₀ ⪯ T]
  {𝔅 : Provability T₀ T}
  {σ τ : Sentence L}

lemma D1_shift : T ⊢ σ → T ⊢ 𝔅 σ := by
  intro h;
  apply Entailment.WeakerThan.pbl (𝓢 := T₀);
  apply D1 h;

lemma D2_shift [𝔅.HBL2] : T ⊢ 𝔅 (σ ➝ τ) ➝ 𝔅 σ ➝ 𝔅 τ := by
  apply Entailment.WeakerThan.pbl (𝓢 := T₀) $ D2;

lemma D3_shift [𝔅.HBL3] : T ⊢ 𝔅 σ ➝ 𝔅 (𝔅 σ) := by
  apply Entailment.WeakerThan.pbl (𝓢 := T₀) $ D3;

lemma FLT_shift [𝔅.FormalizedLöb] : T ⊢ 𝔅 (𝔅 σ ➝ σ) ➝ 𝔅 σ := by
  apply Entailment.WeakerThan.pbl (𝓢 := T₀) $ FLT;

lemma prov_distribute_imply' [𝔅.HBL2] (h : T₀ ⊢ σ ➝ τ) : T₀ ⊢ 𝔅 σ ➝ 𝔅 τ :=
  prov_distribute_imply $ WeakerThan.pbl h

lemma prov_distribute_imply'' [𝔅.HBL2] (h : T ⊢ σ ➝ τ) : T ⊢ 𝔅 σ ➝ 𝔅 τ :=
  WeakerThan.pbl $ prov_distribute_imply h

end


class Diagonalization [L.ReferenceableBy L] (T : Theory L) where
  fixedpoint : Semisentence L 1 → Sentence L
  diag (θ) : T ⊢ fixedpoint θ ⭤ θ/[⌜fixedpoint θ⌝]

open LO.Entailment Diagonalization Provability

variable
  [L.ReferenceableBy L]
  {T₀ T : Theory L} [Diagonalization T₀] {𝔅 : Provability T₀ T}

def gödel [L.ReferenceableBy L] {T₀ T : Theory L} [Diagonalization T₀] (𝔅 : Provability T₀ T) : Sentence L :=
  fixedpoint T₀ “x. ¬!𝔅.prov x”

lemma gödel_spec : T₀ ⊢ (gödel 𝔅) ⭤ ∼𝔅 (gödel 𝔅) := by simpa [gödel] using diag “x. ¬!𝔅.prov x”;

section First

variable [L.DecidableEq]
variable [T₀ ⪯ T] [Consistent T]

theorem unprovable_gödel : T ⊬ (gödel 𝔅) := by
  intro h;
  have h₁ : T ⊢ 𝔅 (gödel 𝔅) := D1_shift h;
  have h₂ : T ⊢ (gödel 𝔅) ⭤ ∼𝔅 (gödel 𝔅) := WeakerThan.pbl $ gödel_spec;
  have : T ⊢ ⊥ := by cl_prover [h₁, h₂, h];
  have : ¬Consistent T := not_consistent_iff_inconsistent.mpr <| inconsistent_iff_provable_bot.mpr this;
  contradiction

theorem unrefutable_gödel [𝔅.Kreisel (gödel 𝔅)] : T ⊬ ∼(gödel 𝔅) := by
  intro h₂;
  have h₁ : T ⊢ (gödel 𝔅) := WeakerThan.pbl $ 𝔅.KR $ by cl_prover [gödel_spec (T₀ := T₀), h₂];
  have : T ⊢ ⊥ := (N!_iff_CO!.mp $ WeakerThan.pbl $ h₂) ⨀ h₁;
  have : ¬Consistent T := not_consistent_iff_inconsistent.mpr <| inconsistent_iff_provable_bot.mpr this
  contradiction;

theorem gödel_independent [𝔅.Kreisel (gödel 𝔅)] : Independent T (gödel 𝔅) := by
  constructor
  . apply unprovable_gödel
  . apply unrefutable_gödel

theorem first_incompleteness [𝔅.Kreisel (gödel 𝔅)] : Incomplete T :=
  incomplete_def.mpr ⟨(gödel 𝔅), gödel_independent⟩

end First


section Second

variable [𝔅.HBL]

omit [Diagonalization T₀] in
lemma formalized_consistent_of_existance_unprovable [L.DecidableEq] : T₀ ⊢ ∼𝔅 σ ➝ 𝔅.con := contra! $ mdp! D2 $ D1 efq!

local notation "𝐆" => gödel 𝔅

variable [L.DecidableEq] [T₀ ⪯ T]

/-- Formalized First Incompleteness Theorem -/
theorem formalized_unprovable_gödel  : T₀ ⊢ 𝔅.con ➝ ∼𝔅 𝐆 := by
  suffices T₀ ⊢ ∼𝔅 ⊥ ➝ ∼𝔅 𝐆 from this
  have h₁ : T₀ ⊢ 𝔅 𝐆 ➝ 𝔅 (𝔅 𝐆) := D3
  have h₂ : T₀ ⊢ 𝔅 𝐆 ➝ 𝔅 (𝔅 𝐆 ➝ ⊥) := prov_distribute_imply $ by
    cl_prover [gödel_spec (T₀ := T₀)]
  have h₃ : T₀ ⊢ 𝔅 (𝔅 𝐆 ➝ ⊥) ➝ 𝔅 (𝔅 𝐆) ➝ 𝔅 ⊥ := D2
  cl_prover [h₁, h₂, h₃]

theorem gödel_iff_con : T₀ ⊢ 𝐆 ⭤ 𝔅.con := by
  have h₁ : T₀ ⊢ ∼𝔅 𝐆 ➝ 𝔅.con := formalized_consistent_of_existance_unprovable
  have h₂ : T₀ ⊢ 𝔅.con ➝ ∼𝔅 𝐆 := formalized_unprovable_gödel
  have h₃ : T₀ ⊢ 𝐆 ⭤ ∼𝔅 𝐆 := gödel_spec
  cl_prover [h₁, h₂, h₃];

theorem con_unprovable [Consistent T] : T ⊬ 𝔅.con := by
  intro h
  have : T₀ ⊢ 𝐆 ⭤ 𝔅.con := gödel_iff_con
  have : T ⊢ 𝐆 := by cl_prover [h, this]
  exact unprovable_gödel this

theorem con_unrefutable [Consistent T] [𝔅.Kreisel (gödel 𝔅)] : T ⊬ ∼𝔅.con := by
  intro h
  have : T₀ ⊢ 𝐆 ⭤ 𝔅.con := gödel_iff_con
  have : T ⊢ ∼𝐆 := by cl_prover [h, this]
  exact unrefutable_gödel this

theorem con_independent [Consistent T] [𝔅.Kreisel (gödel 𝔅)] : Independent T 𝔅.con := by
  constructor
  . apply con_unprovable
  . apply con_unrefutable

end Second


section Löb

def kreisel [Diagonalization T₀] (𝔅 : Provability T₀ T) (σ : Sentence L) : Sentence L := fixedpoint T₀ “x. !𝔅.prov x → !σ”

local notation "𝐊" => kreisel 𝔅

lemma kreisel_spec : T₀ ⊢ (𝐊 σ) ⭤ (𝔅 (𝐊 σ) ➝ σ) := by
  simpa [kreisel, Rew.subst_comp_subst, ←TransitiveRewriting.comp_app] using diag “x. !𝔅.prov x → !σ”;

private lemma kreisel_specAux₂ : T₀ ⊢ (𝔅 (𝐊 σ) ➝ σ) ➝ (𝐊 σ) := K!_right kreisel_spec

variable [𝔅.HBL]

private lemma kreisel_specAux₁ [L.DecidableEq] [T₀ ⪯ T] : T₀ ⊢ 𝔅 (𝐊 σ) ➝ 𝔅 σ :=
  Entailment.mdp₁! (C!_trans (mdp! D2 (D1 (WeakerThan.pbl <| K!_left (kreisel_spec)))) D2) D3

variable [L.DecidableEq] [T₀ ⪯ T]

theorem löb_theorem (H : T ⊢ 𝔅 σ ➝ σ) : T ⊢ σ := by
  have d₁ : T ⊢ 𝔅 (𝐊 σ) ➝ σ := C!_trans (WeakerThan.pbl kreisel_specAux₁) H;
  have d₂ : T ⊢ 𝔅 (𝐊 σ)     := WeakerThan.pbl (𝓢 := T₀) (D1 $ WeakerThan.pbl kreisel_specAux₂ ⨀ d₁);
  exact d₁ ⨀ d₂;

instance : 𝔅.Löb := ⟨löb_theorem⟩

theorem formalized_löb_theorem : T₀ ⊢ 𝔅 (𝔅 σ ➝ σ) ➝ 𝔅 σ := by
  have h₁ : T₀ ⊢ 𝔅 (𝐊 σ) ➝ 𝔅 σ := kreisel_specAux₁;
  have : T₀ ⊢ (𝔅 σ ➝ σ) ➝ (𝔅 (𝐊 σ) ➝ σ) := CCC!_of_C!_left h₁;
  have : T ⊢ (𝔅 σ ➝ σ) ➝ 𝐊 σ := WeakerThan.pbl (𝓢 := T₀) $ C!_trans this kreisel_specAux₂;
  exact C!_trans (D2 ⨀ (D1 this)) h₁;

instance : 𝔅.FormalizedLöb := ⟨formalized_löb_theorem (T := T)⟩

/-
lemma unprovable_con_via_löb [Consistent T] [L.DecidableEq] [𝔅.Löb] : T ⊬ 𝔅.con := by
  by_contra hC;
  have : T ⊢ ⊥ := Löb.LT $ N!_iff_CO!.mp hC;
  have : ¬Consistent T := not_consistent_iff_inconsistent.mpr $ inconsistent_iff_provable_bot.mpr this
  contradiction
-/

lemma formalized_unprovable_not_con [Consistent T] [𝔅.Kreisel (gödel 𝔅)] : T ⊬ 𝔅.con ➝ ∼𝔅 (∼𝔅.con) := by
  by_contra hC;
  have : T ⊢ ∼𝔅.con := Löb.LT $ CN!_of_CN!_right hC;
  have : T ⊬ ∼𝔅.con := con_unrefutable;
  contradiction;

lemma formalized_unrefutable_gödel [Consistent T] [𝔅.Kreisel (gödel 𝔅)] : T ⊬ 𝔅.con ➝ ∼𝔅 (∼(gödel 𝔅)) := by
  by_contra hC;
  have : T ⊬ 𝔅.con ➝ ∼𝔅 (∼𝔅.con) := formalized_unprovable_not_con;
  have : T ⊢ 𝔅.con ➝ ∼𝔅 (∼𝔅.con) := C!_trans hC $ WeakerThan.pbl <| K!_left <| ENN!_of_E!
      <| prov_distribute_iff <| ENN!_of_E! <| WeakerThan.pbl gödel_iff_con;
  contradiction;

end Löb


section Rosser

variable {T₀ T : Theory L} [Diagonalization T₀] [T₀ ⪯ T] [Consistent T] {𝔅 : Provability T₀ T}

local notation "𝐑" => gödel 𝔅

theorem unrefutable_rosser [𝔅.Rosser] : T ⊬ ∼𝐑 := by
  intro hnρ;
  have hρ : T ⊢ 𝐑 := WeakerThan.pbl $ (K!_right gödel_spec) ⨀ (Ros hnρ);
  have : ¬Consistent T := not_consistent_iff_inconsistent.mpr $ inconsistent_iff_provable_bot.mpr <|
    (N!_iff_CO!.mp hnρ) ⨀ hρ;
  contradiction

theorem rosser_independent [L.DecidableEq] [𝔅.Rosser] : Independent T 𝐑 := by
  constructor
  . apply unprovable_gödel
  . apply unrefutable_rosser

theorem rosser_first_incompleteness [L.DecidableEq] (𝔅 : Provability T₀ T) [𝔅.Rosser] : Incomplete T :=
  incomplete_def.mpr ⟨gödel 𝔅, rosser_independent⟩

omit [Diagonalization T₀] [Consistent T] in
/-- If `𝔅` satisfies Rosser provability condition, then `𝔅.con` is provable from `T`. -/
theorem kriesel_remark [𝔅.Rosser] : T ⊢ 𝔅.con := by
  have : T₀ ⊢ ∼𝔅 ⊥ := Ros (N!_iff_CO!.mpr (by simp));
  exact WeakerThan.pbl $ this;

end Rosser

end ProvabilityAbstraction

end FirstOrder
