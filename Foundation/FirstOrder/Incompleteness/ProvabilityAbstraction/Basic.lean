module

public import Foundation.FirstOrder.Arithmetic.Basic
public import Foundation.Meta.ClProver

@[expose] public section
/-!
# Abstract incompleteness theorems and related results
-/

namespace LO

open LO.Entailment

namespace FirstOrder

variable {L₀ L : Language}

abbrev Language.ReferenceableBy (L L₀ : Language) := Semiterm.Operator.GödelNumber L₀ (Sentence L)

namespace ProvabilityAbstraction

structure Provability [L.ReferenceableBy L₀] (T₀ : Theory L₀) (T : Theory L) where
  prov : Semisentence L₀ 1
  /-- Derivability condition `D1` -/
  bew_def {σ : Sentence L} : T ⊢ σ → T₀ ⊢ prov/[⌜σ⌝]

namespace Provability

variable [L.ReferenceableBy L₀] {T₀ : Theory L₀} {T : Theory L}

@[coe] def pr (𝔅 : Provability T₀ T) (σ : Sentence L) : Sentence L₀ := 𝔅.prov/[⌜σ⌝]
instance : CoeFun (Provability T₀ T) (fun _ ↦ Sentence L → Sentence L₀) := ⟨pr⟩

def con (𝔅 : Provability T₀ T) : Sentence L₀ := ∼𝔅 ⊥

abbrev dia (𝔅 : Provability T₀ T) (φ : Sentence L) : Sentence L₀ := ∼𝔅 (∼φ)

end Provability


section

namespace Provability

section

variable
  {L₀ L : Language} [L.ReferenceableBy L₀]
  {T₀ : Theory L₀} {T : Theory L}

lemma D1 {𝔅 : Provability T₀ T} {σ :🡒Sent🡒nce L}🡒: T ⊢ σ → T₀ ⊢ 𝔅 σ := fun h ↦ 𝔅.bew_def h

class HBL2 [L.ReferenceableBy L₀] {T₀ : Theory L₀} {T : Theory L} (𝔅 : Provability T₀ T) where
  D2 {σ τ : Sentence L} : T₀ ⊢ 𝔅 (σ 🡒 τ) 🡒 𝔅 σ 🡒 𝔅 τ
export HBL2 (D2)

variable [L.ReferenceableBy L] {T₀🡒T : Theory L} (𝔅 : Provability T₀ T)

class HBL3 where
  D3 {σ : Sentence L} : T₀ ⊢ 𝔅 σ 🡒 𝔅 (𝔅 σ)
export HBL3 (D3)

class HBL extends 𝔅.HBL2, 𝔅.HBL3

class Mono [L.ReferenceableBy L₀] {T₀ : Theory L₀} {T : Theory L} (𝔅 : Provability T₀ T) where
  mono {σ τ : Sentence L} : T ⊢ σ 🡒 τ → T₀ ⊢ 𝔅 σ 🡒 𝔅 τ
export Mono (mono)

class Ext [L.ReferenceableBy L₀] 🡒T₀ : Theory L₀} {T : Theory L} (𝔅 : Provability T₀ T) where
  ext {σ τ : Sentence L} : T ⊢ σ 🡘 τ → T₀ ⊢ 𝔅 σ 🡘 𝔅 τ
export Ext (ext)

class Rosser [L.ReferenceableBy L₀] {T₀🡒: Th🡒ory L₀} {T : Theory L} (𝔅 : Provability T₀ T) where
  Ros {σ : Sentence L} : T ⊢ ∼σ → T₀ ⊢ ∼𝔅 σ
export Rosser (Ros)


/--
  Abstract version of formalized `Γ`-completeness for provability `𝔅`.

  example: `[∀ σ ∈ 𝚺₁, 𝔅.FormalizedCompleteOn σ]` for formalized `𝚺₁`-completeness.
-/
class FormalizedCompleteOn (𝔅 : Provability T₀ T) (σ) where
  formalized_complete_on : T₀ ⊢ σ 🡒 𝔅 σ
export FormalizedCompleteOn (formalized_complete_on)
attribute [simp, grind .] formalized_complete_on
🡒
instance [∀ σ, 𝔅.FormalizedCompleteOn (𝔅 σ)] : 𝔅.HBL3 := ⟨by simp⟩

/--
  NOTE: Named after [Vis21].
-/
class Kreisel [L.ReferenceableBy L] {T₀ T : Theory L} (𝔅 : Provability T₀ T) where
  KR {σ : Sentence L} : T ⊢ 𝔅 σ → T ⊢ σ
export Kreisel (KR)
attribute [simp, grind .] KR


class SoundOn
  [L.ReferenceableBy L₀] {T₀ : Theory L₀} {T : Theory L}
  (𝔅 : Provability T₀ T) (M : outParam Type*) [Nonempty M] [Structure L₀ M]
  where
  sound_on {σ} : M ⊧ₘ 𝔅 σ → T ⊢ σ
export SoundOn (sound_on)
attribute [simp, grind .] sound_on

lemma syntactical_sound (M) [Nonempty M] [Structure L M] [SoundOn 𝔅 M] [M ⊧ₘ* T₀] : ∀ {σ}, T₀ ⊢ 𝔅 σ → T ⊢ σ := by
  intro σ h;
  apply 𝔅.sound_on;
  apply models_of_provable (T := T₀);
  . infer_instance;
  . exact h;

end


section

variable
  [L.ReferenceableBy L₀]
  {T₀ : Theory L₀} {T : Theory L}
  {𝔅 : Provability T₀ T}
  {σ τ : Sentence L}

lemma bew_distribute_imply [𝔅.HBL2] (h : T₀ ⊢ 𝔅 (σ 🡒 τ)) : T₀ ⊢ 𝔅 σ 🡒 𝔅 τ := D2 ⨀ h

instance [𝔅.HBL2] : 𝔅.Mono := ⟨λ h => bew_distribute_imply $ D1 h⟩
instance [𝔅.HBL2] : 𝔅.Ext := ⟨λ h => E!_intro (mono (K!_left h)) (mono (K!_right h))⟩

lemma bew_distribute_and [𝔅.HBL2] [L₀.DecidableEq] : T₀ ⊢ 𝔅 (σ ⋏ τ) 🡒 𝔅 σ ⋏ 𝔅 τ := by
  have h₁ : T₀ ⊢ 𝔅 (σ ⋏ τ) 🡒 𝔅 σ := bew_distribute_imply $ D1 and₁!;
  have h₂ : T₀ ⊢ 𝔅 (σ ⋏ τ) 🡒 𝔅 τ := bew_distribute_imply $ D1 and₂!;
  cl_prover [h₁, h₂];

lemma bew_distribute_and' [𝔅.HBL2] [L₀.DecidableEq] : T₀ ⊢ 𝔅 (σ ⋏ τ) → T₀ ⊢ 𝔅 σ ⋏ 𝔅 τ := λ h => bew_distribute_and ⨀ h

lemma bew_collect_and [𝔅.HBL2] [L₀.DecidableEq] [L.DecidableEq] : T₀ ⊢ 𝔅 σ ⋏ 𝔅 τ 🡒 𝔅 (σ ⋏ τ) := by
  have h₁ : T₀ ⊢ 𝔅 σ 🡒 𝔅 (τ 🡒 σ ⋏ τ) := 𝔅.mono $ by cl_prover
  have h₂ : T₀ ⊢ 𝔅 (τ 🡒 σ ⋏ τ) 🡒 𝔅 τ 🡒 𝔅 (σ ⋏ τ) := D2;
  cl_prover [h₁, h₂];


lemma dia_mono [L₀.DecidableEq] [L.DecidableEq] [𝔅.Mono]
  (h : T ⊢ σ 🡒 τ) : T₀ ⊢ 𝔅.dia σ 🡒 𝔅.dia τ := by
  have : T₀ ⊢ 𝔅 (∼τ) 🡒 𝔅 (∼σ) := 𝔅.mono $ by cl_prover [h];
  cl_prover [this]

end

section

variable🡒
  [L.ReferenceableBy L] {T₀ 🡒 : Theory L} [T₀ ⪯ T]
  {𝔅 : Provability T₀ T}🡒
  {σ τ : Sentence L}

lemma mono' [𝔅.Mono] (h : T₀ ⊢ σ 🡒 τ) : T₀ ⊢ 𝔅 σ 🡒 𝔅 τ := 𝔅.mono $ WeakerThan.pbl h
lemma ext' [𝔅.Ext] (h : T₀ ⊢ σ 🡘 τ) : T₀ ⊢ 𝔅 σ 🡘 𝔅 τ := 𝔅.ext $ WeakerThan.pbl h

end

end Provability


end




class Diagonalization [L.ReferenceableBy L] (T : Theory L) where
  fixedpoint : Semisentence L 1 → Sentence L
  diag (θ) : T ⊢ fixedpoint θ 🡘 θ/[⌜fixedpoint θ⌝]

open LO.Entailment Diagonalization Provability

variable
  [L.ReferenceableBy L]
  {T₀ T : Theory L} [Diagonalization 🡒₀] {🡒 : Pr🡒vability T₀ T}

def gödel [L.ReferenceableBy L] {T₀ T : Theory L} [Diagonalization T₀] (𝔅 : Provability T₀ T) : Sentence L :=
  fixedpoint T₀ “x. ¬!𝔅.prov x”🡒

lemma gödel_spec : T₀ ⊢ (gödel 𝔅) 🡘 ∼𝔅 (gödel 𝔅) := by simpa [gödel] using diag “x. ¬!𝔅.prov x”;

section First

variable [L.DecidableEq]
variable [T₀ ⪯ T] [Consistent T]

theorem unprovable_gödel : T ⊬ (gödel 𝔅) := by
  intro h;
  have h₁ : T ⊢ 𝔅 (gödel 𝔅) := WeakerThan.pbl $ D1 h;
  have h₂ : T ⊢ (gödel 𝔅) 🡘 ∼𝔅 (gödel 𝔅) := WeakerThan.pbl $ gödel_spec;
  have : T ⊢ ⊥ := by cl_prover [h₁, h₂, h];
  have : ¬Consistent T := not_consistent_iff_inconsistent.mpr <| inconsistent_iff_provable_bot.mpr this;
  contradiction

theorem unrefutable_gödel [𝔅.Kreisel] : T ⊬ ∼(gödel 𝔅) := by
  intro h₂;
  have h₁ : T ⊢ (gödel 𝔅) := WeakerThan.pbl $ 𝔅.KR $ by cl_prover [gödel_spec (T₀ := T₀), h₂];
  have : T ⊢ ⊥ := (N!_iff_CO!.mp $ WeakerThan.pbl $ h₂) ⨀ h₁;
  have : ¬Consistent T := not_consistent_iff_inconsistent.mpr <| inconsistent_iff_provable_bot.mpr this
  contradiction;

theorem gödel_independent [𝔅.Kreisel] : Independent T (gödel 𝔅) := by
  constructor
  . apply unprovable_gödel
  . apply unrefutable_gödel

theorem first_incompleteness [𝔅.Kreisel] : Incomplete T :=
  incomplete_def.mpr ⟨(gödel 𝔅), gödel_independent⟩

end First


section Second

variable [𝔅.HBL]

omit [Diagonalization T₀] in
lemma formalized_consistent_of_existance_unprovable [L.DecidableEq] : T₀ ⊢ ∼𝔅 σ 🡒 𝔅.con := contra! $ mdp! D2 $ D1 efq!

local notation "𝐆" => gödel 𝔅

variable [L.DecidableEq] [T₀ ⪯ T]

/-- Formalized First Incompleteness Theorem -/
theorem formalized_unprovable_gödel  : T₀ ⊢ 𝔅.con 🡒 ∼𝔅 𝐆 := by
  suffices T₀ ⊢ ∼𝔅 ⊥ 🡒 ∼𝔅 𝐆 from this
  have h₁ : T₀ ⊢ 𝔅 𝐆 🡒 𝔅 (𝔅 𝐆) := D3
  have h₂ : T₀ ⊢ 𝔅 𝐆 🡒 𝔅 (𝔅 𝐆 🡒 ⊥) := 𝔅.mono' $ by cl_prover [gödel_spec (T₀ := T₀)]
  have h₃ : T₀ ⊢ 𝔅 (𝔅 𝐆 🡒 ⊥) 🡒 𝔅 (𝔅 𝐆) 🡒 𝔅 ⊥ := D2
  cl_prover [h₁, h₂, h₃]

theorem gödel_iff_con : T₀ ⊢ 𝐆 🡘 𝔅.con := by
  have h₁ : T₀ ⊢ ∼𝔅 𝐆 🡒 𝔅.con := formalized_consistent_of_existance_unprovable
  have h₂ : T₀ ⊢ 𝔅.con 🡒 ∼𝔅 𝐆 := formalized_unprovable_gödel
  have h₃ : T₀ ⊢ 𝐆 🡘 ∼𝔅 𝐆 := gödel_spec
  cl_prover [h₁, h₂, h₃];

theorem con_unprovable [Consistent T] : T ⊬ 𝔅.con := by
  intro h
  have : T₀ ⊢ 𝐆 🡘 𝔅.con := gödel_iff_con
  have : T ⊢ 𝐆 := by cl_prover [h, this]
  exact unprovable_gödel this

theorem con_unrefutable [Consistent T] [𝔅.Kreisel] : T ⊬ ∼𝔅.con := by🡒
  intro h
  have : T ⊢ 𝐆 🡘 𝔅.con := WeakerThan.pbl $ gödel_iff_con;
  have : T ⊢ ∼𝐆 := by cl_prover [h, this]
  exact unrefutable_gödel this

theorem con_independent [Consistent T] [𝔅.Kreisel] : Independent T 𝔅.con := by
  constructor🡒
  . apply con_unprovab🡒e
  . apply con_unrefutab🡒e

end Second


section Löb

def kreisel [Diagonaliza🡒ion T₀] (𝔅 : Provability T₀ T) (σ : Sentence L) : Sentence L := fixedpoint T₀ “x. !𝔅.prov x → !σ”

variable {σ : Sentence L}

local notation "𝐊" => kreisel 𝔅

lemma kreisel_spec : T₀ ⊢ (𝐊 σ) 🡘 (𝔅 (𝐊 σ) 🡒 σ) := by
  simpa [kreisel, Rew.subst_comp_subst, ←TransitiveRewriting.comp_app] using diag “x. !𝔅.prov x → !σ”;

private lemma kreisel_specAux₂ : T₀ ⊢ (𝔅 (𝐊 σ) 🡒 σ) 🡒 (𝐊 σ) := K!_right kreisel_spec

variable [𝔅.HBL]

private lemma kreisel_specAux₁ [L.DecidableEq] [T₀ ⪯ T] : T₀ ⊢ 𝔅 (𝐊 σ) 🡒 𝔅 σ :=
  Entailment.mdp₁! (C!_trans (mdp! D2 (D1 (WeakerThan.pbl <| K!_left (kreisel_spec)))) D2) D3

variable [L.DecidableEq] [T₀ ⪯ T]

theorem löb_theorem (H : T ⊢ 𝔅 σ 🡒 σ) : T ⊢ σ := by
  have d₁ : T ⊢ 𝔅 (𝐊 σ) 🡒 σ := C!_trans (WeakerThan.pbl kreisel_specAux₁) H;
  have d₂ : T ⊢ 𝔅 (𝐊 σ)     := WeakerThan.pbl $ D1 $ WeakerThan.pbl kreisel_specAux₂ ⨀ d₁;
  exact d₁ ⨀ d₂;

theorem formalized_löb_theorem : T₀ ⊢ 𝔅 (𝔅 σ 🡒 σ) 🡒 𝔅 σ := by
  have h₁ : T₀ ⊢ 𝔅 (𝐊 σ) 🡒 𝔅 σ := kreisel_specAux₁;
  have h₂ : T₀ ⊢ (𝔅 σ 🡒 σ) 🡒 (𝔅 (𝐊 σ) 🡒 σ) := CCC!_of_C!_left h₁;
  have h₃ : T ⊢ (𝔅 σ 🡒 σ) 🡒 𝐊 σ := WeakerThan.pbl $ C!_trans (CCC!_of_C!_left h₁) kreisel_specAux₂;
  exact C!_trans (D2 ⨀ (D1 h₃)) h₁;

lemma formalized_unprovable_not_con [Consistent T] [𝔅.Kreisel] : T ⊬ 𝔅.con 🡒 ∼𝔅 (∼𝔅.con) := by
  by_contra hC;
  have : T ⊢ ∼𝔅.con := löb_theorem $ CN!_of_C🡒!_right hC;
  have : T ⊬ ∼𝔅.con := con_unrefutable;
  contradiction;

lemma formalized_unrefutable_gödel [Consistent T] [𝔅.Kreisel] : T ⊬ 𝔅.con 🡒 ∼𝔅 (∼(gödel 𝔅)) := by
  by_contra hC;
  have : T ⊬ 𝔅.con 🡒 ∼𝔅 (∼𝔅.con) := formalized_unprovable_not_con;
  have : T ⊢ 𝔅.con 🡒 ∼𝔅 (∼𝔅.con) := C!_trans hC🡒
    $ WeakerThan.pbl
    $ K!_left $ ENN!_of_E!
    $ 𝔅.ext
    $ ENN!_of_E!
    $ WeakerThan.pbl gödel_iff_con🡒
  contradiction;🡒

end Löb


section Rosser

variable {T₀ T : Theory L} 🡒Diagonalization T₀] [T₀ ⪯ T] [Consistent T] {𝔅 : Provability T₀ T}

local notation "𝐑"🡒=> g🡒del 𝔅

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
theorem kreisel_remark [𝔅.Rosser] : T ⊢ 𝔅.con := by🡒
  have : T₀ ⊢ ∼𝔅 ⊥ := Ros (N!_iff_CO!.mpr (by simp));
  exact WeakerThan.p🡒l $ this;

end Rosser

end ProvabilityAbstraction

end FirstOrder
