module

public import Foundation.FirstOrder.Arithmetic.ISigma1.Prenex
public import Foundation.FirstOrder.Incompleteness.Consistency
public import Foundation.ProvabilityLogic.Arithmetic.SolovaySentences

/-!
# Modified Solovay sentences

Solovay sentences for the root extension of a strong reflexive countermodel of `A` whose limit
jumps from the old root to the reflexive world `u` once a witness of `σ` appears, and the
reflection principle for `σ` that they yield.

For a `𝚫₁`-axiomatized `T` extending `𝗜𝚺₁` and a `𝚺₁` sentence `σ`, they are constructed as the
arithmetical fixed points `T.modifiedSolovay M σ θ`. Along each edge of `M.extendRoot` a trigger
fires: a proof of `∼Λ z`, or a witness of `σ` on the edge from the old root to `u`; the limit
follows the edge whose trigger fires first.

## References

- [Bek90, §6 Lemma 1, Lemma 1.7, Lemma 1.8, Lemma 2, Theorem 2]
- [AB05, Lemma 51, Lemma 53]
-/

@[expose] public section

namespace FFL

open Entailment

namespace ProvabilityLogic.Kripke

open Model Model.World

/-- A rooted countermodel of `A` with an `A`-reflexive world `u` whose only predecessor is the
root.

- [Bek90, §6 Theorem 2]
-/
structure StrongReflexiveCountermodel (κ : Type*) [Nonempty κ] {α : Type*} [DecidableEq α]
    (A : Formula α) extends RootedModel κ α where
  root_not_forces : root ⊮[_] A
  u : toModel.World
  root_rel_u : root ≺ u
  isReflexiveOf_u : u.IsReflexiveOf A.subfmls.prebox
  eq_root_of_rel_u : ∀ z : toModel.World, z ≺ u → z = root

end ProvabilityLogic.Kripke

namespace FirstOrder.ProvabilityAbstraction

open ProvabilityLogic Kripke Model Model.World RootedModel

variable {L : Language} [L.ReferenceableBy L] {T₀ T : Theory L} [T₀ ⪯ T]
         {𝔅 : Provability T₀ T} [𝔅.HBL]
         {κ α : Type*} [Nonempty κ] [DecidableEq α] {A : ProvabilityLogic.Formula α}

open Classical in
/-- Sentences indexed by the worlds of `M.extendRoot` satisfying the Solovay conditions of the
construction whose limit jumps from the old root to `u` once a witness of `σ` is found.

- [Bek90, §6 Lemma 1]
-/
structure Provability.ModifiedSolovaySentences
    (𝔅 : Provability T₀ T) (M : StrongReflexiveCountermodel κ A) [Fintype M.World]
    (σ : Sentence L) where
  Λ : M.extendRoot.World → Sentence L
  protected SC1 : ∀ i j, i ≠ j → T₀ ⊢ Λ i 🡒 ∼Λ j
  protected SC2 : ∀ i j : M.extendRoot.World, i ≺ j → j ≠ some M.u → T₀ ⊢ Λ i 🡒 𝔅.dia (Λ j)
  protected SC3 : ∀ i : M.extendRoot.World, i ≠ none → i ≠ some M.u →
    T₀ ⊢ Λ i 🡒 𝔅 (⩖ j ∈ { j : M.extendRoot.World | i ≺ j }, Λ j)
  protected SC3r : T₀ ⊢ Λ (some M.u) 🡒
    𝔅 (Λ (some M.u) ⋎ ⩖ j ∈ { j : M.extendRoot.World | some M.u ≺ j }, Λ j)
  protected SC4 : T₀ ⊢ ⩖ j, Λ j
  protected SC5 : T₀ ⊢ 𝔅 σ 🡒 ∼Λ none
  protected SC6 : T₀ ⊢ ∼σ 🡒 ∼Λ (some M.u)

namespace Provability.ModifiedSolovaySentences

variable {M : StrongReflexiveCountermodel κ A} [Fintype M.World] {σ : Sentence L}

attribute [coe] Λ

instance : CoeFun (𝔅.ModifiedSolovaySentences M σ) (fun _ ↦ M.extendRoot.World → Sentence L) :=
  ⟨Λ⟩

variable (S : 𝔅.ModifiedSolovaySentences M σ)

open Classical in
noncomputable def realization : Realization α L :=
  ⟨fun a ↦ ⩖ i ∈ { i : M.extendRoot.World | i ⊩[_] #a }, S i⟩

variable [M.IsGL] {i : M.extendRoot.World}

private lemma mainlemma_aux (hi : i ≠ none) {B : ProvabilityLogic.Formula α}
    (hB : B ∈ A.subfmls) :
    (i ⊩[_] B → T₀ ⊢ S i 🡒 B.interpret S.realization 𝔅) ∧
    (i ⊮[_] B → T₀ ⊢ S i 🡒 ∼B.interpret S.realization 𝔅) := by
  classical
  induction B generalizing i with
  | falsum => simp [Formula.interpret];
  | atom a =>
    constructor;
    · exact fun h ↦ right_Fdisj'_intro _ _ (by simpa using h);
    · exact fun h ↦ CN_of_CN_right <| left_Fdisj'_intro _ _ fun j hj ↦ S.SC1 _ _ <| by
        rintro rfl;
        simp_all;
  | imp B C ihB ihC =>
    replace ihB := ihB hi (Formula.subfmls_trans hB (by grind));
    replace ihC := ihC hi (Formula.subfmls_trans hB (by grind));
    constructor;
    · intro h;
      rcases forces_imp.mp h with hB | hC;
      · exact C_trans (ihB.2 hB) CNC;
      · exact C_trans (ihC.1 hC) implyK;
    · intro h;
      obtain ⟨hB, hC⟩ := not_forces_imp.mp h;
      exact CNC_of_C_of_CN (ihB.1 hB) (ihC.2 hC);
  | box B ih =>
    replace ih := fun {j} (hj : j ≠ none) ↦ ih hj (Formula.subfmls_trans hB (by grind));
    have hne {j : M.extendRoot.World} (Rij : i ≺ j) : j ≠ none := by rintro rfl; simp_all;
    have hu : some M.u ⊩[_] □B → some M.u ⊩[_] B :=
      fun h ↦ extendRoot.forces_some.mpr <|
        M.isReflexiveOf_u B (FormulaFinset.mem_prebox.mpr hB) (extendRoot.forces_some.mp h);
    constructor;
    · intro h;
      have h₁ : T₀ ⊢ (⩖ j ∈ { j : M.extendRoot.World | i ≺ j }, S j) 🡒
          B.interpret S.realization 𝔅 :=
        left_Fdisj'_intro _ _ fun j hj ↦ (ih (hne (by simpa using hj))).1 (h j (by simpa using hj));
      rcases eq_or_ne i (some M.u) with rfl | hiu;
      · exact C_trans S.SC3r <| 𝔅.mono' <| left_A_intro ((ih hi).1 (hu h)) h₁;
      · exact C_trans (S.SC3 i hi hiu) <| 𝔅.mono' h₁;
    · intro h;
      obtain ⟨j, Rij, hj⟩ := not_forces_box.mp h;
      obtain ⟨y, ⟨Riy, hy⟩, hymax⟩ :=
        M.extendRoot.terminalOf { y | i ≺ y ∧ y ⊮[_] B } ⟨j, Rij, hj⟩;
      have hyu : y ≠ some M.u := by
        rintro rfl;
        exact hy <| hu fun z Ryz ↦ of_not_not fun hz ↦
          hymax z ⟨IsTrans.trans _ _ _ Riy Ryz, hz⟩ Ryz;
      exact C_trans (S.SC2 i y Riy hyu) <| contra <| 𝔅.mono' <| CN_of_CN_right <|
        (ih (hne Riy)).2 hy;

/-- - [Bek90, §6 Lemma 2]
- [AB05, Lemma 53]
-/
theorem mainlemma (hi : i ≠ none) {B : ProvabilityLogic.Formula α} (hB : B ∈ A.subfmls) :
    i ⊩[_] B → T₀ ⊢ S i 🡒 B.interpret S.realization 𝔅 :=
  (S.mainlemma_aux hi hB).1

/-- - [Bek90, §6 Lemma 2]
- [AB05, Lemma 53]
-/
theorem mainlemma_neg (hi : i ≠ none) {B : ProvabilityLogic.Formula α} (hB : B ∈ A.subfmls) :
    i ⊮[_] B → T₀ ⊢ S i 🡒 ∼B.interpret S.realization 𝔅 :=
  (S.mainlemma_aux hi hB).2

lemma provable_boxItr_bot_of_ne {z : M.World}
    (hr : z ≠ M.root) (hu : z ≠ M.u) :
    T₀ ⊢ S (some z) 🡒 𝔅^[z.rank + 1] ⊥ := by
  classical
  induction z using WellFounded.induction IsConverseWellFounded.cwf (r := flip M.Rel) with
  | h z ih =>
    suffices T₀ ⊢ (⩖ j ∈ { j : M.extendRoot.World | some z ≺ j }, S j) 🡒
        𝔅^[z.rank] ⊥ by
      simpa only [Function.iterate_succ_apply'] using
        C_trans (S.SC3 (some z) (by simp) (by simpa using hu)) (𝔅.mono' this);
    apply left_Fdisj'_intro;
    rintro (_ | y) hy;
    · simp at hy;
    · replace hy : z ≺ y := by simpa using hy;
      exact C_trans (ih y hy (by rintro rfl; exact not_rel_root hy)
        (by rintro rfl; exact hr <| M.eq_root_of_rel_u z hy)) <|
        𝔅.provable_boxItr_bot_mono <| rank_lt_of_rel hy;

lemma provable_b :
    T₀ ⊢ 𝔅.conItr M.height 🡒 𝔅 σ 🡒 ∼σ 🡒 S (some M.root) := by
  classical
  suffices T₀ ⊢ (⩖ j, S j) 🡒 ∼𝔅^[M.height] ⊥ 🡒 𝔅 σ 🡒 ∼σ 🡒 S (some M.root) from
    this ⨀ S.SC4;
  apply left_Udisj_intro;
  rintro (_ | z);
  · cl_prover [S.SC5];
  rcases eq_or_ne z M.root with rfl | hr;
  · cl_prover;
  rcases eq_or_ne z M.u with rfl | hu;
  · cl_prover [S.SC6];
  cl_prover [C_trans (S.provable_boxItr_bot_of_ne hr hu) <|
    𝔅.provable_boxItr_bot_mono <| rank_lt_height <| M.root_rel z hr];

/-- Provably in `T₀`, the `M.height`-times iterated consistency and the realization of `A` yield
the reflection instance `𝔅 σ 🡒 σ`.

- [Bek90, §6 Theorem 2]
- [AB05, Lemma 51]
-/
theorem reflection :
    T₀ ⊢ 𝔅.conItr M.height 🡒 A.interpret S.realization 𝔅 🡒 𝔅 σ 🡒 σ := by
  cl_prover [S.provable_b, S.mainlemma_neg (Option.some_ne_none M.root) Formula.mem_subfmls_self <|
    extendRoot.forces_some.not.mpr M.root_not_forces];

end Provability.ModifiedSolovaySentences

end FirstOrder.ProvabilityAbstraction

noncomputable section

namespace FirstOrder.Arithmetic.Bootstrapping.ModifiedSolovaySentences

open ProvabilityLogic Kripke Model

section comparison

variable {V : Type*} [ORingStructure V]

/-- A witness of `P` appears no later than any witness of `Q`. -/
def WitnessLE (P Q : V → Prop) : Prop := ∃ w, P w ∧ ∀ v < w, ¬Q v

/-- A witness of `P` appears strictly before any witness of `Q`. -/
def WitnessLT (P Q : V → Prop) : Prop := ∃ w, P w ∧ ∀ v ≤ w, ¬Q v

def cmpLE (P : 𝚺₁.Semisentence 2) (Q : 𝚷₁.Semisentence 2) : 𝚺₁.Semisentence 2 := .mkSigma
  “a b. ∃ w, !P.val w a ∧ ∀ v < w, ¬!Q.val v b”

def cmpLT (P : 𝚺₁.Semisentence 2) (Q : 𝚷₁.Semisentence 2) : 𝚺₁.Semisentence 2 := .mkSigma
  “a b. ∃ w, !P.val w a ∧ ∀ v <⁺ w, ¬!Q.val v b”

@[simp] lemma val_cmpLE {P : 𝚺₁.Semisentence 2} {Q : 𝚷₁.Semisentence 2} {a b : V} :
    V ⊧/![a, b] (cmpLE P Q).val ↔
      WitnessLE (fun w ↦ V ⊧/![w, a] P.val) (fun w ↦ V ⊧/![w, b] Q.val) := by
  simp [cmpLE, WitnessLE]

@[simp] lemma val_cmpLT [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {P : 𝚺₁.Semisentence 2} {Q : 𝚷₁.Semisentence 2} {a b : V} :
    V ⊧/![a, b] (cmpLT P Q).val ↔
      WitnessLT (fun w ↦ V ⊧/![w, a] P.val) (fun w ↦ V ⊧/![w, b] Q.val) := by
  simp [cmpLT, WitnessLT, Semiformula.ballLTSucc, lt_succ_iff_le]

variable {P Q : V → Prop}

lemma WitnessLE.exists : WitnessLE P Q → ∃ w, P w := fun ⟨w, hw, _⟩ ↦ ⟨w, hw⟩

lemma WitnessLE.not_witnessLT [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] : WitnessLE P Q → ¬WitnessLT Q P := by
  rintro ⟨w, hw, h⟩ ⟨w', hw', h'⟩;
  rcases lt_or_ge w' w with hlt | hge;
  · exact h w' hlt hw';
  · exact h' w hge hw;

lemma exists_witnessFirst [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {ι : Type*} [Finite ι] (P : ι → V → Prop)
    (hP : ∀ i, 𝚺₁-Predicate (P i)) (o : ι → ℕ) (h : ∃ i w, P i w) :
    ∃ j, (∀ i, o i < o j → WitnessLT (P j) (P i)) ∧ ∀ i, o j ≤ o i → WitnessLE (P j) (P i) := by
  obtain ⟨i₀, w₀, h₀⟩ := h;
  obtain ⟨w, ⟨i₁, h₁⟩, hw⟩ : ∃ w, (∃ i, P i w) ∧ ∀ v < w, ¬∃ i, P i v :=
    InductionOnBroadHierarchy.least_number_sigma 𝚺 1 (HierarchySymbol.Definable.fintype_exs hP)
      ⟨i₀, h₀⟩;
  obtain ⟨j, hj, hmin⟩ := (InvImage.wf o wellFounded_lt).has_min {i | P i w} ⟨i₁, h₁⟩;
  use j;
  and_intros;
  · intro i hi;
    use w, hj;
    intro v hv hv';
    rcases hv.lt_or_eq with hlt | rfl;
    · exact hw v hlt ⟨i, hv'⟩;
    · exact hmin i hv' hi;
  · exact fun i _ ↦ ⟨w, hj, fun v hv hv' ↦ hw v hv ⟨i, hv'⟩⟩;

end comparison

variable {κ α : Type*} [Nonempty κ] [DecidableEq α] {A : ProvabilityLogic.Formula α}
  (T : ArithmeticTheory) [T.Δ₁] (M : StrongReflexiveCountermodel κ A) [Fintype M.World]
  (σ : ArithmeticSentence) (θ : 𝚺₀.Semisentence 1)

section stx

open Classical in
/-- The targets of the edges from `x`. -/
def next (x : M.extendRoot.World) : Finset M.extendRoot.World :=
  {z | (x ≺ z ∧ z ≠ some M.u) ∨ (x = some M.root ∧ z = some M.u)}

variable {M} in
@[simp] lemma mem_next {x z : M.extendRoot.World} :
    z ∈ next M x ↔ (x ≺ z ∧ z ≠ some M.u) ∨ (x = some M.root ∧ z = some M.u) := by
  simp [next]

variable {M} in
lemma rel_of_mem_next {x z : M.extendRoot.World} (h : z ∈ next M x) : x ≺ z := by
  rcases mem_next.mp h with h | ⟨rfl, rfl⟩;
  · exact h.1;
  · exact M.root_rel_u;

open Classical in
/-- A total order on the worlds of `M.extendRoot` in which `u` is the largest. -/
def ord (z : M.extendRoot.World) : ℕ :=
  if z = some M.u then Fintype.card M.extendRoot.World else Fintype.equivFin _ z

variable {M} in
lemma ord_injective : Function.Injective (ord M) := by
  intro a b h;
  unfold ord at h;
  split_ifs at h with ha hb hb;
  · exact ha.trans hb.symm;
  · exact absurd h (Fintype.equivFin _ b).isLt.ne';
  · exact absurd h (Fintype.equivFin _ a).isLt.ne;
  · exact (Fintype.equivFin _).injective (Fin.val_injective h);

def prfNegSigma : 𝚺₁.Semisentence 2 := .mkSigma
  “w e. ∃ n, !(negGraph ℒₒᵣ) n e ∧ !(proof T).sigma w n”

def prfNegPi : 𝚷₁.Semisentence 2 := .mkPi
  “w e. ∀ n, !(negGraph ℒₒᵣ) n e → !(proof T).pi w n”

open Classical in
/-- The witnesses of the trigger of an edge into `z`. -/
def trigSigma (z : M.extendRoot.World) : 𝚺₁.Semisentence 2 :=
  if z = some M.u then .mkSigma “w e. !θ.val w” else prfNegSigma T

open Classical in
def trigPi (z : M.extendRoot.World) : 𝚷₁.Semisentence 2 :=
  if z = some M.u then .mkPi “w e. !θ.val w” else prfNegPi T

variable {n : ℕ} (t : M.extendRoot.World → ArithmeticSemiterm Empty n)

def stpAux (x y : M.extendRoot.World) : ArithmeticSemisentence n :=
  (⩕ z ∈ {z ∈ next M x | ord M z < ord M y},
    (cmpLT (trigSigma T M θ y) (trigPi T M θ z)).val/[t y, t z]) ⋏
  (⩕ z ∈ {z ∈ next M x | ord M y ≤ ord M z},
    (cmpLE (trigSigma T M θ y) (trigPi T M θ z)).val/[t y, t z])

def chainAux : List M.extendRoot.World → ArithmeticSemisentence n
  |          [] => ⊥
  |         [_] => ⊤
  | y :: x :: ε => chainAux (x :: ε) ⋏ stpAux T M θ t x y

open Classical in
def notTrigAux (z : M.extendRoot.World) : ArithmeticSemisentence n :=
  if z = some M.u then Rew.embSubsts ![] ▹ ∼σ else T.consistentWith.val/[t z]

section rew

variable {n' : ℕ} (w : Fin n → ArithmeticSemiterm Empty n')

lemma rew_stpAux (x y : M.extendRoot.World) :
    Rew.subst w ▹ stpAux T M θ t x y = stpAux T M θ (fun z ↦ Rew.subst w (t z)) x y := by
  simp [stpAux, Finset.map_conj', Function.comp_def, ← TransitiveRewriting.comp_app,
    Rew.subst_comp_subst, Matrix.comp_vecCons', Matrix.constant_eq_singleton]

lemma rew_chainAux (ε : List M.extendRoot.World) :
    Rew.subst w ▹ chainAux T M θ t ε = chainAux T M θ (fun z ↦ Rew.subst w (t z)) ε := by
  match ε with
  |          [] => simp [chainAux]
  |         [_] => simp [chainAux]
  | _ :: x :: ε => simp [chainAux, rew_chainAux (x :: ε), rew_stpAux]

omit [Fintype M.World] in
lemma rew_notTrigAux (z : M.extendRoot.World) :
    Rew.subst w ▹ notTrigAux T M σ t z = notTrigAux T M σ (fun z ↦ Rew.subst w (t z)) z := by
  unfold notTrigAux;
  split_ifs <;> simp [← TransitiveRewriting.comp_app, Rew.subst_comp_embSubsts,
    Rew.subst_comp_subst, Matrix.empty_eq]

end rew

/-- The sequences from the root `none` to `x` along the edges, listed from `x`. -/
abbrev EChain (x : M.extendRoot.World) :=
  {ε : List M.extendRoot.World // ε.ChainI (fun a b ↦ a ∈ next M b) x none}

variable [M.IsGL]

instance (x : M.extendRoot.World) : Finite (EChain M x) := by
  have mono {a b : M.extendRoot.World} {l : List M.extendRoot.World}
      (h : l.ChainI (fun a b ↦ a ∈ next M b) a b) : l.ChainI (fun a b ↦ b ≺ a) a b := by
    induction h with
    | singleton => exact .singleton _
    | cons hR _ ih => exact .cons (rel_of_mem_next hR) ih;
  exact Finite.of_injective _
    (Subtype.impEmbedding _ _ fun _ ↦ mono).injective

def HAux (x : M.extendRoot.World) : ArithmeticSemisentence n :=
  haveI := Fintype.ofFinite (EChain M x);
  ⩖ ε : EChain M x, chainAux T M θ t ε

def deltaAux (x : M.extendRoot.World) : ArithmeticSemisentence n :=
  HAux T M θ t x ⋏ ⩕ z ∈ next M x, notTrigAux T M σ t z

/-- The modified Solovay sentences.

- [Bek90, §6 Theorem 2]
-/
def _root_.FFL.FirstOrder.Theory.modifiedSolovay (x : M.extendRoot.World) : ArithmeticSentence :=
  exclusiveMultifixedpoint
    (fun j ↦ deltaAux T M σ θ (fun z ↦ #(Fintype.equivFin _ z)) ((Fintype.equivFin _).symm j))
    (Fintype.equivFin _ x)

abbrev stp (x y : M.extendRoot.World) : ArithmeticSentence :=
  stpAux T M θ (fun z ↦ ⌜T.modifiedSolovay M σ θ z⌝) x y

abbrev chain (ε : List M.extendRoot.World) : ArithmeticSentence :=
  chainAux T M θ (fun z ↦ ⌜T.modifiedSolovay M σ θ z⌝) ε

abbrev H (x : M.extendRoot.World) : ArithmeticSentence :=
  HAux T M θ (fun z ↦ ⌜T.modifiedSolovay M σ θ z⌝) x

abbrev notTrig (z : M.extendRoot.World) : ArithmeticSentence :=
  notTrigAux T M σ (fun z ↦ ⌜T.modifiedSolovay M σ θ z⌝) z

lemma H_sigma_one (x : M.extendRoot.World) : Hierarchy 𝚺 1 (H T M σ θ x) := by
  have h (ε : List M.extendRoot.World) : Hierarchy 𝚺 1 (chain T M σ θ ε) := by
    induction ε with
    | nil => simp [chainAux]
    | cons y ε ih => rcases ε with _ | ⟨x, ε⟩ <;> simp_all [chainAux, stpAux];
  simp [HAux, h]

lemma modifiedSolovay_diag (x : M.extendRoot.World) :
    𝗜𝚺₁ ⊢ T.modifiedSolovay M σ θ x 🡘 H T M σ θ x ⋏ ⩕ z ∈ next M x, notTrig T M σ θ z := by
  have : 𝗜𝚺₁ ⊢ T.modifiedSolovay M σ θ x 🡘
      (Rew.subst fun j ↦ ⌜T.modifiedSolovay M σ θ ((Fintype.equivFin _).symm j)⌝) ▹
        deltaAux T M σ θ (fun z ↦ #(Fintype.equivFin _ z)) x := by
    simpa [Theory.modifiedSolovay] using! exclusiveMultidiagonal (i := Fintype.equivFin _ x)
      (fun j ↦ deltaAux T M σ θ (fun z ↦ #(Fintype.equivFin _ z)) ((Fintype.equivFin _).symm j));
  simpa [deltaAux, HAux, Finset.map_conj', Finset.map_udisj, Function.comp_def, rew_chainAux,
    rew_notTrigAux] using! this

end stx

section model

variable [M.IsGL] (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open Classical in
/-- `w` witnesses the trigger of an edge into `z`. -/
def Wit (z : M.extendRoot.World) (w : V) : Prop :=
  if z = some M.u then V ⊧/![w] θ.val else Proof T w ⌜∼T.modifiedSolovay M σ θ z⌝

open Classical in
/-- The trigger of an edge into `z` is pulled. -/
def Trig (z : M.extendRoot.World) : Prop :=
  if z = some M.u then V ⊧/![] σ else Provable T (⌜∼T.modifiedSolovay M σ θ z⌝ : V)

/-- The edge `x → y` is the one taken from `x`. -/
def Step (x y : M.extendRoot.World) : Prop :=
  y ∈ next M x ∧
    (∀ z ∈ next M x, ord M z < ord M y → WitnessLT (Wit T M σ θ V y) (Wit T M σ θ V z)) ∧
    (∀ z ∈ next M x, ord M y ≤ ord M z → WitnessLE (Wit T M σ θ V y) (Wit T M σ θ V z))

abbrev Reach (x : M.extendRoot.World) : Prop := Relation.ReflTransGen (Step T M σ θ V) none x

def _root_.FFL.FirstOrder.Theory.ModifiedSolovay (x : M.extendRoot.World) : Prop :=
  Reach T M σ θ V x ∧ ∀ z ∈ next M x, ¬Trig T M σ θ V z

variable {T M σ θ V} {x y z : M.extendRoot.World}

@[simp] lemma val_trigSigma {w : V} :
    V ⊧/![w, ⌜T.modifiedSolovay M σ θ z⌝] (trigSigma T M θ z).val ↔ Wit T M σ θ V z w := by
  unfold trigSigma Wit;
  split_ifs <;> simp [prfNegSigma, Sentence.quote_def, Semiformula.quote_def]

@[simp] lemma val_trigPi {w : V} :
    V ⊧/![w, ⌜T.modifiedSolovay M σ θ z⌝] (trigPi T M θ z).val ↔ Wit T M σ θ V z w := by
  unfold trigPi Wit;
  split_ifs <;> simp [prfNegPi, Sentence.quote_def, Semiformula.quote_def]

@[simp] lemma val_stp :
    V ⊧/![] (stp T M σ θ x y) ↔
      (∀ z ∈ next M x, ord M z < ord M y → WitnessLT (Wit T M σ θ V y) (Wit T M σ θ V z)) ∧
      (∀ z ∈ next M x, ord M y ≤ ord M z → WitnessLE (Wit T M σ θ V y) (Wit T M σ θ V z)) := by
  simp [stpAux]

@[simp] lemma val_H : V ⊧/![] (H T M σ θ x) ↔ Reach T M σ θ V x := by
  suffices (∃ ε : EChain M x, V ⊧/![] (chain T M σ θ ε.1)) ↔ Reach T M σ θ V x by
    simpa [HAux] using this;
  constructor;
  · rintro ⟨⟨ε, hε⟩, hc⟩;
    generalize hn : (none : M.extendRoot.World) = r at hε;
    induction hε with
    | singleton => exact hn ▸ .refl
    | @cons a b _ _ hR hC ih =>
      obtain ⟨l, rfl⟩ := hC.tail_exists;
      have : V ⊧/![] (chain T M σ θ (b :: l)) ∧ V ⊧/![] (stp T M σ θ b a) := by
        simpa [-val_stp, chainAux] using hc;
      exact .tail (ih hn this.1) ⟨hR, by simpa using this.2⟩;
  · intro h;
    induction h with
    | refl => exact ⟨⟨[none], .singleton _⟩, by simp [chainAux]⟩
    | tail _ hs ih =>
      obtain ⟨⟨ε, hε⟩, hc⟩ := ih;
      obtain ⟨l, rfl⟩ := hε.tail_exists;
      exact ⟨⟨_, hε.cons hs.1⟩, by simpa [-val_stp, chainAux] using ⟨hc, by simpa using hs.2⟩⟩

@[simp] lemma val_modifiedSolovay :
    V ⊧/![] (T.modifiedSolovay M σ θ x) ↔ T.ModifiedSolovay M σ θ V x := by
  have hn (z : M.extendRoot.World) : V ⊧/![] (notTrig T M σ θ z) ↔ ¬Trig T M σ θ V z := by
    unfold notTrig notTrigAux Trig;
    split_ifs <;> simp [Theory.ConsistentWith.quote_iff];
  simpa [models_iff, hn, Theory.ModifiedSolovay] using
    consequence_iff.mp (Theory.Proof.sound (modifiedSolovay_diag T M σ θ x)) V inferInstance

lemma trig_iff_exists_wit (hθσ : V ⊧/![] σ ↔ ∃ w, V ⊧/![w] θ.val) :
    Trig T M σ θ V z ↔ ∃ w, Wit T M σ θ V z w := by
  unfold Trig Wit;
  split_ifs;
  exacts [hθσ, .rfl];

lemma wit_definable (z : M.extendRoot.World) : 𝚺₁-Predicate (Wit T M σ θ V z) :=
  HierarchySymbol.Defined.to_definable
    (.mkSigma ((trigSigma T M θ z).val/[#0, ⌜T.modifiedSolovay M σ θ z⌝])) (.mk fun v ↦ by simp)

lemma Step.exists_wit (h : Step T M σ θ V x y) : ∃ w, Wit T M σ θ V y w :=
  (h.2.2 y h.1 le_rfl).exists

lemma Step.unique {y₁ y₂ : M.extendRoot.World} (h₁ : Step T M σ θ V x y₁)
    (h₂ : Step T M σ θ V x y₂) : y₁ = y₂ := by
  wlog hlt : ord M y₁ < ord M y₂ generalizing y₁ y₂;
  · rcases (not_lt.mp hlt).lt_or_eq with hlt | heq;
    · exact (this h₂ h₁ hlt).symm;
    · exact ord_injective heq.symm;
  exact absurd (h₂.2.1 y₁ h₁.1 hlt) (h₁.2.2 y₂ h₂.1 hlt.le).not_witnessLT;

lemma Reach.provable (hx : x ≠ none) (hu : x ≠ some M.u) (h : Reach T M σ θ V x) :
    Provable T (⌜∼T.modifiedSolovay M σ θ x⌝ : V) := by
  rcases h.cases_tail with rfl | ⟨_, _, hs⟩;
  · contradiction;
  · obtain ⟨w, hw⟩ := hs.exists_wit;
    exact ⟨w, by simpa [Wit, hu] using hw⟩;

lemma Reach.models_sigma (hθσ : V ⊧/![] σ ↔ ∃ w, V ⊧/![w] θ.val)
    (h : Reach T M σ θ V (some M.u)) : V ⊧/![] σ := by
  rcases h.cases_tail with h | ⟨_, _, hs⟩;
  · cases h;
  · obtain ⟨w, hw⟩ := hs.exists_wit;
    exact hθσ.mpr ⟨w, by simpa [Wit] using hw⟩;

lemma Reach.disjunction (hθσ : V ⊧/![] σ ↔ ∃ w, V ⊧/![w] θ.val) (h : Reach T M σ θ V x) :
    T.ModifiedSolovay M σ θ V x ∨ ∃ y, x ≺ y ∧ T.ModifiedSolovay M σ θ V y := by
  induction x using (IsConverseWellFounded.cwf (rel := M.extendRoot.Rel)).induction with
  | h x ih =>
    by_cases hx : T.ModifiedSolovay M σ θ V x;
    · simp [hx];
    right;
    obtain ⟨z, hz, hzt⟩ : ∃ z ∈ next M x, Trig T M σ θ V z := by
      simpa [Theory.ModifiedSolovay, h] using hx;
    obtain ⟨⟨y, hy⟩, hy₁, hy₂⟩ := exists_witnessFirst (ι := {z // z ∈ next M x})
      (fun z ↦ Wit T M σ θ V z.1) (fun z ↦ wit_definable z.1) (fun z ↦ ord M z.1)
      ⟨⟨z, hz⟩, (trig_iff_exists_wit hθσ).mp hzt⟩;
    have hs : Step T M σ θ V x y := ⟨hy, fun z hz ↦ hy₁ ⟨z, hz⟩, fun z hz ↦ hy₂ ⟨z, hz⟩⟩;
    rcases ih y (rel_of_mem_next hy) (h.tail hs) with hy' | ⟨w, hyw, hw⟩;
    · exact ⟨y, rel_of_mem_next hy, hy'⟩;
    · exact ⟨w, IsTrans.trans _ _ _ (rel_of_mem_next hy) hyw, hw⟩;

lemma ModifiedSolovay.exclusive (hθσ : V ⊧/![] σ ↔ ∃ w, V ⊧/![w] θ.val) (ne : x ≠ y) :
    T.ModifiedSolovay M σ θ V x → ¬T.ModifiedSolovay M σ θ V y := by
  rintro ⟨hx, hxt⟩ ⟨hy, hyt⟩;
  have key {a b : M.extendRoot.World} (hab : Relation.ReflTransGen (Step T M σ θ V) a b)
      (ne : a ≠ b) (ha : ∀ z ∈ next M a, ¬Trig T M σ θ V z) : False := by
    obtain ⟨c, hac, _⟩ := hab.cases_head.resolve_left ne;
    exact ha c hac.1 ((trig_iff_exists_wit hθσ).mpr hac.exists_wit);
  have U : Relator.RightUnique (Step T M σ θ V) := fun _ _ _ ↦ Step.unique;
  rcases Relation.ReflTransGen.total_of_right_unique U hx hy with h | h;
  · exact key h ne hxt;
  · exact key h ne.symm hyt;

lemma ModifiedSolovay.consistent (hxy : x ≺ y) (hy : y ≠ some M.u)
    (h : T.ModifiedSolovay M σ θ V x) : ¬Provable T (⌜∼T.modifiedSolovay M σ θ y⌝ : V) := by
  simpa [Trig, hy] using h.2 y (by simp [hxy, hy])

lemma disjunctive (hθσ : V ⊧/![] σ ↔ ∃ w, V ⊧/![w] θ.val) :
    ∃ x, T.ModifiedSolovay M σ θ V x := by
  rcases Reach.disjunction (M := M) (T := T) hθσ .refl with h | ⟨_, _, h⟩ <;>
    exact ⟨_, h⟩;

end model

section

variable {T M σ θ} [𝗜𝚺₁ ⪯ T] [M.IsGL]
  (hθσ : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁], V ⊧/![] σ ↔ ∃ w, V ⊧/![w] θ.val)
include hθσ

omit [𝗜𝚺₁ ⪯ T] in
open Classical in
lemma provable_H_imp (x : M.extendRoot.World) :
    𝗜𝚺₁ ⊢ H T M σ θ x 🡒 T.modifiedSolovay M σ θ x ⋎
      ⩖ y ∈ {y : M.extendRoot.World | x ≺ y}, T.modifiedSolovay M σ θ y :=
  complete _ _ fun (V : Type) _ _ ↦ by
    simpa [models_iff] using! Reach.disjunction (hθσ V)

open Classical in
lemma ModifiedSolovay.provable_disjunction {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    {x : M.extendRoot.World} (h : T.ModifiedSolovay M σ θ V x) :
    Provable T (⌜T.modifiedSolovay M σ θ x ⋎
      ⩖ y ∈ {y : M.extendRoot.World | x ≺ y}, T.modifiedSolovay M σ θ y⌝ : V) := by
  have h₁ : T.internalize V ⊢ ⌜H T M σ θ x 🡒 T.modifiedSolovay M σ θ x ⋎
      ⩖ y ∈ {y : M.extendRoot.World | x ≺ y}, T.modifiedSolovay M σ θ y⌝ :=
    internal_provable_of_outer_provable <| WeakerThan.pbl <| provable_H_imp hθσ x;
  have h₂ : T.internalize V ⊢ ⌜H T M σ θ x⌝ :=
    Bootstrapping.Arithmetic.sigma_one_provable_of_models T (H_sigma_one T M σ θ x)
      (by simpa [models_iff] using! h.1);
  exact tprovable_tquote_iff_provable_quote.mp ((by simpa using! h₁) ⨀ h₂)

open Classical in
lemma ModifiedSolovay.box_disjunction {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    {x : M.extendRoot.World} (hx : x ≠ none) (hu : x ≠ some M.u)
    (h : T.ModifiedSolovay M σ θ V x) :
    Provable T (⌜⩖ y ∈ {y : M.extendRoot.World | x ≺ y}, T.modifiedSolovay M σ θ y⌝ : V) := by
  have h₁ := tprovable_tquote_iff_provable_quote.mpr
    (ModifiedSolovay.provable_disjunction hθσ h);
  have h₂ : T.internalize V ⊢ ∼⌜T.modifiedSolovay M σ θ x⌝ := by
    simpa using! tprovable_tquote_iff_provable_quote.mpr (Reach.provable hx hu h.1);
  exact tprovable_tquote_iff_provable_quote.mp (of_A_of_N (by simpa using! h₁) h₂)

omit [𝗜𝚺₁ ⪯ T] in
lemma provable_not_sigma_imp : 𝗜𝚺₁ ⊢ ∼σ 🡒 ∼T.modifiedSolovay M σ θ (some M.u) :=
  complete _ _ fun (V : Type) _ _ ↦ by
    simpa [models_iff] using fun (hσ : ¬V ⊧/![] σ) (h : T.ModifiedSolovay M σ θ V (some M.u)) ↦
      hσ (h.1.models_sigma (hθσ V))

omit hθσ in
lemma provable_provable_sigma_imp :
    𝗜𝚺₁ ⊢ T.standardProvability σ 🡒 ∼T.modifiedSolovay M σ θ none := by
  have h₁ : 𝗜𝚺₁ ⊢ σ 🡒 ∼T.modifiedSolovay M σ θ (some M.root) :=
    complete _ _ fun (V : Type) _ _ ↦ by
      simpa [models_iff] using fun (hσ : V ⊧/![] σ) (h : T.ModifiedSolovay M σ θ V _) ↦
        h.2 (some M.u) (by simp) (by simpa [Trig] using hσ);
  have h₂ : 𝗜𝚺₁ ⊢ T.standardProvability σ 🡒 T.standardProvability (∼T.modifiedSolovay M σ θ _) :=
    T.standardProvability.D2 ⨀ T.standardProvability.D1 (WeakerThan.pbl h₁);
  have hru : some M.root ≠ some M.u := fun h ↦
    Std.Irrefl.irrefl (r := M.Rel) M.root (Option.some_injective _ h ▸ M.root_rel_u);
  have h₃ : 𝗜𝚺₁ ⊢ T.modifiedSolovay M σ θ none 🡒
      ∼T.standardProvability (∼T.modifiedSolovay M σ θ (some M.root)) :=
    complete _ _ fun (V : Type) _ _ ↦ by
      simpa [models_iff, standardProvability_def] using! fun h ↦
        ModifiedSolovay.consistent (x := none) (y := some M.root) trivial hru h;
  cl_prover [h₂, h₃]

end

end FirstOrder.Arithmetic.Bootstrapping.ModifiedSolovaySentences

namespace ProvabilityLogic

open FirstOrder Arithmetic Bootstrapping ModifiedSolovaySentences Kripke

variable {κ α : Type*} [Nonempty κ] [DecidableEq α] {A : Formula α}

/-- Modified Solovay sentences for the standard provability predicate of `T` and a `𝚺₁`
sentence `σ`.

- [Bek90, §6 Theorem 2]
- [AB05, Lemma 51]
-/
def standardModifiedSolovaySentences
    (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] (M : StrongReflexiveCountermodel κ A)
    [Fintype M.World] [M.IsGL] {σ : ArithmeticSentence} (hσ : Hierarchy 𝚺 1 σ) :
    T.standardProvability.ModifiedSolovaySentences M σ :=
  have hex := ISigma1.exists_matrix_provable_of_sentence hσ;
  have hθσ : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
      V ⊧/![] σ ↔ ∃ w, V ⊧/![w] hex.choose.val := fun V _ _ ↦ by
    simpa [models_iff] using
      consequence_iff.mp (Theory.Proof.sound hex.choose_spec) V inferInstance;
  { Λ := T.modifiedSolovay M σ hex.choose
    SC1 _ _ ne := complete _ _ fun (V : Type) _ _ ↦ by
      simpa [models_iff] using! ModifiedSolovay.exclusive (hθσ V) ne
    SC2 _ _ hxy hy := complete _ _ fun (V : Type) _ _ ↦ by
      simpa [models_iff, standardProvability_def] using! ModifiedSolovay.consistent hxy hy
    SC3 _ hx hu := complete _ _ fun (V : Type) _ _ ↦ by
      simpa [models_iff, standardProvability_def] using! ModifiedSolovay.box_disjunction hθσ hx hu
    SC3r := complete _ _ fun (V : Type) _ _ ↦ by
      simpa [models_iff, standardProvability_def] using!
        ModifiedSolovay.provable_disjunction hθσ
    SC4 := complete _ _ fun (V : Type) _ _ ↦ by
      simpa [models_iff] using! disjunctive (hθσ V)
    SC5 := provable_provable_sigma_imp
    SC6 := provable_not_sigma_imp hθσ }

end ProvabilityLogic

end

end FFL

end
