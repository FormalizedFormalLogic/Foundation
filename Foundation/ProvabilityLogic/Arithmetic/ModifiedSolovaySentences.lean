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
arithmetical fixed points `T.modifiedSolovay X σ θ`. Along each edge of `X.extendRoot` a trigger
fires: a proof of `∼Λ z`, or a witness of `σ` on the edge from the old root to `u`; the limit
follows the edge whose trigger fires first.

## References

- [Bek90, §6 Lemma 1, Lemma 1.7, Lemma 1.8, Lemma 2, Theorem 2]
- [AB05, Lemma 51, Lemma 53]
-/

@[expose] public section

open FFL.Entailment

namespace FFL.ProvabilityLogic.Kripke

open Model Model.World

/-- A rooted countermodel of `A` with an `A`-reflexive world `u` whose only predecessor is the
root.

- [Bek90, §6 Theorem 2]
-/
structure StrongReflexiveCountermodel (κ : Type*) [Nonempty κ] {α : Type*} [DecidableEq α]
    (A : Formula α) extends RootedModel κ α where
  root_not_forces : root ⊮[toModel] A
  u : toModel.World
  root_rel_u : root ≺ u
  isReflexiveOf_u : u.IsReflexiveOf A.subfmls.prebox
  eq_root_of_rel_u : ∀ z : toModel.World, z ≺ u → z = root

end FFL.ProvabilityLogic.Kripke

namespace FFL.FirstOrder.ProvabilityAbstraction

open ProvabilityLogic Kripke Kripke.Model Kripke.Model.World Kripke.RootedModel

variable {L : Language} [L.ReferenceableBy L] {T₀ T : Theory L} [T₀ ⪯ T]
         {𝔅 : Provability T₀ T} [𝔅.HBL]
         {κ α : Type*} [Nonempty κ] [DecidableEq α] {A : ProvabilityLogic.Formula α}

/-- The `n`-times iterated consistency `∼𝔅^[n] ⊥`. -/
def Provability.conItr (𝔅 : Provability T₀ T) (n : ℕ) : Sentence L := ∼𝔅^[n] ⊥

omit [T₀ ⪯ T] in
lemma Provability.provable_boxItr_bot_mono {n m : ℕ} (h : n ≤ m) : T₀ ⊢ 𝔅^[n] ⊥ 🡒 𝔅^[m] ⊥ := by
  induction m, h using Nat.le_induction with
  | base => exact C_id
  | succ m _ ih =>
    suffices T₀ ⊢ 𝔅^[m] ⊥ 🡒 𝔅^[m + 1] ⊥ from C_trans ih this;
    rcases m with _ | m;
    · exact efq;
    · simpa only [Function.iterate_succ_apply'] using 𝔅.D3;

open Classical in
/-- Sentences indexed by the worlds of `X.extendRoot` satisfying the Solovay conditions of the
construction whose limit jumps from the old root to `u` once a witness of `σ` is found.

- [Bek90, §6 Lemma 1]
-/
structure Provability.ModifiedSolovaySentences
    (𝔅 : Provability T₀ T) (X : StrongReflexiveCountermodel κ A) [Fintype X.World]
    (σ : Sentence L) where
  Λ : X.extendRoot.World → Sentence L
  protected SC1 : ∀ i j, i ≠ j → T₀ ⊢ Λ i 🡒 ∼Λ j
  protected SC2 : ∀ i j : X.extendRoot.World, i ≺ j → j ≠ some X.u → T₀ ⊢ Λ i 🡒 𝔅.dia (Λ j)
  protected SC3 : ∀ i : X.extendRoot.World, i ≠ none → i ≠ some X.u →
    T₀ ⊢ Λ i 🡒 𝔅 (⩖ j ∈ { j : X.extendRoot.World | i ≺ j }, Λ j)
  protected SC3r : T₀ ⊢ Λ (some X.u) 🡒
    𝔅 (Λ (some X.u) ⋎ ⩖ j ∈ { j : X.extendRoot.World | some X.u ≺ j }, Λ j)
  protected SC4 : T₀ ⊢ ⩖ j, Λ j
  protected SC5 : T₀ ⊢ 𝔅 σ 🡒 ∼Λ none
  protected SC6 : T₀ ⊢ ∼σ 🡒 ∼Λ (some X.u)

namespace Provability.ModifiedSolovaySentences

variable {X : StrongReflexiveCountermodel κ A} [Fintype X.World] [X.IsGL] {σ : Sentence L}
         {S : 𝔅.ModifiedSolovaySentences X σ} {i : X.extendRoot.World}

open Classical in
noncomputable def realization (S : 𝔅.ModifiedSolovaySentences X σ) : Realization α L :=
  ⟨fun a ↦ ⩖ i ∈ { i : X.extendRoot.World | i ⊩[X.extendRoot.toModel] #a }, S.Λ i⟩

private lemma mainlemma_aux (hi : i ≠ none) {B : ProvabilityLogic.Formula α}
    (hB : B ∈ A.subfmls) :
    (i ⊩[X.extendRoot.toModel] B → T₀ ⊢ S.Λ i 🡒 B.interpret S.realization 𝔅) ∧
    (i ⊮[X.extendRoot.toModel] B → T₀ ⊢ S.Λ i 🡒 ∼B.interpret S.realization 𝔅) := by
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
    have hne {j : X.extendRoot.World} (Rij : i ≺ j) : j ≠ none := by rintro rfl; simp_all;
    have hu : some X.u ⊩[X.extendRoot.toModel] □B → some X.u ⊩[X.extendRoot.toModel] B :=
      fun h ↦ extendRoot.forces_some.mpr <|
        X.isReflexiveOf_u B (FormulaFinset.mem_prebox.mpr hB) (extendRoot.forces_some.mp h);
    constructor;
    · intro h;
      have h₁ : T₀ ⊢ (⩖ j ∈ { j : X.extendRoot.World | i ≺ j }, S.Λ j) 🡒
          B.interpret S.realization 𝔅 :=
        left_Fdisj'_intro _ _ fun j hj ↦ (ih (hne (by simpa using hj))).1 (h j (by simpa using hj));
      rcases eq_or_ne i (some X.u) with rfl | hiu;
      · exact C_trans S.SC3r <| 𝔅.mono' <| left_A_intro ((ih hi).1 (hu h)) h₁;
      · exact C_trans (S.SC3 i hi hiu) <| 𝔅.mono' h₁;
    · intro h;
      obtain ⟨j, Rij, hj⟩ := not_forces_box.mp h;
      obtain ⟨y, ⟨Riy, hy⟩, hymax⟩ :=
        X.extendRoot.terminalOf { y | i ≺ y ∧ y ⊮[X.extendRoot.toModel] B } ⟨j, Rij, hj⟩;
      have hyu : y ≠ some X.u := by
        rintro rfl;
        exact hy <| hu fun z Ryz ↦ of_not_not fun hz ↦
          hymax z ⟨IsTrans.trans _ _ _ Riy Ryz, hz⟩ Ryz;
      exact C_trans (S.SC2 i y Riy hyu) <| contra <| 𝔅.mono' <| CN_of_CN_right <|
        (ih (hne Riy)).2 hy;

/-- - [Bek90, §6 Lemma 2]
- [AB05, Lemma 53]
-/
theorem mainlemma (hi : i ≠ none) {B : ProvabilityLogic.Formula α} (hB : B ∈ A.subfmls) :
    i ⊩[X.extendRoot.toModel] B → T₀ ⊢ S.Λ i 🡒 B.interpret S.realization 𝔅 :=
  (mainlemma_aux hi hB).1

/-- - [Bek90, §6 Lemma 2]
- [AB05, Lemma 53]
-/
theorem mainlemma_neg (hi : i ≠ none) {B : ProvabilityLogic.Formula α} (hB : B ∈ A.subfmls) :
    i ⊮[X.extendRoot.toModel] B → T₀ ⊢ S.Λ i 🡒 ∼B.interpret S.realization 𝔅 :=
  (mainlemma_aux hi hB).2

lemma provable_boxItr_bot_of_ne (S : 𝔅.ModifiedSolovaySentences X σ) {z : X.World}
    (hr : z ≠ X.root) (hu : z ≠ X.u) :
    T₀ ⊢ S.Λ (some z) 🡒 𝔅^[Model.World.rank z + 1] ⊥ := by
  classical
  induction z using WellFounded.induction IsConverseWellFounded.cwf (r := flip X.Rel) with
  | h z ih =>
    suffices T₀ ⊢ (⩖ j ∈ { j : X.extendRoot.World | some z ≺ j }, S.Λ j) 🡒
        𝔅^[Model.World.rank z] ⊥ by
      simpa only [Function.iterate_succ_apply'] using
        C_trans (S.SC3 (some z) (by simp) (by simpa using hu)) (𝔅.mono' this);
    apply left_Fdisj'_intro;
    rintro (_ | y) hy;
    · simp at hy;
    · replace hy : z ≺ y := by simpa using hy;
      exact C_trans (ih y hy (by rintro rfl; exact not_rel_root hy)
        (by rintro rfl; exact hr <| X.eq_root_of_rel_u z hy)) <|
        𝔅.provable_boxItr_bot_mono <| Model.rank_lt_of_rel hy;

lemma provable_b (S : 𝔅.ModifiedSolovaySentences X σ) :
    T₀ ⊢ 𝔅.conItr X.height 🡒 𝔅 σ 🡒 ∼σ 🡒 S.Λ (some X.root) := by
  classical
  suffices T₀ ⊢ (⩖ j, S.Λ j) 🡒 ∼𝔅^[X.height] ⊥ 🡒 𝔅 σ 🡒 ∼σ 🡒 S.Λ (some X.root) from
    this ⨀ S.SC4;
  apply left_Udisj_intro;
  rintro (_ | z);
  · cl_prover [S.SC5];
  rcases eq_or_ne z X.root with rfl | hr;
  · cl_prover;
  rcases eq_or_ne z X.u with rfl | hu;
  · cl_prover [S.SC6];
  cl_prover [C_trans (S.provable_boxItr_bot_of_ne hr hu) <|
    𝔅.provable_boxItr_bot_mono <| rank_lt_height <| X.root_rel z hr];

/-- Provably in `T₀`, the `X.height`-times iterated consistency and the realization of `A` yield
the reflection instance `𝔅 σ 🡒 σ`.

- [Bek90, §6 Theorem 2]
- [AB05, Lemma 51]
-/
theorem reflection (S : 𝔅.ModifiedSolovaySentences X σ) :
    T₀ ⊢ 𝔅.conItr X.height 🡒 A.interpret S.realization 𝔅 🡒 𝔅 σ 🡒 σ := by
  cl_prover [S.provable_b, S.mainlemma_neg (Option.some_ne_none X.root) Formula.mem_subfmls_self <|
    extendRoot.forces_some.not.mpr X.root_not_forces];

end Provability.ModifiedSolovaySentences

end FFL.FirstOrder.ProvabilityAbstraction

noncomputable section

namespace FFL.FirstOrder.Arithmetic.Bootstrapping.ModifiedSolovaySentences

open ProvabilityLogic Kripke Kripke.Model Kripke.Model.World

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

section stx

variable (T : ArithmeticTheory) [T.Δ₁] (X : StrongReflexiveCountermodel κ A) [Fintype X.World]
  (σ : ArithmeticSentence) (θ : 𝚺₀.Semisentence 1)

open Classical in
/-- The targets of the edges from `x`. -/
def next (x : X.extendRoot.World) : Finset X.extendRoot.World :=
  {z | (x ≺ z ∧ z ≠ some X.u) ∨ (x = some X.root ∧ z = some X.u)}

variable {X} in
@[simp] lemma mem_next {x z : X.extendRoot.World} :
    z ∈ next X x ↔ (x ≺ z ∧ z ≠ some X.u) ∨ (x = some X.root ∧ z = some X.u) := by
  simp [next]

variable {X} in
lemma rel_of_mem_next {x z : X.extendRoot.World} (h : z ∈ next X x) : x ≺ z := by
  rcases mem_next.mp h with h | ⟨rfl, rfl⟩;
  · exact h.1;
  · exact X.root_rel_u;

open Classical in
/-- A total order on the worlds of `X.extendRoot` in which `u` is the largest. -/
def ord (z : X.extendRoot.World) : ℕ :=
  if z = some X.u then Fintype.card X.extendRoot.World else Fintype.equivFin _ z

variable {X} in
lemma ord_injective : Function.Injective (ord X) := by
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
def trigSigma (z : X.extendRoot.World) : 𝚺₁.Semisentence 2 :=
  if z = some X.u then .mkSigma “w e. !θ.val w” else prfNegSigma T

open Classical in
def trigPi (z : X.extendRoot.World) : 𝚷₁.Semisentence 2 :=
  if z = some X.u then .mkPi “w e. !θ.val w” else prfNegPi T

variable {n : ℕ} (t : X.extendRoot.World → ArithmeticSemiterm Empty n)

def stpAux (x y : X.extendRoot.World) : ArithmeticSemisentence n :=
  (⩕ z ∈ {z ∈ next X x | ord X z < ord X y},
    (cmpLT (trigSigma T X θ y) (trigPi T X θ z)).val/[t y, t z]) ⋏
  (⩕ z ∈ {z ∈ next X x | ord X y ≤ ord X z},
    (cmpLE (trigSigma T X θ y) (trigPi T X θ z)).val/[t y, t z])

def chainAux : List X.extendRoot.World → ArithmeticSemisentence n
  |          [] => ⊥
  |         [_] => ⊤
  | y :: x :: ε => chainAux (x :: ε) ⋏ stpAux T X θ t x y

open Classical in
def notTrigAux (z : X.extendRoot.World) : ArithmeticSemisentence n :=
  if z = some X.u then Rew.embSubsts ![] ▹ ∼σ else T.consistentWith.val/[t z]

section rew

variable {n' : ℕ} (w : Fin n → ArithmeticSemiterm Empty n')

lemma rew_stpAux (x y : X.extendRoot.World) :
    Rew.subst w ▹ stpAux T X θ t x y = stpAux T X θ (fun z ↦ Rew.subst w (t z)) x y := by
  simp [stpAux, Finset.map_conj', Function.comp_def, ← TransitiveRewriting.comp_app,
    Rew.subst_comp_subst, Matrix.comp_vecCons', Matrix.constant_eq_singleton]

lemma rew_chainAux (ε : List X.extendRoot.World) :
    Rew.subst w ▹ chainAux T X θ t ε = chainAux T X θ (fun z ↦ Rew.subst w (t z)) ε := by
  match ε with
  |          [] => simp [chainAux]
  |         [_] => simp [chainAux]
  | _ :: x :: ε => simp [chainAux, rew_chainAux (x :: ε), rew_stpAux]

omit [Fintype X.World] in
lemma rew_notTrigAux (z : X.extendRoot.World) :
    Rew.subst w ▹ notTrigAux T X σ t z = notTrigAux T X σ (fun z ↦ Rew.subst w (t z)) z := by
  unfold notTrigAux;
  split_ifs <;> simp [← TransitiveRewriting.comp_app, Rew.subst_comp_embSubsts,
    Rew.subst_comp_subst, Matrix.empty_eq]

end rew

/-- The sequences from the root `none` to `x` along the edges, listed from `x`. -/
abbrev EChain (x : X.extendRoot.World) :=
  {ε : List X.extendRoot.World // ε.ChainI (fun a b ↦ a ∈ next X b) x none}

variable [X.IsGL]

instance (x : X.extendRoot.World) : Finite (EChain X x) := by
  have mono {a b : X.extendRoot.World} {l : List X.extendRoot.World}
      (h : l.ChainI (fun a b ↦ a ∈ next X b) a b) : l.ChainI (fun a b ↦ b ≺ a) a b := by
    induction h with
    | singleton => exact .singleton _
    | cons hR _ ih => exact .cons (rel_of_mem_next hR) ih;
  exact Finite.of_injective _
    (Subtype.impEmbedding _ _ fun _ ↦ mono).injective

def HAux (x : X.extendRoot.World) : ArithmeticSemisentence n :=
  haveI := Fintype.ofFinite (EChain X x);
  ⩖ ε : EChain X x, chainAux T X θ t ε

def deltaAux (x : X.extendRoot.World) : ArithmeticSemisentence n :=
  HAux T X θ t x ⋏ ⩕ z ∈ next X x, notTrigAux T X σ t z

/-- The modified Solovay sentences.

- [Bek90, §6 Theorem 2]
-/
def _root_.FFL.FirstOrder.Theory.modifiedSolovay (x : X.extendRoot.World) : ArithmeticSentence :=
  exclusiveMultifixedpoint
    (fun j ↦ deltaAux T X σ θ (fun z ↦ #(Fintype.equivFin _ z)) ((Fintype.equivFin _).symm j))
    (Fintype.equivFin _ x)

abbrev stp (x y : X.extendRoot.World) : ArithmeticSentence :=
  stpAux T X θ (fun z ↦ ⌜T.modifiedSolovay X σ θ z⌝) x y

abbrev chain (ε : List X.extendRoot.World) : ArithmeticSentence :=
  chainAux T X θ (fun z ↦ ⌜T.modifiedSolovay X σ θ z⌝) ε

abbrev H (x : X.extendRoot.World) : ArithmeticSentence :=
  HAux T X θ (fun z ↦ ⌜T.modifiedSolovay X σ θ z⌝) x

abbrev notTrig (z : X.extendRoot.World) : ArithmeticSentence :=
  notTrigAux T X σ (fun z ↦ ⌜T.modifiedSolovay X σ θ z⌝) z

lemma H_sigma_one (x : X.extendRoot.World) : Hierarchy 𝚺 1 (H T X σ θ x) := by
  have h (ε : List X.extendRoot.World) : Hierarchy 𝚺 1 (chain T X σ θ ε) := by
    induction ε with
    | nil => simp [chainAux]
    | cons y ε ih => rcases ε with _ | ⟨x, ε⟩ <;> simp_all [chainAux, stpAux];
  simp [HAux, h]

lemma modifiedSolovay_diag (x : X.extendRoot.World) :
    𝗜𝚺₁ ⊢ T.modifiedSolovay X σ θ x 🡘 H T X σ θ x ⋏ ⩕ z ∈ next X x, notTrig T X σ θ z := by
  have : 𝗜𝚺₁ ⊢ T.modifiedSolovay X σ θ x 🡘
      (Rew.subst fun j ↦ ⌜T.modifiedSolovay X σ θ ((Fintype.equivFin _).symm j)⌝) ▹
        deltaAux T X σ θ (fun z ↦ #(Fintype.equivFin _ z)) x := by
    simpa [Theory.modifiedSolovay] using! exclusiveMultidiagonal (i := Fintype.equivFin _ x)
      (fun j ↦ deltaAux T X σ θ (fun z ↦ #(Fintype.equivFin _ z)) ((Fintype.equivFin _).symm j));
  simpa [deltaAux, HAux, Finset.map_conj', Finset.map_udisj, Function.comp_def, rew_chainAux,
    rew_notTrigAux] using! this

end stx

section model

variable (T : ArithmeticTheory) [T.Δ₁] (X : StrongReflexiveCountermodel κ A) [Fintype X.World]
  [X.IsGL] (σ : ArithmeticSentence) (θ : 𝚺₀.Semisentence 1)
  (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open Classical in
/-- `w` witnesses the trigger of an edge into `z`. -/
def Wit (z : X.extendRoot.World) (w : V) : Prop :=
  if z = some X.u then V ⊧/![w] θ.val else Proof T w ⌜∼T.modifiedSolovay X σ θ z⌝

open Classical in
/-- The trigger of an edge into `z` is pulled. -/
def Trig (z : X.extendRoot.World) : Prop :=
  if z = some X.u then V ⊧/![] σ else Provable T (⌜∼T.modifiedSolovay X σ θ z⌝ : V)

/-- The edge `x → y` is the one taken from `x`. -/
def Step (x y : X.extendRoot.World) : Prop :=
  y ∈ next X x ∧
    (∀ z ∈ next X x, ord X z < ord X y → WitnessLT (Wit T X σ θ V y) (Wit T X σ θ V z)) ∧
    (∀ z ∈ next X x, ord X y ≤ ord X z → WitnessLE (Wit T X σ θ V y) (Wit T X σ θ V z))

abbrev Reach (x : X.extendRoot.World) : Prop := Relation.ReflTransGen (Step T X σ θ V) none x

def _root_.FFL.FirstOrder.Theory.ModifiedSolovay (x : X.extendRoot.World) : Prop :=
  Reach T X σ θ V x ∧ ∀ z ∈ next X x, ¬Trig T X σ θ V z

variable {T X σ θ V}

@[simp] lemma val_trigSigma {z : X.extendRoot.World} {w : V} :
    V ⊧/![w, ⌜T.modifiedSolovay X σ θ z⌝] (trigSigma T X θ z).val ↔ Wit T X σ θ V z w := by
  unfold trigSigma Wit;
  split_ifs <;> simp [prfNegSigma, Sentence.quote_def, Semiformula.quote_def]

@[simp] lemma val_trigPi {z : X.extendRoot.World} {w : V} :
    V ⊧/![w, ⌜T.modifiedSolovay X σ θ z⌝] (trigPi T X θ z).val ↔ Wit T X σ θ V z w := by
  unfold trigPi Wit;
  split_ifs <;> simp [prfNegPi, Sentence.quote_def, Semiformula.quote_def]

@[simp] lemma val_stp {x y : X.extendRoot.World} :
    V ⊧/![] (stp T X σ θ x y) ↔
      (∀ z ∈ next X x, ord X z < ord X y → WitnessLT (Wit T X σ θ V y) (Wit T X σ θ V z)) ∧
      (∀ z ∈ next X x, ord X y ≤ ord X z → WitnessLE (Wit T X σ θ V y) (Wit T X σ θ V z)) := by
  simp [stpAux]

@[simp] lemma val_H {x : X.extendRoot.World} : V ⊧/![] (H T X σ θ x) ↔ Reach T X σ θ V x := by
  suffices (∃ ε : EChain X x, V ⊧/![] (chain T X σ θ ε.1)) ↔ Reach T X σ θ V x by
    simpa [HAux] using this;
  constructor;
  · rintro ⟨⟨ε, hε⟩, hc⟩;
    generalize hn : (none : X.extendRoot.World) = r at hε;
    induction hε with
    | singleton => exact hn ▸ .refl
    | @cons a b _ _ hR hC ih =>
      obtain ⟨l, rfl⟩ := hC.tail_exists;
      have : V ⊧/![] (chain T X σ θ (b :: l)) ∧ V ⊧/![] (stp T X σ θ b a) := by
        simpa [-val_stp, chainAux] using hc;
      exact .tail (ih hn this.1) ⟨hR, by simpa using this.2⟩;
  · intro h;
    induction h with
    | refl => exact ⟨⟨[none], .singleton _⟩, by simp [chainAux]⟩
    | tail _ hs ih =>
      obtain ⟨⟨ε, hε⟩, hc⟩ := ih;
      obtain ⟨l, rfl⟩ := hε.tail_exists;
      exact ⟨⟨_, hε.cons hs.1⟩, by simpa [-val_stp, chainAux] using ⟨hc, by simpa using hs.2⟩⟩

@[simp] lemma val_modifiedSolovay {x : X.extendRoot.World} :
    V ⊧/![] (T.modifiedSolovay X σ θ x) ↔ T.ModifiedSolovay X σ θ V x := by
  have hn (z : X.extendRoot.World) : V ⊧/![] (notTrig T X σ θ z) ↔ ¬Trig T X σ θ V z := by
    unfold notTrig notTrigAux Trig;
    split_ifs <;> simp [Theory.ConsistentWith.quote_iff];
  simpa [models_iff, hn, Theory.ModifiedSolovay] using
    consequence_iff.mp (Theory.Proof.sound (modifiedSolovay_diag T X σ θ x)) V inferInstance

lemma trig_iff_exists_wit (hθσ : V ⊧/![] σ ↔ ∃ w, V ⊧/![w] θ.val) {z : X.extendRoot.World} :
    Trig T X σ θ V z ↔ ∃ w, Wit T X σ θ V z w := by
  unfold Trig Wit;
  split_ifs;
  exacts [hθσ, .rfl];

lemma wit_definable (z : X.extendRoot.World) : 𝚺₁-Predicate (Wit T X σ θ V z) :=
  HierarchySymbol.Defined.to_definable
    (.mkSigma ((trigSigma T X θ z).val/[#0, ⌜T.modifiedSolovay X σ θ z⌝])) (.mk fun v ↦ by simp)

lemma Step.exists_wit {x y : X.extendRoot.World} (h : Step T X σ θ V x y) :
    ∃ w, Wit T X σ θ V y w :=
  (h.2.2 y h.1 le_rfl).exists

lemma Step.unique {x y₁ y₂ : X.extendRoot.World} (h₁ : Step T X σ θ V x y₁)
    (h₂ : Step T X σ θ V x y₂) : y₁ = y₂ := by
  wlog hlt : ord X y₁ < ord X y₂ generalizing y₁ y₂;
  · rcases (not_lt.mp hlt).lt_or_eq with hlt | heq;
    · exact (this h₂ h₁ hlt).symm;
    · exact ord_injective heq.symm;
  exact absurd (h₂.2.1 y₁ h₁.1 hlt) (h₁.2.2 y₂ h₂.1 hlt.le).not_witnessLT;

lemma Reach.provable {x : X.extendRoot.World} (hx : x ≠ none) (hu : x ≠ some X.u)
    (h : Reach T X σ θ V x) : Provable T (⌜∼T.modifiedSolovay X σ θ x⌝ : V) := by
  rcases h.cases_tail with rfl | ⟨_, _, hs⟩;
  · contradiction;
  · obtain ⟨w, hw⟩ := hs.exists_wit;
    exact ⟨w, by simpa [Wit, hu] using hw⟩;

lemma Reach.models_sigma (hθσ : V ⊧/![] σ ↔ ∃ w, V ⊧/![w] θ.val)
    (h : Reach T X σ θ V (some X.u)) : V ⊧/![] σ := by
  rcases h.cases_tail with h | ⟨_, _, hs⟩;
  · cases h;
  · obtain ⟨w, hw⟩ := hs.exists_wit;
    exact hθσ.mpr ⟨w, by simpa [Wit] using hw⟩;

lemma Reach.disjunction (hθσ : V ⊧/![] σ ↔ ∃ w, V ⊧/![w] θ.val) {x : X.extendRoot.World}
    (h : Reach T X σ θ V x) :
    T.ModifiedSolovay X σ θ V x ∨ ∃ y, x ≺ y ∧ T.ModifiedSolovay X σ θ V y := by
  induction x using (IsConverseWellFounded.cwf (rel := X.extendRoot.Rel)).induction with
  | h x ih =>
    by_cases hx : T.ModifiedSolovay X σ θ V x;
    · simp [hx];
    right;
    obtain ⟨z, hz, hzt⟩ : ∃ z ∈ next X x, Trig T X σ θ V z := by
      simpa [Theory.ModifiedSolovay, h] using hx;
    obtain ⟨⟨y, hy⟩, hy₁, hy₂⟩ := exists_witnessFirst (ι := {z // z ∈ next X x})
      (fun z ↦ Wit T X σ θ V z.1) (fun z ↦ wit_definable z.1) (fun z ↦ ord X z.1)
      ⟨⟨z, hz⟩, (trig_iff_exists_wit hθσ).mp hzt⟩;
    have hs : Step T X σ θ V x y := ⟨hy, fun z hz ↦ hy₁ ⟨z, hz⟩, fun z hz ↦ hy₂ ⟨z, hz⟩⟩;
    rcases ih y (rel_of_mem_next hy) (h.tail hs) with hy' | ⟨w, hyw, hw⟩;
    · exact ⟨y, rel_of_mem_next hy, hy'⟩;
    · exact ⟨w, IsTrans.trans _ _ _ (rel_of_mem_next hy) hyw, hw⟩;

lemma ModifiedSolovay.exclusive (hθσ : V ⊧/![] σ ↔ ∃ w, V ⊧/![w] θ.val)
    {x y : X.extendRoot.World} (ne : x ≠ y) :
    T.ModifiedSolovay X σ θ V x → ¬T.ModifiedSolovay X σ θ V y := by
  rintro ⟨hx, hxt⟩ ⟨hy, hyt⟩;
  have key {a b : X.extendRoot.World} (hab : Relation.ReflTransGen (Step T X σ θ V) a b)
      (ne : a ≠ b) (ha : ∀ z ∈ next X a, ¬Trig T X σ θ V z) : False := by
    obtain ⟨c, hac, _⟩ := hab.cases_head.resolve_left ne;
    exact ha c hac.1 ((trig_iff_exists_wit hθσ).mpr hac.exists_wit);
  have U : Relator.RightUnique (Step T X σ θ V) := fun _ _ _ ↦ Step.unique;
  rcases Relation.ReflTransGen.total_of_right_unique U hx hy with h | h;
  · exact key h ne hxt;
  · exact key h ne.symm hyt;

lemma ModifiedSolovay.consistent {x y : X.extendRoot.World} (hxy : x ≺ y) (hy : y ≠ some X.u)
    (h : T.ModifiedSolovay X σ θ V x) : ¬Provable T (⌜∼T.modifiedSolovay X σ θ y⌝ : V) := by
  simpa [Trig, hy] using h.2 y (by simp [hxy, hy])

lemma disjunctive (hθσ : V ⊧/![] σ ↔ ∃ w, V ⊧/![w] θ.val) :
    ∃ x, T.ModifiedSolovay X σ θ V x := by
  rcases Reach.disjunction (X := X) (T := T) hθσ .refl with h | ⟨_, _, h⟩ <;>
    exact ⟨_, h⟩;

end model

section

variable {T : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T] {X : StrongReflexiveCountermodel κ A}
  [Fintype X.World] [X.IsGL] {σ : ArithmeticSentence} {θ : 𝚺₀.Semisentence 1}
  (hθσ : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁], V ⊧/![] σ ↔ ∃ w, V ⊧/![w] θ.val)
include hθσ

omit [𝗜𝚺₁ ⪯ T] in
open Classical in
lemma provable_H_imp (x : X.extendRoot.World) :
    𝗜𝚺₁ ⊢ H T X σ θ x 🡒 T.modifiedSolovay X σ θ x ⋎
      ⩖ y ∈ {y : X.extendRoot.World | x ≺ y}, T.modifiedSolovay X σ θ y :=
  complete _ _ fun (V : Type) _ _ ↦ by
    simpa [models_iff] using! Reach.disjunction (hθσ V)

open Classical in
lemma ModifiedSolovay.provable_disjunction {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    {x : X.extendRoot.World} (h : T.ModifiedSolovay X σ θ V x) :
    Provable T (⌜T.modifiedSolovay X σ θ x ⋎
      ⩖ y ∈ {y : X.extendRoot.World | x ≺ y}, T.modifiedSolovay X σ θ y⌝ : V) := by
  have h₁ : T.internalize V ⊢ ⌜H T X σ θ x 🡒 T.modifiedSolovay X σ θ x ⋎
      ⩖ y ∈ {y : X.extendRoot.World | x ≺ y}, T.modifiedSolovay X σ θ y⌝ :=
    internal_provable_of_outer_provable <| WeakerThan.pbl <| provable_H_imp hθσ x;
  have h₂ : T.internalize V ⊢ ⌜H T X σ θ x⌝ :=
    Bootstrapping.Arithmetic.sigma_one_provable_of_models T (H_sigma_one T X σ θ x)
      (by simpa [models_iff] using! h.1);
  exact tprovable_tquote_iff_provable_quote.mp ((by simpa using! h₁) ⨀ h₂)

open Classical in
lemma ModifiedSolovay.box_disjunction {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    {x : X.extendRoot.World} (hx : x ≠ none) (hu : x ≠ some X.u)
    (h : T.ModifiedSolovay X σ θ V x) :
    Provable T (⌜⩖ y ∈ {y : X.extendRoot.World | x ≺ y}, T.modifiedSolovay X σ θ y⌝ : V) := by
  have h₁ := tprovable_tquote_iff_provable_quote.mpr
    (ModifiedSolovay.provable_disjunction hθσ h);
  have h₂ : T.internalize V ⊢ ∼⌜T.modifiedSolovay X σ θ x⌝ := by
    simpa using! tprovable_tquote_iff_provable_quote.mpr (Reach.provable hx hu h.1);
  exact tprovable_tquote_iff_provable_quote.mp (of_A_of_N (by simpa using! h₁) h₂)

omit [𝗜𝚺₁ ⪯ T] in
lemma provable_not_sigma_imp : 𝗜𝚺₁ ⊢ ∼σ 🡒 ∼T.modifiedSolovay X σ θ (some X.u) :=
  complete _ _ fun (V : Type) _ _ ↦ by
    simpa [models_iff] using fun (hσ : ¬V ⊧/![] σ) (h : T.ModifiedSolovay X σ θ V (some X.u)) ↦
      hσ (h.1.models_sigma (hθσ V))

omit hθσ in
lemma provable_provable_sigma_imp :
    𝗜𝚺₁ ⊢ T.standardProvability σ 🡒 ∼T.modifiedSolovay X σ θ none := by
  have h₁ : 𝗜𝚺₁ ⊢ σ 🡒 ∼T.modifiedSolovay X σ θ (some X.root) :=
    complete _ _ fun (V : Type) _ _ ↦ by
      simpa [models_iff] using fun (hσ : V ⊧/![] σ) (h : T.ModifiedSolovay X σ θ V _) ↦
        h.2 (some X.u) (by simp) (by simpa [Trig] using hσ);
  have h₂ : 𝗜𝚺₁ ⊢ T.standardProvability σ 🡒 T.standardProvability (∼T.modifiedSolovay X σ θ _) :=
    T.standardProvability.D2 ⨀ T.standardProvability.D1 (WeakerThan.pbl h₁);
  have hru : some X.root ≠ some X.u := fun h ↦
    Std.Irrefl.irrefl (r := X.Rel) X.root (Option.some_injective _ h ▸ X.root_rel_u);
  have h₃ : 𝗜𝚺₁ ⊢ T.modifiedSolovay X σ θ none 🡒
      ∼T.standardProvability (∼T.modifiedSolovay X σ θ (some X.root)) :=
    complete _ _ fun (V : Type) _ _ ↦ by
      simpa [models_iff, standardProvability_def] using! fun h ↦
        ModifiedSolovay.consistent (x := none) (y := some X.root) trivial hru h;
  cl_prover [h₂, h₃]

end

end FFL.FirstOrder.Arithmetic.Bootstrapping.ModifiedSolovaySentences

namespace FFL.FirstOrder.Arithmetic

open Bootstrapping ModifiedSolovaySentences ProvabilityLogic Kripke ProvabilityAbstraction

variable {κ α : Type*} [Nonempty κ] [DecidableEq α] {A : ProvabilityLogic.Formula α}

/-- Modified Solovay sentences for the standard provability predicate of `T` and a `𝚺₁`
sentence `σ`.

- [Bek90, §6 Theorem 2]
- [AB05, Lemma 51]
-/
def _root_.FFL.FirstOrder.Theory.standardProvability.modifiedSolovaySentences
    (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] (X : StrongReflexiveCountermodel κ A)
    [Fintype X.World] [X.IsGL] {σ : ArithmeticSentence} (hσ : Hierarchy 𝚺 1 σ) :
    T.standardProvability.ModifiedSolovaySentences X σ :=
  have hex := ISigma1.exists_matrix_provable_of_sentence hσ;
  have hθσ : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
      V ⊧/![] σ ↔ ∃ w, V ⊧/![w] hex.choose.val := fun V _ _ ↦ by
    simpa [models_iff] using
      consequence_iff.mp (Theory.Proof.sound hex.choose_spec) V inferInstance;
  { Λ := T.modifiedSolovay X σ hex.choose
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

end FFL.FirstOrder.Arithmetic

end

end
