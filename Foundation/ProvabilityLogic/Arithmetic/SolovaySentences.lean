module

public import Foundation.ProvabilityLogic.Arithmetic.Interpret
public import Foundation.ProvabilityLogic.Kripke.RootExtension
public import Foundation.FirstOrder.Incompleteness.ProvabilityAbstraction.Height
public import Foundation.Vorspiel.List.ChainI
public import Mathlib.Data.ENat.SuccOrder

/-!
# Solovay sentences

## References

- [Sol76]
-/

@[expose] public section

open FFL.Entailment

namespace FFL.FirstOrder.ProvabilityAbstraction

open ProvabilityLogic Kripke Kripke.Model Kripke.Model.World

variable {L : Language} [L.ReferenceableBy L] {T₀ T : Theory L} [T₀ ⪯ T]
         {𝔅 : Provability T₀ T} [𝔅.HBL]
         {κ α : Type*} [Nonempty κ] {A : ProvabilityLogic.Formula α}

open Classical in
structure Provability.SolovaySentences
    (𝔅 : Provability T₀ T) (M : RootedModel κ α) [Fintype M.World] where
  σ : M.World → Sentence L
  protected SC1 : ∀ i j, i ≠ j → T₀ ⊢ σ i 🡒 ∼σ j
  protected SC2 : ∀ i j, i ≺ j → T₀ ⊢ σ i 🡒 𝔅.dia (σ j)
  protected SC3 : ∀ i : M.World, M.root ≠ i → T₀ ⊢ σ i 🡒 𝔅 (⩖ j ∈ { j : M.World | i ≺ j }, σ j)
  protected SC4 : T₀ ⊢ ⩖ j, σ j

namespace Provability.SolovaySentences

attribute [coe] σ

variable {M : RootedModel κ α} [Fintype M.World] [M.IsGL] {i : M.World}
         {S : SolovaySentences 𝔅 M}

open Classical in
noncomputable def realization : Realization α L :=
  ⟨fun a ↦ ⩖ i ∈ { i : M.World | i ⊩ (.atom a) }, S.σ i⟩

private lemma mainlemma_aux (hri : M.root ≠ i) :
    (i ⊩ A → T₀ ⊢ S.σ i 🡒 A.interpret S.realization 𝔅) ∧
    (i ⊮ A → T₀ ⊢ S.σ i 🡒 ∼A.interpret S.realization 𝔅) := by
  induction A generalizing i with
  | falsum => simp [Formula.interpret];
  | atom a =>
    constructor;
    · exact fun h ↦ right_Fdisj'_intro _ _ (by simpa using h);
    · exact fun h ↦ CN_of_CN_right <| left_Fdisj'_intro _ _ fun j hj ↦ S.SC1 _ _ <| by
        rintro rfl;
        simp_all;
  | imp A B ihA ihB =>
    constructor;
    · intro h;
      rcases forces_imp.mp h with hA | hB;
      · exact C_trans ((ihA hri).2 hA) CNC;
      · exact C_trans ((ihB hri).1 hB) implyK;
    · intro h;
      obtain ⟨hA, hB⟩ := not_forces_imp.mp h;
      exact CNC_of_C_of_CN ((ihA hri).1 hA) ((ihB hri).2 hB);
  | box A ihA =>
    have hrj {j : M.World} (Rij : i ≺ j) : M.root ≠ j := by
      rintro rfl;
      exact Std.Irrefl.irrefl i <| IsTrans.trans _ _ _ Rij (M.root_rel i hri.symm);
    constructor;
    · intro h;
      exact C_trans (S.SC3 i hri) <| 𝔅.mono' <| left_Fdisj'_intro _ _ fun j hj ↦
        (ihA (hrj (by simpa using hj))).1 (forces_box.mp h j (by simpa using hj));
    · intro h;
      obtain ⟨j, Rij, hA⟩ := not_forces_box.mp h;
      exact C_trans (S.SC2 i j Rij) <| contra <| 𝔅.mono' <| CN_of_CN_right <| (ihA (hrj Rij)).2 hA;

theorem mainlemma (hri : M.root ≠ i) : i ⊩ A → T₀ ⊢ S.σ i 🡒 A.interpret S.realization 𝔅 :=
  (mainlemma_aux hri).1

theorem mainlemma_neg (hri : M.root ≠ i) : i ⊮ A → T₀ ⊢ S.σ i 🡒 ∼A.interpret S.realization 𝔅 :=
  (mainlemma_aux hri).2

lemma theory_height (hSound : ∀ {σ}, T₀ ⊢ 𝔅 σ → T ⊢ σ) (h : M.root ⊩ ◇(∼A))
    (b : T ⊢ A.interpret S.realization 𝔅) : 𝔅.height < M.height := by
  classical
  apply 𝔅.height_lt_pos_of_boxBot hSound (n := M.height) (Model.rank_pos_of_forces_dia h);
  obtain ⟨i, hi, hiA⟩ := forces_dia.mp h;
  have h₁ : T₀ ⊢ (⩖ j, S.σ j) 🡒 ∼S.σ M.root 🡒 𝔅^[M.height] ⊥ := by
    apply left_Udisj_intro;
    intro j;
    rcases eq_or_ne j M.root with rfl | hj;
    · cl_prover;
    · have : T₀ ⊢ S.σ j 🡒 𝔅^[M.height] ⊥ := by
        simpa [Formula.interpret] using S.mainlemma hj.symm (A := □^[M.height] ⊥) <|
          Model.forces_boxItr_bot_iff.mpr <| RootedModel.rank_lt_height <| M.root_rel j hj;
      cl_prover [this];
  have h₂ : T₀ ⊢ 𝔅.dia (S.σ i) 🡒 ∼𝔅 (A.interpret S.realization 𝔅) := by
    simpa [Provability.dia] using! 𝔅.dia_mono <| WeakerThan.pbl <|
      S.mainlemma_neg (ne_of_irrefl hi) (forces_neg.mp hiA);
  cl_prover [𝔅.D1 b, h₁, S.SC4, S.SC2 M.root i hi, h₂];

section

variable {M : RootedModel κ α} [Fintype M.World] [M.IsGL] [DecidableEq α]
         {S : SolovaySentences 𝔅 M.extendRoot}

/-- If the root of `M` forces `□B 🡒 B` for every subformula `□B` of `A`, then the Solovay
sentence of the new root of `M.extendRoot` decides the realizations of the subformulas of `A`
as the root of `M` decides them.

- [AB05, Lemma 49]
-/
theorem rfl_mainlemma (ha : ∀ B, □B ∈ A.subfmls → M.root ⊩ □B 🡒 B)
    {B : ProvabilityLogic.Formula α}
    (hB : B ∈ A.subfmls) :
    (M.root ⊩ B → T₀ ⊢ S.σ none 🡒 B.interpret S.realization 𝔅) ∧
    (M.root ⊮ B → T₀ ⊢ S.σ none 🡒 ∼B.interpret S.realization 𝔅) := by
  classical
  induction B with
  | falsum => simp [Formula.interpret];
  | atom a =>
    constructor;
    · exact fun h ↦ right_Fdisj'_intro _ _ (by simpa [RootedModel.extendRoot] using h);
    · exact fun h ↦ CN_of_CN_right <| left_Fdisj'_intro _ _ fun j hj ↦ S.SC1 _ _ <| by
        rintro rfl;
        exact h (by simpa [RootedModel.extendRoot] using hj);
  | imp B C ihB ihC =>
    replace ihB := ihB (Formula.subfmls_trans hB (by grind));
    replace ihC := ihC (Formula.subfmls_trans hB (by grind));
    constructor;
    · intro h;
      rcases forces_imp.mp h with hB | hC;
      · exact C_trans (ihB.2 hB) CNC;
      · exact C_trans (ihC.1 hC) implyK;
    · intro h;
      obtain ⟨hB, hC⟩ := not_forces_imp.mp h;
      exact CNC_of_C_of_CN (ihB.1 hB) (ihC.2 hC);
  | box B ihB =>
    replace ihB := ihB (Formula.subfmls_trans hB (by grind));
    constructor;
    · intro h;
      have hB' : M.root ⊩ B := ha B hB h;
      have h₁ : ∀ i, T₀ ⊢ S.σ i 🡒 B.interpret S.realization 𝔅 := by
        rintro (_ | x);
        · exact ihB.1 hB';
        · apply S.mainlemma (Option.some_ne_none x).symm;
          apply RootedModel.extendRoot.forces_some.mpr;
          by_cases hx : x = M.root;
          · exact hx ▸ hB';
          · exact h x (M.root_rel x hx);
      exact C_of_conseq <| 𝔅.D1 <| WeakerThan.pbl <| left_Udisj_intro _ h₁ ⨀ S.SC4;
    · intro h;
      obtain ⟨y, _, hy⟩ := not_forces_box.mp h;
      exact C_trans (S.SC2 _ (some y) trivial) <| contra <| 𝔅.mono' <| CN_of_CN_right <|
        S.mainlemma_neg (Option.some_ne_none y).symm <|
          RootedModel.extendRoot.forces_some.not.mpr hy;

end

end Provability.SolovaySentences

end FFL.FirstOrder.ProvabilityAbstraction

noncomputable section

namespace FFL.FirstOrder.Arithmetic.Bootstrapping.SolovaySentences

open ProvabilityLogic Kripke Kripke.Model Kripke.Model.World

variable {κ α : Type*} [Nonempty κ]

variable {T : ArithmeticTheory} [T.Δ₁]

section model

variable (T) {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A proof of the negation of `φ` appears no later than any proof of the negation of `ψ`. -/
def NegativeSuccessor (φ ψ : V) : Prop := T.ProvabilityComparisonLE (neg ℒₒᵣ φ) (neg ℒₒᵣ ψ)

lemma NegativeSuccessor.quote_iff_provabilityComparisonLE {φ ψ : ArithmeticSentence} :
    NegativeSuccessor (V := V) T ⌜φ⌝ ⌜ψ⌝ ↔ T.ProvabilityComparisonLE (V := V) ⌜∼φ⌝ ⌜∼ψ⌝ := by
  simp [NegativeSuccessor, Sentence.quote_def, Semiformula.quote_def];

def negativeSuccessor : 𝚺₁.Semisentence 2 := .mkSigma
  “φ ψ. ∃ nφ, ∃ nψ, !(negGraph ℒₒᵣ) nφ φ ∧ !(negGraph ℒₒᵣ) nψ ψ ∧ !T.provabilityComparisonLE nφ nψ”

instance negativeSuccessor_defined :
    𝚺₁-Relation[V] NegativeSuccessor T via (negativeSuccessor T) := .mk fun v ↦ by
  simp [negativeSuccessor, NegativeSuccessor];

instance negativeSuccessor_definable : 𝚺₁-Relation (NegativeSuccessor T : V → V → Prop) :=
  (negativeSuccessor_defined T).to_definable

/-- Instance for the definability tactic. -/
instance negativeSuccessor_definable' :
    𝚺-[0 + 1]-Relation (NegativeSuccessor T : V → V → Prop) :=
  (negativeSuccessor_defined T).to_definable

end model

section stx

variable (T) (M : RootedModel κ α) [Fintype M.World] [M.IsGL]

abbrev WChain (i j : M.World) := {l : List M.World // l.ChainI (fun x y ↦ y ≺ x) j i}

omit [Fintype M.World] in
instance [Finite M.World] (i j : M.World) : Finite (WChain M i j) :=
  List.ChainI.finite_of_irreflexive_of_transitive
    (show Std.Irrefl (fun x y : M.World ↦ y ≺ x) from ⟨fun x ↦ Std.Irrefl.irrefl (r := M.Rel) x⟩)
    (show IsTrans M.World (fun x y ↦ y ≺ x) from
      ⟨fun x y z hxy hyz ↦ IsTrans.trans (r := M.Rel) z y x hyz hxy⟩)
    j i

open Classical in
def twoPointAux {N : ℕ} (t : M.World → FirstOrder.ArithmeticSemiterm Empty N) (i j : M.World) :
    ArithmeticSemisentence N :=
  ⩕ k ∈ { k : M.World | i ≺ k }, (negativeSuccessor T)/[t j, t k]

def θChainAux {N : ℕ} (t : M.World → FirstOrder.ArithmeticSemiterm Empty N) :
    List M.World → ArithmeticSemisentence N
  |          [] => ⊥
  |         [_] => ⊤
  | j :: i :: ε => (θChainAux t (i :: ε)) ⋏ (twoPointAux T M t i j)

omit [M.IsGL] in
lemma rew_θChainAux {N N' : ℕ} (w : Fin N → FirstOrder.ArithmeticSemiterm Empty N')
    (t : M.World → FirstOrder.ArithmeticSemiterm Empty N) (ε : List M.World) :
    Rew.subst w ▹ θChainAux T M t ε = θChainAux T M (fun i ↦ Rew.subst w (t i)) ε := by
  match ε with
  |          [] => simp [θChainAux];
  |         [_] => simp [θChainAux];
  | j :: i :: ε =>
    simp [θChainAux, twoPointAux, rew_θChainAux w _ (i :: ε), Finset.map_conj', Function.comp_def,
      ← TransitiveRewriting.comp_app, Rew.subst_comp_subst, Matrix.comp_vecCons',
      Matrix.constant_eq_singleton];

def θAux {N : ℕ} (t : M.World → FirstOrder.ArithmeticSemiterm Empty N) (i : M.World) :
    ArithmeticSemisentence N :=
  haveI := Fintype.ofFinite (WChain M M.root i);
  ⩖ ε : WChain M M.root i, θChainAux T M t ε

open Classical in
def _root_.FFL.FirstOrder.Theory.solovay (i : M.World) : ArithmeticSentence :=
  exclusiveMultifixedpoint
  (fun j ↦
    let jj := (Fintype.equivFin M.World).symm j
    (θAux T M (fun i ↦ #(Fintype.equivFin M.World i)) jj) ⋏
      (⩕ k ∈ { k : M.World | jj ≺ k }, T.consistentWith.val/[#(Fintype.equivFin M.World k)]))
  (Fintype.equivFin M.World i)

def twoPoint (i j : M.World) : ArithmeticSentence := twoPointAux T M (fun i ↦ ⌜T.solovay M i⌝) i j

def θChain (ε : List M.World) : ArithmeticSentence := θChainAux T M (fun i ↦ ⌜T.solovay M i⌝) ε

def θ (i : M.World) : ArithmeticSentence := θAux T M (fun i ↦ ⌜T.solovay M i⌝) i

open Classical in
lemma solovay_diag (i : M.World) :
    𝗜𝚺₁ ⊢ T.solovay M i 🡘
      θ T M i ⋏ ⩕ j ∈ { j : M.World | i ≺ j }, T.consistentWith.val/[⌜T.solovay M j⌝] := by
  have : 𝗜𝚺₁ ⊢ (T.solovay M i) 🡘
      (Rew.subst fun j ↦ ⌜T.solovay M ((Fintype.equivFin M.World).symm j)⌝) ▹
        ((θAux T M (fun i ↦ #(Fintype.equivFin M.World i)) i) ⋏
          (⩕ k ∈ { k : M.World | i ≺ k },
            T.consistentWith.val/[#(Fintype.equivFin M.World k)])) := by
    simpa [Theory.solovay, Matrix.comp_vecCons', Matrix.constant_eq_singleton] using!
      exclusiveMultidiagonal (T := 𝗜𝚺₁) (i := Fintype.equivFin M.World i)
        (fun j ↦
          let jj := (Fintype.equivFin M.World).symm j
          (θAux T M (fun i ↦ #(Fintype.equivFin M.World i)) jj) ⋏
            (⩕ k ∈ { k : M.World | jj ≺ k },
              T.consistentWith.val/[#(Fintype.equivFin M.World k)]));
  simpa [θ, θAux, Finset.map_conj', Finset.map_udisj, Function.comp_def, rew_θChainAux,
    ← TransitiveRewriting.comp_app, Rew.subst_comp_subst, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton] using! this;

@[simp] lemma solovay_exclusive {i j : M.World} : T.solovay M i = T.solovay M j ↔ i = j := by
  simp [Theory.solovay];

@[simp] lemma θ_sigma1 (i : M.World) : Hierarchy 𝚺 1 (θ T M i) := by
  have h {N} {t : M.World → ArithmeticSemiterm Empty N} (ε : List M.World) :
      Hierarchy 𝚺 1 (θChainAux T M t ε) := by
    induction ε with
    | nil => simp [θChainAux];
    | cons j ε ih => rcases ε with _ | ⟨i, ε⟩ <;> simp_all [θChainAux, twoPointAux];
  simp [θ, θAux, h];

end stx

section model

variable (T) (M : RootedModel κ α) [Fintype M.World] [M.IsGL]

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

@[simp] lemma val_twoPoint (i j : M.World) :
    V ⊧/![] (twoPoint T M i j) ↔
      ∀ k, i ≺ k → NegativeSuccessor (V := V) T ⌜T.solovay M j⌝ ⌜T.solovay M k⌝ := by
  simp [twoPoint, twoPointAux];

variable (V)

/-- The traveler moves along `ε`, listed from its last world. -/
inductive ΘChain : List M.World → Prop where
  | singleton (i : M.World) : ΘChain [i]
  | cons {i j : M.World} {ε : List M.World} :
    (∀ k, i ≺ k → NegativeSuccessor (V := V) T ⌜T.solovay M j⌝ ⌜T.solovay M k⌝) →
      ΘChain (i :: ε) → ΘChain (j :: i :: ε)

/-- The traveler reaches `i`. -/
def Θ (i : M.World) : Prop :=
  ∃ ε : List M.World, ε.ChainI (fun x y ↦ y ≺ x) i M.root ∧ ΘChain T M V ε

/-- The traveler's final stop is `i`. -/
def _root_.FFL.FirstOrder.Theory.Solovay (i : M.World) :=
  Θ T M V i ∧ ∀ j, i ≺ j → T.ConsistentWith (⌜T.solovay M j⌝ : V)

variable {T M V}

attribute [simp] ΘChain.singleton

@[simp] lemma ΘChain.not_nil : ¬ΘChain T M V ([] : List M.World) := by rintro ⟨⟩;

lemma ΘChain.doubleton_iff {i j : M.World} :
    ΘChain T M V [j, i] ↔
      ∀ k, i ≺ k → NegativeSuccessor (V := V) T ⌜T.solovay M j⌝ ⌜T.solovay M k⌝ := by
  constructor;
  · rintro ⟨⟩; simp_all;
  · rintro h; exact .cons h (by simp);

lemma ΘChain.cons_cons_iff {i j : M.World} {ε} :
    ΘChain T M V (j :: i :: ε) ↔
      ΘChain T M V (i :: ε) ∧
        ∀ k, i ≺ k → NegativeSuccessor (V := V) T ⌜T.solovay M j⌝ ⌜T.solovay M k⌝ := by
  constructor;
  · rintro ⟨⟩; simp_all;
  · rintro ⟨ih, h⟩; exact .cons h ih;

lemma ΘChain.cons_cons_iff' {i j : M.World} {ε} :
    ΘChain T M V (j :: i :: ε) ↔ ΘChain T M V [j, i] ∧ ΘChain T M V (i :: ε) := by
  constructor;
  · rintro ⟨⟩; simpa [ΘChain.doubleton_iff, *];
  · rintro ⟨ih, h⟩; exact h.cons (by rcases ih; assumption);

@[simp] lemma val_θChain (ε : List M.World) : V ⊧/![] (θChain T M ε) ↔ ΘChain T M V ε := by
  unfold θChain θChainAux;
  match ε with
  |          [] => simp;
  |         [i] => simp;
  | j :: i :: ε =>
    suffices
      V ⊧/![] (θChain T M (i :: ε)) ∧ V ⊧/![] (twoPoint T M i j) ↔
      ΘChain T M V (j :: i :: ε) by simpa [-val_twoPoint] using! this;
    simp [ΘChain.cons_cons_iff, val_θChain (i :: ε)];

@[simp] lemma val_θ {i : M.World} : V ⊧/![] (θ T M i) ↔ Θ T M V i := by
  suffices (∃ ε, List.ChainI (fun x y ↦ y ≺ x) i M.root ε ∧ V ⊧/![] (θChain T M ε)) ↔ Θ T M V i by
    simpa [-val_θChain, θ, θAux];
  simp [Θ];

@[simp] lemma val_solovay {i : M.World} : V ⊧/![] (T.solovay M i) ↔ T.Solovay M V i := by
  simpa [models_iff] using!
    consequence_iff.mp (Theory.Proof.sound (solovay_diag T M i)) V inferInstance;

lemma ΘChain.append_iff {i : M.World} {ε₁ ε₂ : List M.World} :
    ΘChain T M V (ε₁ ++ i :: ε₂) ↔ ΘChain T M V (ε₁ ++ [i]) ∧ ΘChain T M V (i :: ε₂) := by
  match ε₁ with
  |           [] => simp;
  |          [x] => simp [ΘChain.cons_cons_iff' (ε := ε₂)];
  | x :: y :: ε₁ =>
    have : ΘChain T M V (y :: (ε₁ ++ i :: ε₂)) ↔
        ΘChain T M V (y :: (ε₁ ++ [i])) ∧ ΘChain T M V (i :: ε₂) :=
      append_iff (ε₁ := y :: ε₁) (ε₂ := ε₂) (i := i);
    simp [cons_cons_iff' (ε := ε₁ ++ i :: ε₂), cons_cons_iff' (ε := ε₁ ++ [i]), and_assoc, this];

private lemma Solovay.exclusive.comparable {i₁ i₂ r : M.World} {ε₁ ε₂ : List M.World}
    (ne : i₁ ≠ i₂) (h : ε₁ <:+ ε₂) (Hi₁ : ∀ j, i₁ ≺ j → T.ConsistentWith (⌜T.solovay M j⌝ : V))
    (cε₁ : List.ChainI (fun x y ↦ y ≺ x) i₁ r ε₁) (cε₂ : List.ChainI (fun x y ↦ y ≺ x) i₂ r ε₂)
    (Θε₂ : ΘChain T M V ε₂) : False := by
  obtain ⟨j, hj⟩ : ∃ a, a :: ε₁ <:+ ε₂ := by
    rcases List.IsSuffix.eq_or_cons_suffix h with rfl | h;
    · exact absurd (List.ChainI.eq_of cε₁ cε₂).1 ne;
    · exact h;
  have hji₁ε₂ : [j, i₁] <:+: ε₂ := by
    obtain ⟨ε₁', rfl⟩ := cε₁.tail_exists;
    exact List.infix_iff_prefix_suffix.mpr ⟨j :: i₁ :: ε₁', by simp, hj⟩;
  have hij₁ : i₁ ≺ j := cε₂.rel_of_infix j i₁ hji₁ε₂;
  have : ΘChain T M V [j, i₁] := by
    obtain ⟨η₁, η₂, rfl⟩ := hji₁ε₂;
    exact (ΘChain.cons_cons_iff'.mp (ΘChain.append_iff.mp (by simpa using! Θε₂)).2).1;
  have : T.ProvabilityComparisonLE (V := V) ⌜∼T.solovay M j⌝ ⌜∼T.solovay M j⌝ := by
    simpa [NegativeSuccessor.quote_iff_provabilityComparisonLE] using!
      ΘChain.doubleton_iff.mp this j hij₁;
  exact (Theory.ConsistentWith.quote_iff T).mp (Hi₁ j hij₁) <|
    (ProvabilityComparison.iff_le_refl_provable (L := ℒₒᵣ)).mp this;

/-- Solovay condition `SC1`. -/
lemma Solovay.exclusive {i₁ i₂ : M.World} (ne : i₁ ≠ i₂) :
    T.Solovay M V i₁ → ¬T.Solovay M V i₂ := by
  rintro ⟨⟨ε₁, cε₁, Θε₁⟩, Hi₁⟩;
  by_contra h₂;
  obtain ⟨⟨ε₂, cε₂, Θε₂⟩, Hi₂⟩ := h₂;
  by_cases hε₁₂ : ε₁ <:+ ε₂;
  · exact Solovay.exclusive.comparable ne hε₁₂ Hi₁ cε₁ cε₂ Θε₂;
  by_cases hε₂₁ : ε₂ <:+ ε₁;
  · exact Solovay.exclusive.comparable ne.symm hε₂₁ Hi₂ cε₂ cε₁ Θε₁;
  obtain ⟨ε, k, j₁, j₂, nej, hj₁, hj₂⟩ :
      ∃ ε k j₁ j₂, j₁ ≠ j₂ ∧ j₁ :: k :: ε <:+ ε₁ ∧ j₂ :: k :: ε <:+ ε₂ := by
    obtain ⟨ε', j₁, j₂, nej, h₁, h₂⟩ := List.suffix_trichotomy hε₁₂ hε₂₁;
    match ε' with
    |     [] =>
      exact absurd ((List.single_suffix_uniq h₁ cε₁.prefix_suffix.2).trans
        (List.single_suffix_uniq h₂ cε₂.prefix_suffix.2).symm) nej;
    | k :: ε => exact ⟨ε, k, j₁, j₂, nej, h₁, h₂⟩;
  have P {j j' : M.World} {ε' : List M.World} (hj : j :: k :: ε <:+ ε') (Θ : ΘChain T M V ε')
      (hkj' : k ≺ j') : T.ProvabilityComparisonLE (V := V) ⌜∼T.solovay M j⌝ ⌜∼T.solovay M j'⌝ := by
    obtain ⟨_, rfl⟩ := hj;
    simpa [NegativeSuccessor.quote_iff_provabilityComparisonLE] using!
      ΘChain.doubleton_iff.mp (ΘChain.cons_cons_iff'.mp (ΘChain.append_iff.mp Θ).2).1 j' hkj';
  exact nej <| by
    simpa using! ProvabilityComparison.le_antisymm (V := V)
      (P hj₁ Θε₁ <| cε₂.rel_of_infix _ _ <| List.infix_iff_prefix_suffix.mpr ⟨_, by simp, hj₂⟩)
      (P hj₂ Θε₂ <| cε₁.rel_of_infix _ _ <| List.infix_iff_prefix_suffix.mpr ⟨_, by simp, hj₁⟩);

/-- Solovay condition `SC2`. -/
lemma Solovay.consistent {i j : M.World} (hij : i ≺ j) :
    T.Solovay M V i → ¬Provable T (⌜∼T.solovay M j⌝ : V) := fun h ↦
  (Theory.ConsistentWith.quote_iff T).mp (h.2 j hij)

lemma Solovay.refute {i : M.World} (ne : M.root ≠ i) :
    T.Solovay M V i → Provable T (⌜∼T.solovay M i⌝ : V) := by
  rintro ⟨⟨ε, hε, cε⟩, _⟩;
  obtain ⟨ε', i', hii', rfl, _⟩ := List.ChainI.prec_exists_of_ne hε ne.symm;
  have : T.ProvabilityComparisonLE (V := V) ⌜∼T.solovay M i⌝ ⌜∼T.solovay M i⌝ := by
    simpa [NegativeSuccessor.quote_iff_provabilityComparisonLE] using!
      (ΘChain.cons_cons_iff.mp cε).2 i hii';
  exact (ProvabilityComparison.iff_le_refl_provable (T := T)).mp this;

lemma Θ.disjunction (i : M.World) (hΘ : Θ T M V i) :
    T.Solovay M V i ∨ ∃ j, i ≺ j ∧ T.Solovay M V j := by
  induction i using (IsConverseWellFounded.cwf (rel := M.Rel)).induction with
  | h i ih =>
    by_cases hS : T.Solovay M V i;
    · simp [hS];
    right;
    obtain ⟨j, hij, hj⟩ : ∃ j, i ≺ j ∧
        ∀ k, i ≺ k → T.ProvabilityComparisonLE (V := V) ⌜∼T.solovay M j⌝ ⌜∼T.solovay M k⌝ := by
      obtain ⟨j', hij', hj'⟩ : ∃ j, i ≺ j ∧ Provable T (⌜∼T.solovay M j⌝ : V) := by
        simpa [Theory.ConsistentWith.quote_iff] using! not_and.mp hS hΘ;
      obtain ⟨⟨j, hij⟩, hj⟩ := ProvabilityComparison.find_minimal_proof_fintype (T := T)
        (i := (⟨j', hij'⟩ : {j : M.World // i ≺ j})) (fun k ↦ ⌜∼T.solovay M k.val⌝) (by simpa);
      exact ⟨j, hij, fun k hk ↦ hj ⟨k, hk⟩⟩;
    have hΘj : Θ T M V j := by
      obtain ⟨ε, hε, cε⟩ := hΘ;
      use j :: ε, hε.cons hij;
      rcases hε <;>
        exact .cons (by simpa [NegativeSuccessor.quote_iff_provabilityComparisonLE]) cε;
    rcases ih j hij hΘj with hSj | ⟨k, hjk, hSk⟩;
    · exact ⟨j, hij, hSj⟩;
    · exact ⟨k, IsTrans.trans _ _ _ hij hjk, hSk⟩;

/-- Solovay condition `SC4`. -/
lemma disjunctive : ∃ i : M.World, T.Solovay M V i := by
  rcases Θ.disjunction (V := V) (T := T) M.root ⟨[M.root], by simp⟩ with H | ⟨_, _, H⟩ <;>
    exact ⟨_, H⟩;

open Classical in
/-- Solovay condition `SC3`. -/
lemma Solovay.box_disjunction [𝗜𝚺₁ ⪯ T] {i : M.World} (ne : M.root ≠ i) :
    T.Solovay M V i → Provable T (⌜⩖ j ∈ {j : M.World | i ≺ j}, T.solovay M j⌝ : V) := by
  intro hS;
  have h₁ : T.internalize V ⊢
      ⌜θ T M i 🡒 T.solovay M i ⋎ ⩖ j ∈ {j : M.World | i ≺ j}, T.solovay M j⌝ :=
    internal_provable_of_outer_provable <| WeakerThan.pbl (𝓢 := 𝗜𝚺₁) <|
      complete _ _ fun (V : Type) _ _ ↦ by simpa [models_iff] using! Θ.disjunction i;
  have h₂ : T.internalize V ⊢ ⌜θ T M i⌝ :=
    Bootstrapping.Arithmetic.sigma_one_provable_of_models T (θ_sigma1 T M i)
      (by simpa [models_iff] using! hS.1);
  have h₃ : T.internalize V ⊢ ∼⌜T.solovay M i⌝ := by
    simpa using! tprovable_tquote_iff_provable_quote.mpr (Solovay.refute ne hS);
  exact tprovable_tquote_iff_provable_quote.mp (of_A_of_N ((by simpa using! h₁) ⨀ h₂) h₃);

end model

section

variable {M : RootedModel κ α} [Fintype M.World] [M.IsGL]

/-- - [Sol76] -/
theorem solovay_root_sound [𝗜𝚺₁ ⪯ T] [sound : T.SoundOn (Arithmetic.Hierarchy 𝚷 2)] :
    T.Solovay M ℕ M.root := by
  classical
  obtain H | ⟨i, hri, H⟩ := Θ.disjunction (V := ℕ) (T := T) M.root ⟨[M.root], by simp⟩;
  · exact H;
  set π := θ T M i ⋏ ⩕ j ∈ { j : M.World | i ≺ j }, T.consistentWith.val/[⌜T.solovay M j⌝];
  have sπ : 𝗜𝚺₁ ⊢ T.solovay M i 🡘 π := solovay_diag T M i;
  have h₁ : T ⊢ ∼π := K_left (ENN_of_E (WeakerThan.wk inferInstance sπ)) ⨀
    (provable_iff_provable (T := T)).mp (Solovay.refute (ne_of_irrefl hri) H);
  have h₂ : ¬ℕ ⊧/![] π := by
    simpa [models_iff] using! sound.sound (σ := ∼π) h₁ (by simp [π,
      (show Hierarchy 𝚷 1 T.consistentWith.val by simp).strict_mono 𝚺 (show 1 < 2 by simp),
      (θ_sigma1 T M i).mono (show 1 ≤ 2 by simp)]);
  have h₃ : T.Solovay M ℕ i ↔ ℕ ⊧/![] π := by
    simpa [models_iff] using! consequence_iff.mp (Theory.Proof.sound sπ) ℕ inferInstance;
  exact absurd (h₃.mp H) h₂;

end

end FFL.FirstOrder.Arithmetic.Bootstrapping.SolovaySentences


namespace FFL.ProvabilityLogic

open FirstOrder ProvabilityAbstraction Arithmetic Bootstrapping SolovaySentences
open Kripke Kripke.Model.World

variable {κ α : Type*} [Nonempty κ] {A : Formula α}

/-- Solovay sentences for the standard provability predicate. -/
noncomputable def standardSolovaySentences (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T]
    (M : RootedModel κ α) [Fintype M.World] [M.IsGL] :
    T.standardProvability.SolovaySentences M where
  σ := T.solovay M
  SC1 _ _ ne := complete _ _ fun (V : Type) _ _ ↦ by simpa [models_iff] using! Solovay.exclusive ne
  SC2 _ _ h := complete _ _ fun (V : Type) _ _ ↦ by
    simpa [models_iff, standardProvability_def] using! Solovay.consistent h
  SC3 _ h := complete _ _ fun (V : Type) _ _ ↦ by
    simpa [models_iff, standardProvability_def] using! Solovay.box_disjunction h
  SC4 := complete _ _ fun (V : Type) _ _ ↦ by simpa [models_iff] using! disjunctive

theorem unprovable_realization_exists (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T]
    (M : RootedModel κ α) [Fintype M.World] [M.IsGL]
    (hA : M.root ⊮ A) (h : M.height < T.height) :
    ∃ f : Realization α ℒₒᵣ, T ⊬ f T A := by
  let S := standardSolovaySentences T M.extendRoot;
  use S.realization;
  contrapose! h;
  apply Order.le_of_lt_add_one;
  calc
    T.height < M.extendRoot.height := S.theory_height (T.standardProvability.syntactical_sound ℕ)
      (forces_dia.mpr ⟨some M.root, trivial, RootedModel.extendRoot.forces_some.not.mpr hA⟩) h
    _        = M.height + 1        := by simp [RootedModel.extendRoot.height_extendRoot];

end FFL.ProvabilityLogic

end

end
