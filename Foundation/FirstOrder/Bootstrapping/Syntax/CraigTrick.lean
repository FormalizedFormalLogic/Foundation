module

public import Foundation.FirstOrder.Arithmetic.ISigma1.Prenex
public import Foundation.FirstOrder.Arithmetic.R0.Representation
public import Foundation.FirstOrder.Bootstrapping.Syntax.Theory
public import Foundation.FirstOrder.Bootstrapping.Syntax.Formula.Iteration
public import Foundation.FirstOrder.Basic.Padding
public import Foundation.FirstOrder.Basic.PrimrecCoding

/-!
# Craig's trick

The Craig companion of a recursively enumerable theory is moreover primitive recursive.
-/

@[expose] public section

namespace FFL.FirstOrder.Semiformula

open Encodable

variable {L : Language} {ξ : Type*} {n : ℕ}

lemma weight_succ (k : ℕ) :
    (weight (k + 1) : Semiformula L ξ n) = ⊤ ⋏ weight k := by
  simp [weight, List.replicate_succ];

variable [L.Encodable] [Encodable ξ]

lemma encode_weight_succ (k : ℕ) :
    encode (weight (k + 1) : Semiformula L ξ n) =
      Nat.pair 4 (Nat.pair (encode (⊤ : Semiformula L ξ n))
        (encode (weight k : Semiformula L ξ n))) + 1 := by
  rw [weight_succ]; rfl;

private lemma left_lt_pair4 (a b : ℕ) : a < Nat.pair 4 (Nat.pair a b) + 1 := by
  have := Nat.left_le_pair a b;
  have := Nat.right_le_pair 4 (Nat.pair a b);
  omega;

private lemma right_lt_pair4 (a b : ℕ) : b < Nat.pair 4 (Nat.pair a b) + 1 := by
  have := Nat.right_le_pair a b;
  have := Nat.right_le_pair 4 (Nat.pair a b);
  omega;

lemma le_encode_weight (k : ℕ) :
    k ≤ encode (weight k : Semiformula L ξ n) := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [encode_weight_succ];
    exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (right_lt_pair4 _ _));

lemma encode_padding (φ : Semiformula L ξ n) (k : ℕ) :
    encode (φ.padding k) =
      Nat.pair 4 (Nat.pair (encode φ) (encode (weight k : Semiformula L ξ n))) + 1 := rfl

lemma encode_lt_encode_padding (φ : Semiformula L ξ n) (k : ℕ) :
    encode φ < encode (φ.padding k) := by
  simp only [encode_padding]; exact left_lt_pair4 _ _;

lemma lt_encode_padding (φ : Semiformula L ξ n) (k : ℕ) :
    k < encode (φ.padding k) := by
  simp only [encode_padding];
  exact lt_of_le_of_lt (le_encode_weight (L := L) (ξ := ξ) (n := n) k) (right_lt_pair4 _ _);

lemma primrec_encode_weight :
    Primrec fun k : ℕ ↦ encode (weight k : Semiformula L ξ n) := by
  have step : Primrec₂ fun _ r : ℕ ↦
      Nat.pair 4 (Nat.pair (encode (⊤ : Semiformula L ξ n)) r) + 1 :=
    Primrec.nat_add.comp
      (Primrec₂.natPair.comp (Primrec.const 4)
        (Primrec₂.natPair.comp (Primrec.const (encode (⊤ : Semiformula L ξ n))) Primrec.snd))
      (Primrec.const 1);
  refine (Primrec.nat_rec₁ (encode (⊤ : Semiformula L ξ n)) step).of_eq ?_;
  intro k;
  induction k with
  | zero => simp [weight]
  | succ k ih => simp [encode_weight_succ, ih]

end FFL.FirstOrder.Semiformula

namespace FFL.FirstOrder.Theory

open FFL.FirstOrder.Arithmetic

variable {L : Language} [L.Encodable]

section
variable [L.Primcodable]

-- `[T.RE]` is spelled out instead of taken from a `variable`: the body does not use it, so Lean
-- would drop it from the signature and let the Craig companion be built for an arbitrary theory.
noncomputable def reCh (T : Theory L) [T.RE] : 𝚺₁.Semisentence 1 :=
  .mkSigma (codeOfREPred (Encodable.encode '' T)) $ by simp [codeOfREPred, codeOfPartrec']

variable (T : Theory L) [T.RE]

noncomputable def reWitness : 𝚺₀.Semisentence 2 :=
  (ISigma1.exists_matrix_provable T.reCh.sigma_prop).choose

lemma reWitness_spec (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (e : Fin 1 → V) :
    V ⊧/e T.reCh.val ↔ ∃ w, V ⊧/(w :> e) T.reWitness.val :=
  (models_iff_of_provable_iff
    (ISigma1.exists_matrix_provable T.reCh.sigma_prop).choose_spec V e).trans
    Semiformula.eval_ex

@[simp, grind .]
lemma rePred_codes_of_RE : REPred (Encodable.encode '' T) :=
  ((Theory.RE.re.comp Computable.snd).and (PrimrecPred.computablePred
    (Primrec.eq.comp (Primrec.encode.comp Primrec.snd) Primrec.fst)).to_re).projection.of_eq
    fun _ ↦ Iff.rfl

variable [L.LORDefinable]

lemma exists_mem_of_reCh (φ : Proposition L) (h : ℕ ⊧/![⌜φ⌝] T.reCh.val) : ∃ σ ∈ T, φ = σ := by
  rcases (Set.mem_image ..).mp ((codeOfREPred_spec (rePred_codes_of_RE T)).mp h) with ⟨σ, hσ, hσφ⟩;
  exact ⟨σ, hσ, Semiformula.encode_inj_sentence.mp (by simpa [Semiformula.quote_eq_encode_nat] using hσφ)⟩;

lemma mem_of_reCh (σ : Sentence L) (h : ℕ ⊧/![⌜σ⌝] T.reCh.val) : σ ∈ T := by
  rcases (Set.mem_image ..).mp ((codeOfREPred_spec (rePred_codes_of_RE T)).mp h) with ⟨ρ, hρ, hρσ⟩;
  rwa [Encodable.encode_inj.mp (hρσ.trans (Sentence.quote_eq_encode_nat σ))] at hρ;

lemma reCh_of_mem (σ : Sentence L) (hσ : σ ∈ T) : ℕ ⊧/![⌜σ⌝] T.reCh.val :=
  (codeOfREPred_spec (rePred_codes_of_RE T)).mpr
    ((Set.mem_image ..).mpr ⟨σ, hσ, by simp [Sentence.quote_def, Semiformula.quote_eq_encode_nat]⟩)

def craig : Theory L := { φ | ∃ (σ : Sentence L) (s : ℕ), ℕ ⊧/![(s : ℕ), ⌜σ⌝] T.reWitness.val ∧ φ = σ.padding s}

end

end FFL.FirstOrder.Theory

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

variable {L : Language} [L.Encodable] [L.LORDefinable]

lemma quote_eq_qqAnd_iff {φ : Proposition L} {p q : ℕ} :
    (⌜φ⌝ : ℕ) = p ^⋏ q ↔ ∃ φ₁ φ₂, φ = φ₁ ⋏ φ₂ ∧ p = ⌜φ₁⌝ ∧ q = ⌜φ₂⌝ := by
  constructor
  . intro h
    cases φ with
    | rel | nrel => simp [qqRel, qqNRel, qqAnd] at h
    | verum =>
      change qqVerum = p ^⋏ q at h;
      simp [qqVerum, qqAnd] at h
    | falsum =>
      change qqFalsum = p ^⋏ q at h;
      simp [qqFalsum, qqAnd] at h
    | or φ₁ φ₂ =>
      change ⌜φ₁⌝ ^⋎ ⌜φ₂⌝ = p ^⋏ q at h;
      simp [qqOr, qqAnd] at h
    | all φ =>
      change ^∀ ⌜φ⌝ = p ^⋏ q at h;
      simp [qqAll, qqAnd] at h
    | exs φ =>
      change ^∃ ⌜φ⌝ = p ^⋏ q at h
      simp [qqExs, qqAnd] at h
    | and φ₁ φ₂ =>
      rcases (qqAnd_inj _ _ _ _).mp h with ⟨rfl, rfl⟩
      exact ⟨φ₁, φ₂, rfl, rfl, rfl⟩
  . rintro ⟨φ₁, φ₂, rfl, rfl, rfl⟩;
    rfl

section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma quote_weight (k : ℕ) : (⌜(Semiformula.weight k : Proposition L)⌝ : V) = qqVerums (k : V) := by
  induction k with
  | zero => simp [Semiformula.weight]
  | succ k ih =>
    change ⌜(⊤ : Proposition L) ⋏ Semiformula.weight k⌝ = _
    simp [ih]

lemma quote_padding (φ : Proposition L) (k : ℕ) : (⌜φ.padding k⌝ : V) = ⌜φ⌝ ^⋏ qqVerums (k : V) := by
  change ⌜φ ⋏ Semiformula.weight k⌝ = _
  simp [quote_weight]

namespace Sentence

lemma quote_padding (σ : Sentence L) (k : ℕ) : (⌜σ.padding k⌝ : V) = ⌜σ⌝ ^⋏ qqVerums (k : V) := by
  simpa [Sentence.quote_def] using
    FFL.FirstOrder.Arithmetic.Bootstrapping.quote_padding (V := V) (Rewriting.emb σ) k

end Sentence

end

lemma quote_eq_qqVerums {χ : Proposition L} {s : ℕ} : (⌜χ⌝ : ℕ) = qqVerums (s : ℕ) → χ = Semiformula.weight s := by
  intro h;
  exact (Semiformula.quote_inj_iff (V := ℕ)).mp <| by simpa [quote_weight] using h

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [L.Primcodable]

section

variable (T : Theory L) [T.RE]

def _root_.FFL.FirstOrder.Theory.IsCraigAxiom : V → Prop :=
  fun x ↦ ∃ s p : V, x = p ^⋏ qqVerums s ∧ V ⊧/![s, p] T.reWitness.val

noncomputable def _root_.FFL.FirstOrder.Theory.craigCh : 𝚫₁.Semisentence 1 := .mkDelta
  (.mkSigma “x. ∃ s < x, ∃ p < x, ∃ v < x,
    !qqVerumsGraph v s ∧ !qqAndDef x p v ∧ !(T.reWitness.val) s p”
  )
  (.mkPi “x. ∃ s < x, ∃ p < x, ∃ v < x,
    (∀ v', !qqVerumsGraph v' s → v' = v) ∧ !qqAndDef x p v ∧ !(T.reWitness.val) s p”
  )

end

instance Theory.IsCraigAxiom.defined {T : Theory L} [T.RE] :
    𝚫₁-Predicate[V] (T.IsCraigAxiom : V → Prop) via T.craigCh := .mk <| by
  have h (v : Fin 1 → V) :
      (∃ s < v 0, ∃ p < v 0, qqVerums s < v 0 ∧ v 0 = p ^⋏ qqVerums s
        ∧ (Semiformula.Eval ![s, p] Empty.elim) T.reWitness.val) ↔
        ∃ s p, v 0 = p ^⋏ qqVerums s ∧ (Semiformula.Evalb ![s, p]) T.reWitness.val := by
    constructor
    . rintro ⟨s, _, p, _, _, h, hT⟩;
      use s, p;
    . rintro ⟨s, p, hx, hT⟩;
      exact ⟨s, hx ▸ lt_of_le_of_lt (le_qqVerums s) (lt_K!_right _ _), p,
        hx ▸ lt_K!_left _ _, hx ▸ lt_K!_right _ _, hx, hT⟩
  constructor
  . intro v; simp [Theory.craigCh, h]
  . intro v; simp [Theory.craigCh, Theory.IsCraigAxiom, h]

lemma Theory.isCraigAxiom_quote_iff {T : Theory L} [T.RE] (φ : Proposition L) :
    T.IsCraigAxiom (⌜φ⌝ : ℕ) ↔ ∃ ρ ∈ T.craig, φ = ρ := by
  constructor
  . rintro ⟨s, p, hφ, hT⟩
    rcases quote_eq_qqAnd_iff.mp hφ with ⟨φ₁, φ₂, hφ, hp, hs⟩
    have hφ₂ : φ₂ = Semiformula.weight s := quote_eq_qqVerums hs.symm
    have h₁ : ℕ ⊧/![p] T.reCh.val := (Theory.reWitness_spec T ℕ ![p]).mpr ⟨s, hT⟩
    rcases T.exists_mem_of_reCh φ₁ (by simpa [hp] using h₁) with ⟨ρ, hρ, hρ'⟩
    use ρ.padding s
    and_intros
    . use ρ, s
      and_intros
      . simpa [hp, hρ', Sentence.quote_def] using hT
      . rfl
    . rw [Semiformula.rew_padding]
      simpa [Semiformula.padding, Semiformula.weight, hρ', hφ₂] using hφ
  . rintro ⟨ρ, ⟨σ, s, hT, rfl⟩, rfl⟩
    use s, ⌜σ⌝
    and_intros
    . simpa [Sentence.quote_def] using Sentence.quote_padding (V := ℕ) σ s
    . exact hT

end FFL.FirstOrder.Arithmetic.Bootstrapping

namespace FFL.FirstOrder.Theory

open Arithmetic.Bootstrapping

open FFL.Entailment

open Encodable

variable {L : Language} [L.Encodable] [L.LORDefinable] [L.Primcodable] {T : Theory L} [T.RE]

lemma mem_craig_codes_iff (n : ℕ) :
    n ∈ Encodable.encode '' T.craig ↔
      ∃ s < n, ∃ m < n, (decode₂ (Sentence L) m).isSome ∧
        n = Nat.pair 4 (Nat.pair m
          (encode (Semiformula.weight s : Sentence L))) + 1 ∧
        ℕ ⊧/![s, m] T.reWitness.val := by
  constructor
  . rintro ⟨φ, ⟨σ, s, hs, rfl⟩, rfl⟩;
    use s, Semiformula.lt_encode_padding σ s, encode σ, Semiformula.encode_lt_encode_padding σ s;
    and_intros;
    . simp;
    . exact (Semiformula.encode_padding σ s).symm;
    . simpa [Sentence.quote_def, Semiformula.quote_eq_encode] using hs;
  . rintro ⟨s, _, m, _, hm, hn, hT⟩;
    obtain ⟨σ, hσ⟩ := Option.isSome_iff_exists.mp hm;
    have hσm : encode σ = m := decode₂_eq_some.mp hσ;
    use σ.padding s;
    and_intros;
    . use σ, s;
      and_intros;
      . simpa [Sentence.quote_def, Semiformula.quote_eq_encode, hσm] using hT;
      . rfl;
    . exact (Semiformula.encode_padding σ s).trans <| by simpa [hσm] using hn.symm;

-- `p = (m, (n, s))`: `m` is the sentence code, `n` is the candidate craig axiom code,
-- `s` is the padding index.
omit [L.LORDefinable] in
lemma primrecPred_craig_core : PrimrecPred fun p : ℕ × (ℕ × ℕ) ↦
    (decode₂ (Sentence L) p.1).isSome ∧
      p.2.1 = Nat.pair 4 (Nat.pair p.1 (encode (Semiformula.weight p.2.2 : Sentence L))) + 1 ∧
      ℕ ⊧/![p.2.2, p.1] T.reWitness.val := by
  have hm : Primrec fun p : ℕ × (ℕ × ℕ) ↦ p.1 := Primrec.fst;
  have hn : Primrec fun p : ℕ × (ℕ × ℕ) ↦ p.2.1 := Primrec.fst.comp Primrec.snd;
  have hs : Primrec fun p : ℕ × (ℕ × ℕ) ↦ p.2.2 := Primrec.snd.comp Primrec.snd;
  have hweight : Primrec fun p : ℕ × (ℕ × ℕ) ↦ encode (Semiformula.weight p.2.2 : Sentence L) :=
    Semiformula.primrec_encode_weight.comp hs;
  have hdecode : PrimrecPred fun p : ℕ × (ℕ × ℕ) ↦ (decode₂ (Sentence L) p.1).isSome := by
    simpa using Primrec.eq.comp
      (Primrec.option_isSome.comp (Primrec.decode₂.comp hm)) (Primrec.const true);
  have heq : PrimrecPred fun p : ℕ × (ℕ × ℕ) ↦
      p.2.1 = Nat.pair 4 (Nat.pair p.1 (encode (Semiformula.weight p.2.2 : Sentence L))) + 1 :=
    Primrec.eq.comp hn (Primrec.nat_add.comp
      (Primrec₂.natPair.comp (Primrec.const 4) (Primrec₂.natPair.comp hm hweight))
      (Primrec.const 1));
  have heval : PrimrecPred fun p : ℕ × (ℕ × ℕ) ↦ ℕ ⊧/![p.2.2, p.1] T.reWitness.val :=
    ((Arithmetic.delta0_primrec Empty.elim T.reWitness.sigma_prop).comp
      (Primrec.vector_cons.comp hs
        (Primrec.vector_cons.comp hm (Primrec.const List.Vector.nil)))).of_eq fun p ↦ by
      simp [List.Vector.cons_get];
  exact hdecode.and (heq.and heval);

lemma primrecPred_craig_codes : PrimrecPred (· ∈ Encodable.encode '' T.craig) := by
  refine PrimrecPred.of_eq ?_ fun n ↦ (mem_craig_codes_iff n).symm;
  have hinner : PrimrecPred fun p : ℕ × ℕ ↦
      ∃ m < p.1, (decode₂ (Sentence L) m).isSome ∧
        p.1 = Nat.pair 4 (Nat.pair m (encode (Semiformula.weight p.2 : Sentence L))) + 1 ∧
        ℕ ⊧/![p.2, m] T.reWitness.val :=
    ((PrimrecRel.exists_mem_list (primrecPred_craig_core (T := T)).primrecRel).comp
      (Primrec.list_range.comp Primrec.fst) Primrec.id).of_eq (by simp);
  exact ((PrimrecRel.exists_mem_list
      (hinner.comp (Primrec.pair Primrec.snd Primrec.fst)).primrecRel).comp
    Primrec.list_range Primrec.id).of_eq (by simp);

instance : T.craig.Primrec :=
  ⟨((primrecPred_craig_codes (T := T)).comp Primrec.encode).of_eq fun _ ↦ by simp⟩

section

noncomputable instance : (T.craig).Δ₁ where
  ch := T.craigCh
  mem_iff φ := (Theory.IsCraigAxiom.defined (V := ℕ) (T := T)).iff.trans
    (Theory.isCraigAxiom_quote_iff φ)
  isDelta1 := Arithmetic.HierarchySymbol.Semiformula.ProvablyProperOn.ofProperOn.{0} _ fun V _ _ ↦
    (Theory.IsCraigAxiom.defined (V := V) (T := T)).proper

variable [L.DecidableEq]

instance : T.craig ⪯ T := WeakerThan.ofAxm! $ by
  rintro σ ⟨ρ, s, hρ, rfl⟩;
  have hρ' : ℕ ⊧/![⌜ρ⌝] T.reCh.val := (reWitness_spec T ℕ ![⌜ρ⌝]).mpr ⟨s, hρ⟩
  have hρT : ρ ∈ T := T.mem_of_reCh ρ hρ'
  exact mdp (C_of_E_mpr (Entailment.padding_iff ρ s)) (by_axm hρT)

instance : T ⪯ T.craig := WeakerThan.ofAxm! $ by
  intro σ hσ;
  have hσ' : ℕ ⊧/![⌜σ⌝] T.reCh.val := T.reCh_of_mem σ hσ
  rcases (reWitness_spec T ℕ ![⌜σ⌝]).mp hσ' with ⟨s, hs⟩
  have hpadding : σ.padding s ∈ T.craig := ⟨σ, s, hs, rfl⟩
  exact mdp (C_of_E_mp (Entailment.padding_iff σ s)) (by_axm hpadding)

instance : T ≊ T.craig :=
  Equiv.antisymm_iff.mpr ⟨inferInstance, inferInstance⟩

instance [Consistent T] : Consistent T.craig :=
  Consistent.of_le inferInstance (inferInstance : T.craig ⪯ T)

end

end FFL.FirstOrder.Theory
