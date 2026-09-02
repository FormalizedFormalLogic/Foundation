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

namespace LO.FirstOrder.Semiformula

open Encodable

variable {L : Language} {ξ : Type*} {n : ℕ}

lemma weight_succ (k : ℕ) :
    (weight (k + 1) : Semiformula L ξ n) = ⊤ ⋏ weight k := by
  simp [weight, List.replicate_succ]

lemma encode_weight_succ [L.Encodable] [Encodable ξ] (k : ℕ) :
    encode (weight (k + 1) : Semiformula L ξ n) =
      Nat.pair 4 (Nat.pair (encode (⊤ : Semiformula L ξ n))
        (encode (weight k : Semiformula L ξ n))) + 1 := by
  rw [weight_succ]
  rfl

lemma le_encode_weight [L.Encodable] [Encodable ξ] (k : ℕ) :
    k ≤ encode (weight k : Semiformula L ξ n) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [encode_weight_succ]
    have h₁ := Nat.right_le_pair (encode (⊤ : Semiformula L ξ n))
      (encode (weight k : Semiformula L ξ n))
    have h₂ := Nat.right_le_pair 4
      (Nat.pair (encode (⊤ : Semiformula L ξ n))
        (encode (weight k : Semiformula L ξ n)))
    omega

lemma encode_padding [L.Encodable] [Encodable ξ] (φ : Semiformula L ξ n) (k : ℕ) :
    encode (φ.padding k) =
      Nat.pair 4 (Nat.pair (encode φ) (encode (weight k : Semiformula L ξ n))) + 1 := by
  rfl

lemma encode_lt_encode_padding [L.Encodable] [Encodable ξ]
    (φ : Semiformula L ξ n) (k : ℕ) :
    encode φ < encode (φ.padding k) := by
  rw [encode_padding]
  have h₁ := Nat.left_le_pair (encode φ) (encode (weight k : Semiformula L ξ n))
  have h₂ := Nat.right_le_pair 4
    (Nat.pair (encode φ) (encode (weight k : Semiformula L ξ n)))
  omega

lemma lt_encode_padding [L.Encodable] [Encodable ξ] (φ : Semiformula L ξ n) (k : ℕ) :
    k < encode (φ.padding k) := by
  rw [encode_padding]
  have h₁ := le_encode_weight (L := L) (ξ := ξ) (n := n) k
  have h₂ := Nat.right_le_pair (encode φ) (encode (weight k : Semiformula L ξ n))
  have h₃ := Nat.right_le_pair 4
    (Nat.pair (encode φ) (encode (weight k : Semiformula L ξ n)))
  omega

/-- The code of the iterated truth padding is primitive recursive.
This is a routine technical bridge from syntax recursion to code recursion. -/
lemma primrec_encode_weight [L.Encodable] [Encodable ξ] :
    Primrec fun k : ℕ ↦ encode (weight k : Semiformula L ξ n) := by
  let step : Primrec₂ fun _ r : ℕ ↦
      Nat.pair 4 (Nat.pair (encode (⊤ : Semiformula L ξ n)) r) + 1 :=
    Primrec.nat_add.comp
      (Primrec₂.natPair.comp (Primrec.const 4)
        (Primrec₂.natPair.comp (Primrec.const (encode (⊤ : Semiformula L ξ n))) Primrec.snd))
      (Primrec.const 1)
  refine (Primrec.nat_rec₁ (encode (⊤ : Semiformula L ξ n)) step).of_eq ?_
  intro k
  induction k with
  | zero => simp [weight]
  | succ k ih => simp [encode_weight_succ, ih]

end LO.FirstOrder.Semiformula

namespace LO.FirstOrder.Theory

open LO.FirstOrder.Arithmetic

-- `[T.RE]` is spelled out instead of taken from a `variable`: the body does not use it, so Lean
-- would drop it from the signature and let the Craig companion be built for an arbitrary theory.
noncomputable def reCh {L : Language} [L.Encodable] [L.LORDefinable] (T : Theory L) [T.RE] : 𝚺₁.Semisentence 1 :=
  .mkSigma (codeOfREPred fun n ↦ n ∈ T.codes) (by simp [codeOfREPred, codeOfPartrec'])

lemma reCh_mem_iff {L : Language} [L.Encodable] [L.LORDefinable] (T : Theory L) [T.RE] (φ : Proposition L) :
  ℕ ⊧/![⌜φ⌝] T.reCh.val ↔ ∃ σ ∈ T, φ = σ := by
  have hT : REPred fun n : ℕ ↦ n ∈ T.codes := Theory.RE.re
  simpa [Theory.reCh, Theory.codes, Matrix.fun_eq_vec_one, Semiformula.quote_eq_encode] using
    codeOfREPred_spec hT (x := ⌜φ⌝)

variable {L : Language} [L.Encodable] [L.LORDefinable]

section

variable (T : Theory L) [T.RE]

noncomputable def reWitness : 𝚺₀.Semisentence 2 :=
  let h := ISigma1.exists_matrix_provable T.reCh.sigma_prop;
  .mkSigma h.choose h.choose_spec.1

lemma reWitness_spec (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (e : Fin 1 → V) :
  V ⊧/e T.reCh.val ↔ ∃ w, V ⊧/(w :> e) T.reWitness.val := by
  simpa [reWitness] using
    (models_iff_of_provable_iff
      (ISigma1.exists_matrix_provable T.reCh.sigma_prop).choose_spec.2 V e).trans
      Semiformula.eval_ex

def craig : Theory L := { φ | ∃ (σ : Sentence L) (s : ℕ), ℕ ⊧/![(s : ℕ), ⌜σ⌝] T.reWitness.val ∧ φ = σ.padding s}

end

end LO.FirstOrder.Theory

namespace LO.FirstOrder.Arithmetic.Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

variable {L : Language} [L.Encodable] [L.LORDefinable]

section

variable (T : Theory L) [T.RE]

def _root_.LO.FirstOrder.Theory.IsCraigAxiom : V → Prop :=
  fun x ↦ ∃ s p : V, x = p ^⋏ qqVerums s ∧ V ⊧/![s, p] T.reWitness.val

noncomputable def _root_.LO.FirstOrder.Theory.craigCh : 𝚫₁.Semisentence 1 := .mkDelta
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
      refine ⟨s, ?_, p, ?_⟩;
      . exact hx ▸ lt_of_le_of_lt (le_qqVerums s) (lt_K!_right _ _)
      . and_intros
        . exact hx ▸ lt_K!_left _ _
        . exact hx ▸ lt_K!_right _ _
        . exact hx
        . exact hT
  constructor
  . intro v; simp [Theory.craigCh, h]
  . intro v; simp [Theory.craigCh, Theory.IsCraigAxiom, h]

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

lemma quote_weight (k : ℕ) : (⌜(Semiformula.weight k : Proposition L)⌝ : V) = qqVerums (k : V) := by
  induction k with
  | zero => simp [Semiformula.weight]
  | succ k ih =>
    change ⌜(⊤ : Proposition L) ⋏ Semiformula.weight k⌝ = _
    simp [ih]

lemma quote_eq_qqVerums {χ : Proposition L} {s : ℕ} : (⌜χ⌝ : ℕ) = qqVerums (s : ℕ) → χ = Semiformula.weight s := by
  intro h;
  exact (Semiformula.quote_inj_iff (V := ℕ)).mp <| by simpa [quote_weight] using h

lemma quote_padding (φ : Proposition L) (k : ℕ) : (⌜φ.padding k⌝ : V) = ⌜φ⌝ ^⋏ qqVerums (k : V) := by
  change ⌜φ ⋏ Semiformula.weight k⌝ = _
  simp [quote_weight]

namespace Sentence

lemma quote_padding (σ : Sentence L) (k : ℕ) : (⌜σ.padding k⌝ : V) = ⌜σ⌝ ^⋏ qqVerums (k : V) := by
  simpa [Sentence.quote_def] using
    LO.FirstOrder.Arithmetic.Bootstrapping.quote_padding (V := V) (Rewriting.emb σ) k

end Sentence

lemma Theory.isCraigAxiom_quote_iff {T : Theory L} [T.RE] (φ : Proposition L) :
    T.IsCraigAxiom (⌜φ⌝ : ℕ) ↔ ∃ ρ ∈ T.craig, φ = ρ := by
  constructor
  . rintro ⟨s, p, hφ, hT⟩
    rcases quote_eq_qqAnd_iff.mp hφ with ⟨φ₁, φ₂, hφ, hp, hs⟩
    have hφ₂ : φ₂ = Semiformula.weight s := quote_eq_qqVerums hs.symm
    have h₁ : ℕ ⊧/![p] T.reCh.val := (Theory.reWitness_spec T ℕ ![p]).mpr ⟨s, hT⟩
    rcases (T.reCh_mem_iff φ₁).mp (by simpa [hp] using h₁) with ⟨ρ, hρ, hρ'⟩
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

end LO.FirstOrder.Arithmetic.Bootstrapping

namespace LO.FirstOrder.Theory

open Arithmetic.Bootstrapping

variable {L : Language} [L.Encodable] [L.LORDefinable]

open LO.Entailment

section

variable {T : Theory L} [T.RE]

/-- Code-level bounded-search characterization of the axioms of the Craig companion.
This is a routine technical bridge specific to the coding used here. -/
lemma mem_craig_codes_iff (n : ℕ) :
    n ∈ T.craig.codes ↔
      ∃ s < n, ∃ m < n, (Encodable.decode₂ (Sentence L) m).isSome ∧
        n = Nat.pair 4 (Nat.pair m
          (Encodable.encode (Semiformula.weight s : Sentence L))) + 1 ∧
        ℕ ⊧/![s, m] T.reWitness.val := by
  constructor
  · rintro ⟨φ, ⟨σ, s, hs, rfl⟩, rfl⟩
    refine ⟨s, Semiformula.lt_encode_padding σ s,
      Encodable.encode σ, Semiformula.encode_lt_encode_padding σ s, ?_⟩
    simp only [Encodable.decode₂_encode, Option.isSome_some, true_and]
    exact ⟨(Semiformula.encode_padding σ s).symm,
      by simpa [Sentence.quote_def, Semiformula.quote_eq_encode] using hs⟩
  · rintro ⟨s, _, m, _, hm, hn, hT⟩
    obtain ⟨σ, hσ⟩ := Option.isSome_iff_exists.mp hm
    have hσm : Encodable.encode σ = m := Encodable.decode₂_eq_some.mp hσ
    refine ⟨σ.padding s, ⟨σ, s, ?_, rfl⟩, ?_⟩
    · simpa [Sentence.quote_def, Semiformula.quote_eq_encode, hσm] using hT
    · exact (Semiformula.encode_padding σ s).trans <| by simpa [hσm] using hn.symm

instance [L.Primcodable] : T.craig.Primrec := by
  constructor
  refine PrimrecPred.of_eq ?_ fun n ↦ (mem_craig_codes_iff n).symm
  let hm : Primrec fun p : ℕ × (ℕ × ℕ) ↦ p.1 := Primrec.fst
  let hn : Primrec fun p : ℕ × (ℕ × ℕ) ↦ p.2.1 := Primrec.fst.comp Primrec.snd
  let hs : Primrec fun p : ℕ × (ℕ × ℕ) ↦ p.2.2 := Primrec.snd.comp Primrec.snd
  have hdecode : PrimrecPred fun p : ℕ × (ℕ × ℕ) ↦
      (Encodable.decode₂ (Sentence L) p.1).isSome := by
    simpa using Primrec.eq.comp
      (Primrec.option_isSome.comp (Primrec.decode₂.comp hm)) (Primrec.const true)
  have hweight : Primrec fun p : ℕ × (ℕ × ℕ) ↦
      Encodable.encode (Semiformula.weight p.2.2 : Sentence L) :=
    Semiformula.primrec_encode_weight.comp hs
  have hpad : Primrec fun p : ℕ × (ℕ × ℕ) ↦
      Nat.pair 4 (Nat.pair p.1
        (Encodable.encode (Semiformula.weight p.2.2 : Sentence L))) + 1 :=
    Primrec.nat_add.comp
      (Primrec₂.natPair.comp (Primrec.const 4)
        (Primrec₂.natPair.comp hm hweight))
      (Primrec.const 1)
  have heq : PrimrecPred fun p : ℕ × (ℕ × ℕ) ↦
      p.2.1 = Nat.pair 4 (Nat.pair p.1
        (Encodable.encode (Semiformula.weight p.2.2 : Sentence L))) + 1 :=
    Primrec.eq.comp hn hpad
  have hvec : Primrec fun p : ℕ × (ℕ × ℕ) ↦
      (p.2.2 ::ᵥ p.1 ::ᵥ List.Vector.nil : List.Vector ℕ 2) :=
    Primrec.vector_cons.comp hs
      (Primrec.vector_cons.comp hm (Primrec.const List.Vector.nil))
  have heval : PrimrecPred fun p : ℕ × (ℕ × ℕ) ↦
      ℕ ⊧/![p.2.2, p.1] T.reWitness.val :=
    ((Arithmetic.delta0_primrec Empty.elim T.reWitness.sigma_prop).comp hvec).of_eq fun p ↦ by
      simp [List.Vector.cons_get]
  have hcore : PrimrecPred fun p : ℕ × (ℕ × ℕ) ↦
      (Encodable.decode₂ (Sentence L) p.1).isSome ∧
        p.2.1 = Nat.pair 4 (Nat.pair p.1
          (Encodable.encode (Semiformula.weight p.2.2 : Sentence L))) + 1 ∧
        ℕ ⊧/![p.2.2, p.1] T.reWitness.val := hdecode.and (heq.and heval)
  have hinner : PrimrecPred fun p : ℕ × ℕ ↦
      ∃ m < p.1, (Encodable.decode₂ (Sentence L) m).isSome ∧
        p.1 = Nat.pair 4 (Nat.pair m
          (Encodable.encode (Semiformula.weight p.2 : Sentence L))) + 1 ∧
        ℕ ⊧/![p.2, m] T.reWitness.val :=
    ((PrimrecRel.exists_mem_list hcore.primrecRel).comp
      (Primrec.list_range.comp Primrec.fst) Primrec.id).of_eq (by simp)
  have houter : PrimrecRel fun s n : ℕ ↦
      ∃ m < n, (Encodable.decode₂ (Sentence L) m).isSome ∧
        n = Nat.pair 4 (Nat.pair m
          (Encodable.encode (Semiformula.weight s : Sentence L))) + 1 ∧
        ℕ ⊧/![s, m] T.reWitness.val :=
    (hinner.comp (Primrec.pair Primrec.snd Primrec.fst)).primrecRel
  exact ((PrimrecRel.exists_mem_list houter).comp Primrec.list_range Primrec.id).of_eq (by simp)

noncomputable instance : (T.craig).Δ₁ where
  ch := T.craigCh
  mem_iff φ := (Theory.IsCraigAxiom.defined (V := ℕ) (T := T)).iff.trans
    (Theory.isCraigAxiom_quote_iff φ)
  isDelta1 := Arithmetic.HierarchySymbol.Semiformula.ProvablyProperOn.ofProperOn.{0} _ fun V _ _ ↦
    (Theory.IsCraigAxiom.defined (V := V) (T := T)).proper

instance [L.DecidableEq] : T.craig ⪯ T := WeakerThan.ofAxm! $ by
  rintro σ ⟨ρ, s, hρ, rfl⟩;
  have hρ' : ℕ ⊧/![⌜ρ⌝] T.reCh.val := (reWitness_spec T ℕ ![⌜ρ⌝]).mpr ⟨s, hρ⟩
  rcases (T.reCh_mem_iff (Rewriting.emb ρ)).mp
    (by simpa [Sentence.quote_def] using hρ') with ⟨τ, hτ, hρτ⟩
  have hρT : ρ ∈ T := Rewriting.emb_injective hρτ ▸ hτ
  exact mdp (C_of_E_mpr (Entailment.padding_iff ρ s)) (by_axm hρT)

instance [L.DecidableEq] : T ⪯ T.craig := WeakerThan.ofAxm! $ by
  intro σ hσ;
  have hσ' : ℕ ⊧/![⌜σ⌝] T.reCh.val :=
    (T.reCh_mem_iff (Rewriting.emb σ)).mpr ⟨σ, hσ, rfl⟩
  rcases (reWitness_spec T ℕ ![⌜σ⌝]).mp hσ' with ⟨s, hs⟩
  have hpadding : σ.padding s ∈ T.craig := ⟨σ, s, hs, rfl⟩
  exact mdp (C_of_E_mp (Entailment.padding_iff σ s)) (by_axm hpadding)

instance [L.DecidableEq] : T ≊ T.craig :=
  Equiv.antisymm_iff.mpr ⟨inferInstance, inferInstance⟩

instance [L.DecidableEq] [Consistent T] : Consistent T.craig :=
  Consistent.of_le inferInstance (inferInstance : T.craig ⪯ T)

end

/-- Every recursively enumerable theory is equivalent to a primitive-recursively axiomatized
theory. This is the strengthened form of Craig's trick developed directly in this file. -/
theorem exists_primrec_equiv [L.Primcodable] [L.DecidableEq] (T : Theory L) [T.RE] :
    ∃ U : Theory L, U.Primrec ∧ Nonempty U.Δ₁ ∧ T ≊ U :=
  ⟨T.craig, inferInstance, ⟨inferInstance⟩, inferInstance⟩

end LO.FirstOrder.Theory
