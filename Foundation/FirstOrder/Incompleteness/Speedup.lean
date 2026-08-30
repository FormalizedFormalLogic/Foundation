module

public import Foundation.FirstOrder.Basic.PrimrecCoding
public import Foundation.FirstOrder.Bootstrapping.DerivabilityCondition.D1
public import Foundation.FirstOrder.Incompleteness.Church
public import Mathlib.Computability.Reduce
public import Mathlib.Data.Nat.Log

/-!
# Ehrenfeucht–Mycielski speedup theorem

`Theory.minProof T σ` is the least code of a `T`-proof of `σ`, and `0` when `σ` is not
`T`-provable.
-/

@[expose] public section

namespace LO.FirstOrder.Arithmetic.Bootstrapping


section
variable {L : Language} [L.DecidableEq] {T : Theory L} {σ π : Sentence L}

lemma provable_insert_neg_iff_or :
    insert (∼σ) T ⊢ π ↔ T ⊢ σ ⋎ π :=
  Entailment.deduction_iff.trans ⟨λ h ↦ by cl_prover [h], λ h ↦ by cl_prover [h]⟩

end


section

variable {f : ℕ → ℕ}

private def boundedMax (f : ℕ → ℕ) (n : ℕ) : ℕ := Nat.rec (f 0) (λ k ih ↦ max ih (f (k + 1))) n

private lemma computable_boundedMax (hf : Computable f) : Computable (boundedMax f) := by
  have hstep : Computable λ q : ℕ × (ℕ × ℕ) ↦ max q.2.2 (f (q.2.1 + 1)) :=
    Computable₂.comp Primrec.nat_max.to_comp (Computable.snd.comp Computable.snd)
      (hf.comp (Computable.succ.comp (Computable.fst.comp Computable.snd)));
  exact Computable.nat_rec Computable.id (Computable.const (f 0)) hstep.to₂;

private lemma le_boundedMax {k n : ℕ} (h : k ≤ n) : f k ≤ boundedMax f n := by
  induction n with
  | zero => simp_all [boundedMax];
  | succ n ih => rcases Nat.eq_or_lt_of_le h with rfl | h <;> simp_all [boundedMax];

end


variable
  {α : Type*} [Primcodable α]
  {L : Language} [L.DecidableEq] [L.Encodable] [L.LORDefinable]
  {T : Theory L} [T.Δ₁] {σ : Sentence L}

noncomputable def _root_.LO.FirstOrder.Theory.minProof (T : Theory L) [T.Δ₁] (σ : Sentence L) : ℕ :=
  sInf (Set.range λ d : T ⊢! σ ↦ (⌜d⌝ : ℕ))

@[grind →]
lemma proof_minProof (h : T ⊢ σ) : Proof T (T.minProof σ) ⌜σ⌝ := by
  obtain ⟨b, hb⟩ : T.minProof σ ∈ Set.range (λ d : T ⊢! σ ↦ (⌜d⌝ : ℕ)) :=
    Nat.sInf_mem ⟨_, Set.mem_range_self h.get⟩
  exact hb ▸ proof_of_quote_proof b

@[grind →]
lemma minProof_eq_zero_of_unprovable (h : T ⊬ σ) : T.minProof σ = 0 := by
  simp [Theory.minProof, Set.range_eq_empty_iff.mpr (Entailment.unprovable_iff_isEmpty.mp h)]

@[grind ←]
lemma minProof_le (b : T ⊢! σ) : T.minProof σ ≤ ⌜b⌝ := Nat.sInf_le (Set.mem_range_self b)

section Speedup

open Encodable

variable {F : α → Sentence L}

omit [L.DecidableEq] in
lemma computablePred_proof : ComputablePred λ p : ℕ × ℕ ↦ Proof T p.1 p.2 := by
  apply ComputablePred.computable_iff_re_compl_re'.mpr;
  obtain ⟨φ, hφ⟩ := HierarchySymbol.Definable.of_delta (Γ := 𝚺) (Proof.definable (V := ℕ) (T := T));
  obtain ⟨ψ, hψ⟩ := (HierarchySymbol.Definable.of_delta (Γ := 𝚷) (Proof.definable (V := ℕ) (T := T))).notPi;
  have hcomp : Computable λ p : ℕ × ℕ ↦ (p.1 ::ᵥ p.2 ::ᵥ List.Vector.nil : List.Vector ℕ 2) :=
    Primrec.to_comp <|
    Primrec.vector_cons.comp .fst (Primrec.vector_cons.comp .snd (.const List.Vector.nil));
  exact ⟨((sigma1_re id φ.sigma_prop).comp hcomp).of_eq
      λ p ↦ by simpa [List.Vector.cons_get] using hφ.iff (v := ![p.1, p.2]),
    ((sigma1_re id ψ.sigma_prop).comp hcomp).of_eq
      λ p ↦ by simpa [List.Vector.cons_get] using hψ.iff (v := ![p.1, p.2])⟩;

def speedupDerivation {φ : Proposition L} (d : ⊢ᴸᴷ¹ [φ, ∼φ]) (ψ : Proposition L) :
    ⊢ᴸᴷ¹ [φ ⋎ ψ, ∼φ] := Derivation.or d.contra

def speedupProof (σ π : Sentence L) : insert σ T ⊢! σ ⋎ π where
  axioms := [σ]
  axioms_mem := by simp
  derivation := .cast (speedupDerivation (Derivation.eta ↑σ) ↑π)

section

variable {Γ Δ : Finset (Proposition L)} {χ ξ : Proposition L}

private lemma quote_cut (d₁ : T ⟹₂ insert χ Γ) (d₂ : T ⟹₂ insert (∼χ) Γ) :
    (⌜Derivation2.cut d₁ d₂⌝ : ℕ) = cutRule ⌜Γ⌝ ⌜χ⌝ ⌜d₁⌝ ⌜d₂⌝ := by
  show (Derivation2.typedQuote ℕ (Derivation2.cut d₁ d₂)).val = _;
  simp only [Derivation2.typedQuote, TDerivation.cut_val, TDerivation.cast_val];
  rfl;

private lemma quote_axm (ψ : Sentence L) (hT : ψ ∈ T) (hΓ : (ψ : Proposition L) ∈ Γ) :
    (⌜Derivation2.axm (Γ := Γ) ψ hT hΓ⌝ : ℕ) = axm ⌜Γ⌝ ⌜ψ⌝ := by
  show (Derivation2.typedQuote ℕ (Derivation2.axm ψ hT hΓ)).val = _;
  simp only [Derivation2.typedQuote, TDerivation.byAxm_val];
  rfl;

private lemma quote_or (h : χ ⋎ ξ ∈ Γ) (d : T ⟹₂ insert χ (insert ξ Γ)) :
    (⌜Derivation2.or h d⌝ : ℕ) = orIntro ⌜Γ⌝ ⌜χ⌝ ⌜ξ⌝ ⌜d⌝ := by
  show (Derivation2.typedQuote ℕ (Derivation2.or h d)).val = _;
  simp only [Derivation2.typedQuote, TDerivation.or'_val, TDerivation.cast_val];
  rfl;

private lemma quote_wk (d : T ⟹₂ Δ) (ss : Δ ⊆ Γ) :
    (⌜Derivation2.wk d ss⌝ : ℕ) = wkRule ⌜Γ⌝ ⌜d⌝ := by
  show (Derivation2.typedQuote ℕ (Derivation2.wk d ss)).val = _;
  simp only [Derivation2.typedQuote, TDerivation.wk_val];
  rfl;

end

section

variable {φ ψ : Sentence L}

private lemma quote_cutManyProof_singleton (hψ : ∀ χ ∈ [ψ], χ ∈ T)
    (e : T ⟹₂ insert (φ : Proposition L) (∼Sequent.embed [ψ]).toFinset) :
    (⌜Derivation2.cutManyProof [ψ] hψ e⌝ : ℕ)
      = cutRule ⌜insert (φ : Proposition L) (∅ : Finset (Proposition L))⌝ ⌜ψ⌝
          (axm ⌜insert (ψ : Proposition L)
            (insert (φ : Proposition L) (∅ : Finset (Proposition L)))⌝ ⌜ψ⌝) ⌜e⌝ := by
  have h : (⌜Derivation2.cutManyProof [ψ] hψ e⌝ : ℕ)
      = ⌜Derivation2.cut (Γ := insert (φ : Proposition L) (∅ : Finset (Proposition L)))
            (φ := (ψ : Proposition L)) (Derivation2.axm ψ (hψ ψ (by simp)) (by simp))
            (Derivation2.cast e (by ext x; simp [Sequent.embed]; grind))⌝ := rfl;
  rw [h, quote_cut, quote_axm, Derivation2.quote_cast];
  rfl;

private lemma quote_proof_eq (b : T ⊢! φ) (h : b.axioms = [ψ]) :
    (⌜b⌝ : ℕ)
      = cutRule ⌜insert (φ : Proposition L) (∅ : Finset (Proposition L))⌝ ⌜ψ⌝
          (axm ⌜insert (ψ : Proposition L)
            (insert (φ : Proposition L) (∅ : Finset (Proposition L)))⌝ ⌜ψ⌝)
          ⌜Derivation.toDerivation2 T b.derivation⌝ := by
  obtain ⟨A, hA, d⟩ := b;
  subst h;
  rw [quote_proof_def];
  have h : (⌜(⟨[ψ], hA, d⟩ : T ⊢! φ).toProof2⌝ : ℕ)
      = ⌜Derivation2.cutManyProof [ψ] hA
          ((Derivation2.cast (Derivation.toDerivation2 T d)
              (by ext x; simp [List.toFinset_cons, Sequent.embed]) :
            T ⟹₂ insert (φ : Proposition L) (∼Sequent.embed [ψ]).toFinset))⌝ := rfl;
  rw [h, quote_cutManyProof_singleton, Derivation2.quote_cast];

end

section

variable {χ ξ : Proposition L}

private lemma quote_pullback_cast {A : List (Sentence L)} {Γ : List (Proposition L)}
    (d : ⊢ᴸᴷ¹ Γ) (h : Γ = A.map Rewriting.emb) :
    (⌜Derivation.toDerivation2 T (OneSidedLK.Pullback.cast d h)⌝ : ℕ)
      = ⌜Derivation.toDerivation2 T d⌝ := by
  subst h; rfl;

private lemma quote_speedupDerivation (d : ⊢ᴸᴷ¹ [χ, ∼χ]) :
    (⌜Derivation.toDerivation2 T (speedupDerivation d ξ)⌝ : ℕ)
      = orIntro ⌜([χ ⋎ ξ, ∼χ] : List (Proposition L)).toFinset⌝ ⌜χ⌝ ⌜ξ⌝
          (wkRule ⌜insert χ (insert ξ ([χ ⋎ ξ, ∼χ] : List (Proposition L)).toFinset)⌝
            (wkRule ⌜([χ, ξ, ∼χ] : List (Proposition L)).toFinset⌝
              ⌜Derivation.toDerivation2 T d⌝)) := by
  have h₁ : (⌜Derivation.toDerivation2 T (speedupDerivation d ξ)⌝ : ℕ)
      = ⌜Derivation2.or (Γ := ([χ ⋎ ξ, ∼χ] : List (Proposition L)).toFinset)
          (φ := χ) (ψ := ξ) (by simp)
          (Derivation2.wk (Derivation.toDerivation2 T (Derivation.contra (Γ := [χ, ξ, ∼χ]) d))
            (by simp))⌝ := rfl;
  have h₂ : (⌜Derivation.toDerivation2 T (Derivation.contra (Γ := [χ, ξ, ∼χ]) d)⌝ : ℕ)
      = ⌜Derivation2.wk (Γ := ([χ, ξ, ∼χ] : List (Proposition L)).toFinset)
          (Derivation.toDerivation2 T d) (by simp)⌝ := rfl;
  rw [h₁, quote_or, quote_wk, h₂, quote_wk];

end

private lemma quote_speedupProof_eq (π : Sentence L) :
    (⌜speedupProof (T := T) σ π⌝ : ℕ)
      = cutRule (insert ⌜σ ⋎ π⌝ ∅) ⌜σ⌝ (axm (insert ⌜σ⌝ (insert ⌜σ ⋎ π⌝ ∅)) ⌜σ⌝)
          (orIntro (insert ⌜σ ⋎ π⌝ (insert ⌜∼σ⌝ ∅)) ⌜σ⌝ ⌜π⌝
            (wkRule (insert ⌜σ⌝ (insert ⌜π⌝ (insert ⌜σ ⋎ π⌝ (insert ⌜∼σ⌝ ∅))))
              (wkRule (insert ⌜σ⌝ (insert ⌜π⌝ (insert ⌜∼σ⌝ ∅)))
                ⌜Derivation.toDerivation2 (insert σ T)
                  (Derivation.eta (σ : Proposition L))⌝))) := by
  rw [quote_proof_eq (speedupProof σ π) rfl];
  have h : (⌜Derivation.toDerivation2 (insert σ T) (speedupProof (T := T) σ π).derivation⌝ : ℕ)
      = ⌜Derivation.toDerivation2 (insert σ T)
          (speedupDerivation (Derivation.eta (σ : Proposition L)) (π : Proposition L))⌝ :=
    quote_pullback_cast _ _;
  rw [h, quote_speedupDerivation];
  simp [Sentence.quote_def];

private lemma nat_mem_iff {x s : ℕ} : x ∈ s ↔ s / 2 ^ x % 2 = 1 := by
  simp [mem_iff_mem_bitIndices, Nat.testBit_eq_decide_div_mod_eq];

private lemma nat_insert_eq (x s : ℕ) :
    (insert x s : ℕ) = if s / 2 ^ x % 2 = 1 then s else s + 2 ^ x := by
  simp [insert_eq, bitInsert, exp_nat_eq_two_pow, nat_mem_iff];

private lemma primrec₂_nat_insert : Primrec₂ λ x s : ℕ ↦ (insert x s : ℕ) := by
  have hpow : Primrec λ z : ℕ × ℕ ↦ 2 ^ z.1 :=
    (Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (Primrec.const 2) Primrec.fst;
  have hc : PrimrecPred λ z : ℕ × ℕ ↦ z.2 / 2 ^ z.1 % 2 = 1 :=
    Primrec.eq.comp
      (Primrec.nat_mod.comp (Primrec.nat_div.comp Primrec.snd hpow) (Primrec.const 2))
      (Primrec.const 1);
  exact (Primrec.ite hc Primrec.snd (Primrec.nat_add.comp Primrec.snd hpow)).of_eq
    λ z ↦ (nat_insert_eq z.1 z.2).symm;

private lemma primrec_speedupCode {p q : α → ℕ} (hp : Primrec p) (hq : Primrec q)
    (a na n₀ : ℕ) :
    Primrec λ x ↦
      cutRule (insert (q x) ∅) a (axm (insert a (insert (q x) ∅)) a)
        (orIntro (insert (q x) (insert na ∅)) a (p x)
          (wkRule (insert a (insert (p x) (insert (q x) (insert na ∅))))
            (wkRule (insert a (insert (p x) (insert na ∅))) n₀))) := by
  have hins : ∀ {f g : α → ℕ}, Primrec f → Primrec g →
      Primrec λ x ↦ (insert (f x) (g x) : ℕ) := λ hf hg ↦ primrec₂_nat_insert.comp hf hg;
  have hpair : ∀ {f g : α → ℕ}, Primrec f → Primrec g →
      Primrec λ x ↦ Nat.pair (f x) (g x) := λ hf hg ↦ Primrec₂.natPair.comp hf hg;
  have hs₁ : Primrec λ x ↦ (insert (q x) ∅ : ℕ) := hins hq (Primrec.const ∅);
  have hs₂ : Primrec λ x ↦ (insert a (insert (q x) ∅) : ℕ) := hins (Primrec.const a) hs₁;
  have hax : Primrec λ x ↦ axm (insert a (insert (q x) ∅)) a :=
    (Primrec.succ.comp (hpair hs₂ (hpair (Primrec.const 9) (Primrec.const a)))).of_eq
      λ x ↦ by simp [axm, nat_pair_eq];
  have hs₃ : Primrec λ x ↦ (insert (q x) (insert na ∅) : ℕ) := hins hq (Primrec.const _);
  have hu : Primrec λ x ↦ (insert a (insert (p x) (insert na ∅)) : ℕ) :=
    hins (Primrec.const a) (hins hp (Primrec.const _));
  have hw₁ : Primrec λ x ↦ wkRule (insert a (insert (p x) (insert na ∅))) n₀ :=
    (Primrec.succ.comp (hpair hu (hpair (Primrec.const 6) (Primrec.const n₀)))).of_eq
      λ x ↦ by simp [wkRule, nat_pair_eq];
  have hv : Primrec λ x ↦ (insert a (insert (p x) (insert (q x) (insert na ∅))) : ℕ) :=
    hins (Primrec.const a) (hins hp hs₃);
  have hw₂ : Primrec λ x ↦ wkRule (insert a (insert (p x) (insert (q x) (insert na ∅))))
      (wkRule (insert a (insert (p x) (insert na ∅))) n₀) :=
    (Primrec.succ.comp (hpair hv (hpair (Primrec.const 6) hw₁))).of_eq
      λ x ↦ by simp [wkRule, nat_pair_eq];
  have hor : Primrec λ x ↦ orIntro (insert (q x) (insert na ∅)) a (p x)
      (wkRule (insert a (insert (p x) (insert (q x) (insert na ∅))))
        (wkRule (insert a (insert (p x) (insert na ∅))) n₀)) :=
    (Primrec.succ.comp
      (hpair hs₃ (hpair (Primrec.const 3) (hpair (Primrec.const a) (hpair hp hw₂))))).of_eq
      λ x ↦ by simp [orIntro, nat_pair_eq];
  exact (Primrec.succ.comp
    (hpair hs₁ (hpair (Primrec.const 8) (hpair (Primrec.const a) (hpair hax hor))))).of_eq
    λ x ↦ by simp [cutRule, nat_pair_eq];

lemma computable_quote_speedupProof [L.Primcodable] :
    Computable λ π ↦ (⌜speedupProof (T := T) σ π⌝ : ℕ) := by
  have hp : Primrec λ π : Sentence L ↦ (⌜π⌝ : ℕ) :=
    Primrec.encode.of_eq λ π ↦ (Sentence.quote_eq_encode_nat π).symm;
  have hq : Primrec λ π : Sentence L ↦ (⌜σ ⋎ π⌝ : ℕ) :=
    (Primrec.encode.comp (Semiformula.primrec₂_or.comp (Primrec.const σ) Primrec.id)).of_eq
      λ π ↦ (Sentence.quote_eq_encode_nat _).symm;
  exact Primrec.to_comp <|
    (primrec_speedupCode hp hq ⌜σ⌝ ⌜∼σ⌝
      ⌜Derivation.toDerivation2 (insert σ T) (Derivation.eta (σ : Proposition L))⌝).of_eq
      λ π ↦ (quote_speedupProof_eq π).symm;

lemma exists_computable_bound_minProof_or [L.Primcodable] :
    ∃ c : Sentence L → ℕ, Computable c ∧ ∀ π, (insert σ T).minProof (σ ⋎ π) ≤ c π :=
  ⟨λ π ↦ ⌜speedupProof σ π⌝, computable_quote_speedupProof,
    λ π ↦ minProof_le (speedupProof σ π)⟩

omit [L.DecidableEq] in
lemma computablePred_bddExists_proof [L.Primcodable]
  (hF : Computable F) {bd : α → ℕ} (hbd : Computable bd) :
  ComputablePred λ a ↦ ∃ d ≤ bd a, Proof T d ⌜F a⌝ := by
  set cd := λ a ↦ encode (F a);
  have hcd : Computable cd := Computable.encode.comp hF;
  obtain ⟨χ, hχ, hχe⟩ := ComputablePred.computable_iff.mp (computablePred_proof (T := T));
  have hstep : Computable (λ q : α × (ℕ × Bool) ↦ Bool.or q.2.2 (χ (q.2.1, cd q.1))) :=
    Computable₂.comp Primrec.or.to_comp (Computable.snd.comp Computable.snd)
      (hχ.comp (Computable.pair (Computable.fst.comp Computable.snd) (hcd.comp Computable.fst)));
  have hS : Computable λ a ↦ Nat.rec (motive := λ _ ↦ Bool) false (λ d ih ↦ ih || χ (d, cd a)) (bd a + 1) :=
    Computable.nat_rec (Computable.succ.comp hbd) (Computable.const false) hstep.to₂;
  refine ComputablePred.computable_iff.mpr ⟨_, hS, ?_⟩;
  . funext a;
    apply propext;
    have key : ∀ N e, (Nat.rec (motive := λ _ ↦ Bool) false (λ d ih ↦ ih || χ (d, e)) (N + 1) = true) ↔
      ∃ d ≤ N, χ (d, e) = true := by
      intro N e;
      induction N with
      | zero => simp;
      | succ n ih => grind;
    rw [key (bd a) (cd a), Sentence.quote_eq_encode_nat];
    exact exists_congr λ d ↦ and_congr_right λ _ ↦ (congrFun hχe (d, cd a)).to_iff;

lemma computablePred_provable_of_minProof_le [L.Primcodable] (hF : Computable F)
  {bd : α → ℕ} (hbd : Computable bd) (hb : ∀ a, T ⊢ F a → T.minProof (F a) ≤ bd a) :
  ComputablePred λ a ↦ T ⊢ F a := by
  apply ComputablePred.of_eq (computablePred_bddExists_proof (T := T) hF hbd);
  intro a;
  have hp : ∀ d, Proof T d ⌜F a⌝ → T ⊢ F a := λ d hd ↦ provable_iff_provable.mp ⟨d, hd⟩;
  grind;

/-- The Ehrenfeucht–Mycielski speedup theorem [EM71]. -/
theorem ehrenfeucht_mycielski_speedup [L.Primcodable]
  (hU : ¬ComputablePred (insert (∼σ) T).theory) (f : ℕ → ℕ) (hf : Computable f) :
  ∃ π : Sentence L, T ⊢ π ∧ f ((insert σ T).minProof π) < T.minProof π := by
  contrapose! hU;
  obtain ⟨c, hc, hcb⟩ := exists_computable_bound_minProof_or (T := T) (σ := σ);
  refine ComputablePred.of_eq ?_ (λ π ↦ provable_insert_neg_iff_or.symm);
  exact computablePred_provable_of_minProof_le
    (Semiformula.primrec₂_or.comp (Primrec.const σ) Primrec.id).to_comp
    ((computable_boundedMax hf).comp hc)
    λ π hπ ↦ (hU (σ ⋎ π) hπ).trans (le_boundedMax (hcb π));

theorem ehrenfeucht_mycielski_speedup_arithmetic
  {T : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T] {σ : ArithmeticSentence} (hσ : T ⊬ σ) (f : ℕ → ℕ) (hf : Computable f) :
  ∃ π : ArithmeticSentence, T ⊢ π ∧ f ((insert σ T).minProof π) < T.minProof π :=
  have : 𝗜𝚺₁ ⪯ insert (∼σ) T := Entailment.WeakerThan.trans ‹𝗜𝚺₁ ⪯ T› (Entailment.Axiomatized.le_of_subset (Set.subset_insert _ T));
  have : Entailment.Consistent (insert (∼σ) T) := Entailment.unprovable_iff_consistent_adjoin.mp hσ;
  ehrenfeucht_mycielski_speedup (uncomputable_theory_of_consistent : ¬ComputablePred (insert (∼σ) T).theory) f hf

example {T : ArithmeticTheory} [T.Δ₁] {σ : ArithmeticSentence} [𝗜𝚺₁ ⪯ T] (hσ : T ⊬ σ) :
  ∃ π : ArithmeticSentence, T ⊢ π ∧ (insert σ T).minProof π < Nat.log 2 (T.minProof π) := by
  obtain ⟨π, hπ, hlt⟩ := ehrenfeucht_mycielski_speedup_arithmetic hσ
    (λ x ↦ 2 ^ (x + 1))
    (((Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (Primrec.const 2) Primrec.succ).to_comp);
  use π;
  and_intros;
  . assumption;
  . apply Nat.le_log_iff_pow_le ?_ ?_ |>.mpr;
    all_goals grind;

end Speedup

end LO.FirstOrder.Arithmetic.Bootstrapping
