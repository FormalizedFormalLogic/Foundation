module

public import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Coding
public import Foundation.Vorspiel.Computability

/-!
# Primitive recursive proof-code constructors

Primitive recursive closure lemmas for the numerical encodings used by the bootstrapped proof
system.
-/

@[expose] public section

namespace FFL.FirstOrder.Arithmetic.Bootstrapping

lemma primrec₂_nat_insert : Primrec₂ λ x s : ℕ ↦ (insert x s : ℕ) := by
  have hpow : Primrec λ z : ℕ × ℕ ↦ 2 ^ z.1 :=
    (Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (Primrec.const 2) Primrec.fst
  have hc : PrimrecPred λ z : ℕ × ℕ ↦ z.2 / 2 ^ z.1 % 2 = 1 :=
    Primrec.eq.comp
      (Primrec.nat_mod.comp (Primrec.nat_div.comp Primrec.snd hpow) (Primrec.const 2))
      (Primrec.const 1)
  exact (Primrec.ite hc Primrec.snd (Primrec.nat_add.comp Primrec.snd hpow)).of_eq
    λ z ↦ (nat_insert_eq z.1 z.2).symm

variable {α : Type*} [Primcodable α] {s p q t d d₁ d₂ : α → ℕ}

lemma primrec_insert (hp : Primrec p) (hq : Primrec q) :
    Primrec λ x ↦ (insert (p x) (q x) : ℕ) := primrec₂_nat_insert.comp hp hq

lemma primrec_axL (hs : Primrec s) (hp : Primrec p) : Primrec λ x ↦ axL (s x) (p x) :=
  (Primrec.succ.comp (Primrec₂.natPair.comp hs (Primrec₂.natPair.comp (.const 0) hp))).of_eq
    λ x ↦ by simp [axL, nat_pair_eq]

lemma primrec_verumIntro (hs : Primrec s) : Primrec λ x ↦ verumIntro (s x) :=
  (Primrec.succ.comp
    (Primrec₂.natPair.comp hs (Primrec₂.natPair.comp (.const 1) (.const 0)))).of_eq
    λ x ↦ by simp [verumIntro, nat_pair_eq]

lemma primrec_andIntro (hs : Primrec s) (hp : Primrec p) (hq : Primrec q)
    (hd₁ : Primrec d₁) (hd₂ : Primrec d₂) :
    Primrec λ x ↦ andIntro (s x) (p x) (q x) (d₁ x) (d₂ x) :=
  (Primrec.succ.comp (Primrec₂.natPair.comp hs (Primrec₂.natPair.comp (.const 2)
    (Primrec₂.natPair.comp hp
      (Primrec₂.natPair.comp hq (Primrec₂.natPair.comp hd₁ hd₂)))))).of_eq
    λ x ↦ by simp [andIntro, nat_pair_eq]

lemma primrec_orIntro (hs : Primrec s) (hp : Primrec p) (hq : Primrec q) (hd : Primrec d) :
    Primrec λ x ↦ orIntro (s x) (p x) (q x) (d x) :=
  (Primrec.succ.comp (Primrec₂.natPair.comp hs (Primrec₂.natPair.comp (.const 3)
    (Primrec₂.natPair.comp hp (Primrec₂.natPair.comp hq hd))))).of_eq
    λ x ↦ by simp [orIntro, nat_pair_eq]

lemma primrec_allIntro (hs : Primrec s) (hp : Primrec p) (hd : Primrec d) :
    Primrec λ x ↦ allIntro (s x) (p x) (d x) :=
  (Primrec.succ.comp (Primrec₂.natPair.comp hs (Primrec₂.natPair.comp (.const 4)
    (Primrec₂.natPair.comp hp hd)))).of_eq
    λ x ↦ by simp [allIntro, nat_pair_eq]

lemma primrec_exsIntro (hs : Primrec s) (hp : Primrec p) (ht : Primrec t) (hd : Primrec d) :
    Primrec λ x ↦ exsIntro (s x) (p x) (t x) (d x) :=
  (Primrec.succ.comp (Primrec₂.natPair.comp hs (Primrec₂.natPair.comp (.const 5)
    (Primrec₂.natPair.comp hp (Primrec₂.natPair.comp ht hd))))).of_eq
    λ x ↦ by simp [exsIntro, nat_pair_eq]

lemma primrec_wkRule (hs : Primrec s) (hd : Primrec d) : Primrec λ x ↦ wkRule (s x) (d x) :=
  (Primrec.succ.comp (Primrec₂.natPair.comp hs (Primrec₂.natPair.comp (.const 6) hd))).of_eq
    λ x ↦ by simp [wkRule, nat_pair_eq]

lemma primrec_shiftRule (hs : Primrec s) (hd : Primrec d) : Primrec λ x ↦ shiftRule (s x) (d x) :=
  (Primrec.succ.comp (Primrec₂.natPair.comp hs (Primrec₂.natPair.comp (.const 7) hd))).of_eq
    λ x ↦ by simp [shiftRule, nat_pair_eq]

lemma primrec_cutRule (hs : Primrec s) (hp : Primrec p)
    (hd₁ : Primrec d₁) (hd₂ : Primrec d₂) :
    Primrec λ x ↦ cutRule (s x) (p x) (d₁ x) (d₂ x) :=
  (Primrec.succ.comp (Primrec₂.natPair.comp hs (Primrec₂.natPair.comp (.const 8)
    (Primrec₂.natPair.comp hp (Primrec₂.natPair.comp hd₁ hd₂))))).of_eq
    λ x ↦ by simp [cutRule, nat_pair_eq]

lemma primrec_axm (hs : Primrec s) (hp : Primrec p) : Primrec λ x ↦ axm (s x) (p x) :=
  (Primrec.succ.comp (Primrec₂.natPair.comp hs (Primrec₂.natPair.comp (.const 9) hp))).of_eq
    λ x ↦ by simp [axm, nat_pair_eq]

section Derivation2

open Derivation2

variable {L : Language} [L.DecidableEq] [L.Encodable] [L.LORDefinable] {T : Theory L} [T.Δ₁]
  {Γ : α → Finset (Proposition L)} {φ ψ : α → Proposition L} {ξ : α → Sentence L}

lemma primrec_quote_singleton (hφ : Primrec λ x ↦ (⌜φ x⌝ : ℕ)) :
    Primrec λ x ↦ (⌜({φ x} : Finset (Proposition L))⌝ : ℕ) :=
  (primrec_insert hφ (.const ∅)).of_eq λ x ↦ by simp

lemma primrec_quote_insert (hφ : Primrec λ x ↦ (⌜φ x⌝ : ℕ)) (hΓ : Primrec λ x ↦ (⌜Γ x⌝ : ℕ)) :
    Primrec λ x ↦ (⌜φ x ⫽ Γ x⌝ : ℕ) :=
  (primrec_insert hφ hΓ).of_eq λ x ↦ by simp

lemma primrec_quote_or {h : ∀ x, φ x ⋎ ψ x ∈ Γ x}
    {d : ∀ x, T ⟹₂ φ x ⫽ ψ x ⫽ Γ x}
    (hΓ : Primrec λ x ↦ (⌜Γ x⌝ : ℕ)) (hφ : Primrec λ x ↦ (⌜φ x⌝ : ℕ))
    (hψ : Primrec λ x ↦ (⌜ψ x⌝ : ℕ)) (hd : Primrec λ x ↦ (⌜d x⌝ : ℕ)) :
    Primrec λ x ↦ (⌜Derivation2.or (h x) (d x)⌝ : ℕ) :=
  (primrec_orIntro hΓ hφ hψ hd).of_eq λ x ↦ by simp [quote_or]

lemma primrec_quote_axm {hT : ∀ x, ξ x ∈ T} {hm : ∀ x, ((ξ x : Sentence L) : Proposition L) ∈ Γ x}
    (hΓ : Primrec λ x ↦ (⌜Γ x⌝ : ℕ)) (hξ : Primrec λ x ↦ (⌜ξ x⌝ : ℕ)) :
    Primrec λ x ↦ (⌜Derivation2.axm (Γ := Γ x) (ξ x) (hT x) (hm x)⌝ : ℕ) :=
  (primrec_axm hΓ hξ).of_eq λ x ↦ by simp [quote_axm]

end Derivation2

end FFL.FirstOrder.Arithmetic.Bootstrapping
