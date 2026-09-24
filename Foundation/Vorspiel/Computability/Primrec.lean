module

public import Foundation.Vorspiel.Tactic.Primrec
public import Mathlib.Computability.Primrec.List

/-!
# The rules of the `primrec` tactic

Pointwise forms `Primrec fun a ↦ F (f a) (g a)` of Mathlib's combinators: the head `F` is what
lets Aesop key a rule.
-/

@[expose] public section

variable {α β γ δ σ : Type*} [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable δ]
  [Primcodable σ]

namespace Primrec

/-! ## The leaves -/

variable (α) in
lemma id' : Primrec fun a : α ↦ a := Primrec.id

/-! ## Products -/

lemma fst' {f : α → β × γ} (hf : Primrec f) : Primrec fun a ↦ (f a).1 := fst.comp hf

lemma snd' {f : α → β × γ} (hf : Primrec f) : Primrec fun a ↦ (f a).2 := snd.comp hf

/-! ## Arithmetic -/

section nat

variable {f g : α → ℕ}

lemma succ' (hf : Primrec f) : Primrec fun a ↦ (f a).succ := succ.comp hf

lemma nat_add' (hf : Primrec f) (hg : Primrec g) : Primrec fun a ↦ f a + g a :=
  nat_add.comp hf hg

lemma nat_sub' (hf : Primrec f) (hg : Primrec g) : Primrec fun a ↦ f a - g a :=
  nat_sub.comp hf hg

lemma nat_mul' (hf : Primrec f) (hg : Primrec g) : Primrec fun a ↦ f a * g a :=
  nat_mul.comp hf hg

lemma nat_div' (hf : Primrec f) (hg : Primrec g) : Primrec fun a ↦ f a / g a :=
  nat_div.comp hf hg

lemma nat_mod' (hf : Primrec f) (hg : Primrec g) : Primrec fun a ↦ f a % g a :=
  nat_mod.comp hf hg

lemma nat_max' (hf : Primrec f) (hg : Primrec g) : Primrec fun a ↦ max (f a) (g a) :=
  nat_max.comp hf hg

lemma nat_min' (hf : Primrec f) (hg : Primrec g) : Primrec fun a ↦ min (f a) (g a) :=
  nat_min.comp hf hg

lemma nat_pair' (hf : Primrec f) (hg : Primrec g) : Primrec fun a ↦ (f a).pair (g a) :=
  Primrec₂.natPair.comp hf hg

lemma unpair' (hf : Primrec f) : Primrec fun a ↦ (f a).unpair := unpair.comp hf

lemma nat_pow' (hf : Primrec f) (hg : Primrec g) : Primrec fun a ↦ f a ^ g a :=
  (Primrec₂.unpaired'.1 Nat.Primrec.pow).comp hf hg

lemma nat_le' (hf : Primrec f) (hg : Primrec g) : PrimrecPred fun a ↦ f a ≤ g a :=
  PrimrecRel.comp nat_le hf hg

lemma nat_lt' (hf : Primrec f) (hg : Primrec g) : PrimrecPred fun a ↦ f a < g a :=
  PrimrecRel.comp nat_lt hf hg

end nat

/-! ## Lists and vectors -/

section list

variable {f : α → β} {l m : α → List β}

lemma list_cons' (hf : Primrec f) (hl : Primrec l) : Primrec fun a ↦ f a :: l a :=
  list_cons.comp hf hl

lemma list_append' (hl : Primrec l) (hm : Primrec m) : Primrec fun a ↦ l a ++ m a :=
  list_append.comp hl hm

lemma list_length' (hl : Primrec l) : Primrec fun a ↦ (l a).length := list_length.comp hl

lemma list_getD' (d : β) {n : α → ℕ} (hl : Primrec l) (hn : Primrec n) :
    Primrec fun a ↦ (l a).getD (n a) d :=
  (list_getD d).comp hl hn

lemma list_getElem?' {n : α → ℕ} (hl : Primrec l) (hn : Primrec n) :
    Primrec fun a ↦ (l a)[n a]? :=
  list_getElem?.comp hl hn

lemma vector_cons' {n : ℕ} {v : α → List.Vector β n} (hf : Primrec f) (hv : Primrec v) :
    Primrec fun a ↦ f a ::ᵥ v a :=
  vector_cons.comp hf hv

lemma vector_toList' {n : ℕ} {v : α → List.Vector β n} (hv : Primrec v) :
    Primrec fun a ↦ (v a).toList :=
  vector_toList.comp hv

-- `vector_get'` is taken upstream.
lemma vector_get'' {n : ℕ} {v : α → List.Vector β n} {i : α → Fin n} (hv : Primrec v)
    (hi : Primrec i) : Primrec fun a ↦ (v a).get (i a) :=
  vector_get.comp hv hi

end list

/-! ## Equality -/

lemma eq' {f g : α → β} (hf : Primrec f) (hg : Primrec g) :
    PrimrecPred fun a ↦ f a = g a :=
  PrimrecRel.comp Primrec.eq hf hg

/-! ## Encodings -/

section encodable

open Encodable

variable {f : α → β} {n : α → ℕ}

lemma encode' (hf : Primrec f) : Primrec fun a ↦ encode (f a) := Primrec.encode.comp hf

lemma decode' (hn : Primrec n) : Primrec fun a ↦ (decode (n a) : Option β) :=
  Primrec.decode.comp hn

lemma decode₂' (hn : Primrec n) : Primrec fun a ↦ decode₂ β (n a) := Primrec.decode₂.comp hn

lemma encdec' (hn : Primrec n) : Primrec fun a ↦ encode (decode (n a) : Option β) :=
  encdec.comp hn

lemma option_some' (hf : Primrec f) : Primrec fun a ↦ some (f a) := option_some.comp hf

lemma option_isSome' {o : α → Option β} (ho : Primrec o) : Primrec fun a ↦ (o a).isSome :=
  option_isSome.comp ho

lemma option_getD' {o : α → Option β} (ho : Primrec o) (hf : Primrec f) :
    Primrec fun a ↦ (o a).getD (f a) :=
  option_getD.comp ho hf

end encodable

end Primrec

/-! ## Predicates -/

namespace PrimrecPred

variable {p q : α → Prop}

lemma imp (hp : PrimrecPred p) (hq : PrimrecPred q) : PrimrecPred fun a ↦ p a → q a :=
  (hp.not.or hq).of_eq fun _ ↦ by simp [imp_iff_not_or]

lemma iff (hp : PrimrecPred p) (hq : PrimrecPred q) : PrimrecPred fun a ↦ (p a ↔ q a) :=
  ((hp.imp hq).and (hq.imp hp)).of_eq fun _ ↦ by simp [iff_iff_implies_and_implies]

lemma const (p : Prop) : PrimrecPred fun _ : α ↦ p := by
  classical
  exact Primrec.primrecPred (Primrec.const (decide p))

end PrimrecPred

/-! ## Bounded quantifiers

Mathlib's `PrimrecRel.exists_lt` and `forall_lt` fix the parameter at `ℕ`.
-/

section quantifier

variable {R : ℕ → β → Prop}

lemma PrimrecRel.exists_lt' (h : PrimrecRel R) : PrimrecRel fun n y ↦ ∃ x < n, R x y :=
  (PrimrecRel.exists_mem_list h |>.comp (Primrec.list_range.comp .fst) .snd).of_eq (by simp)

lemma PrimrecRel.forall_lt' (h : PrimrecRel R) : PrimrecRel fun n y ↦ ∀ x < n, R x y :=
  (PrimrecRel.forall_mem_list h |>.comp (Primrec.list_range.comp .fst) .snd).of_eq (by simp)

end quantifier

section pointwiseQuantifier

variable {n : α → ℕ} {R : α → ℕ → Prop}

lemma PrimrecPred.exists_lt' (hn : Primrec n) (hR : PrimrecRel R) :
    PrimrecPred fun a ↦ ∃ x < n a, R a x := by
  have h : PrimrecRel fun (m : ℕ) (a : α) ↦ ∃ x < m, R a x := PrimrecRel.exists_lt' hR.swap;
  exact PrimrecRel.comp h hn Primrec.id

lemma PrimrecPred.forall_lt' (hn : Primrec n) (hR : PrimrecRel R) :
    PrimrecPred fun a ↦ ∀ x < n a, R a x := by
  have h : PrimrecRel fun (m : ℕ) (a : α) ↦ ∀ x < m, R a x := PrimrecRel.forall_lt' hR.swap;
  exact PrimrecRel.comp h hn Primrec.id

end pointwiseQuantifier

lemma PrimrecRel.mk {r : α → β → Prop} (h : PrimrecPred fun p : α × β ↦ r p.1 p.2) :
    PrimrecRel r := h

/-! ## The rule set

Rules match at `reducible` transparency: at default, a failed match unfolds `Nat.unpair` and
`Nat.sqrt`, which costs minutes.
-/

attribute [aesop (rule_sets := [Primrec]) norm] Function.comp_def

-- Point-free forms too: `Primrec fun l ↦ l.length` is eta-reduced before indexing.
attribute [aesop 1 (rule_sets := [Primrec]) safe apply (transparency := reducible)]
  Primrec.id' Primrec.id Primrec.const Primrec₂.const
  Primrec.fst Primrec.snd Primrec.succ Primrec.pred Primrec.unpair
  Primrec.list_length Primrec.list_range Primrec.list_reverse Primrec.vector_toList
  Primrec.vector_ofFn'
  Primrec.encode Primrec.decode Primrec.decode₂ Primrec.encdec Primrec.option_some
  Primrec.option_isSome

attribute [aesop 2 (rule_sets := [Primrec]) safe apply (transparency := reducible)]
  Primrec.fst' Primrec.snd'
  Primrec.succ' Primrec.nat_add' Primrec.nat_sub' Primrec.nat_mul' Primrec.nat_div'
  Primrec.nat_mod' Primrec.nat_max' Primrec.nat_min' Primrec.nat_pair' Primrec.unpair'
  Primrec.nat_pow'
  Primrec.nat_le' Primrec.nat_lt'
  Primrec.list_cons' Primrec.list_append' Primrec.list_length' Primrec.list_getD'
  Primrec.list_getElem?' Primrec.eq' Primrec.vector_cons' Primrec.vector_toList'
  Primrec.vector_get'' Primrec.vector_ofFn
  Primrec.encode' Primrec.decode' Primrec.decode₂' Primrec.encdec' Primrec.option_some'
  Primrec.option_isSome' Primrec.option_getD'

attribute [aesop 3 (rule_sets := [Primrec]) safe apply (transparency := reducible)]
  PrimrecPred.not PrimrecPred.and PrimrecPred.or PrimrecPred.imp PrimrecPred.iff
  Primrec.ite Primrec.cond Primrec.nat_rec' Primrec.nat_casesOn Primrec.nat_iterate
  Primrec.option_casesOn Primrec.option_map Primrec.option_bind Primrec.list_map
  Primrec.list_foldl Primrec.list_foldr Primrec.list_rec

attribute [aesop 10 (rule_sets := [Primrec]) safe apply (transparency := reducible)]
  PrimrecPred.exists_lt' PrimrecPred.forall_lt' PrimrecPred.const

-- After `@[primrec]` (penalty 10): uncurrying a goal such a lemma closes makes the search loop.
attribute [aesop 20 (rule_sets := [Primrec]) safe apply (transparency := reducible)]
  Primrec₂.mk PrimrecRel.mk

-- Unsafe: by structure eta it matches projections too, and loops.
attribute [aesop 50% (rule_sets := [Primrec]) unsafe apply (transparency := reducible)]
  Primrec.pair

attribute [aesop 20% (rule_sets := [Primrec]) unsafe apply (transparency := reducible)]
  Primrec.comp Primrec₂.comp PrimrecPred.comp PrimrecRel.comp

section examples

variable {k : ℕ} {F : α → ℕ → ℕ} {f g : List ℕ → ℕ → ℕ}

example : Primrec fun p : α × ℕ × ℕ ↦ p.2.1 := by primrec

example : Primrec fun p : ℕ × ℕ ↦ max p.1 (p.2 + 1) := by primrec

example : PrimrecRel fun (b : ℕ) (l : List ℕ) ↦ b < l.length := by primrec

example : Primrec₂ fun a b : ℕ ↦ if a = 1 then b else a := by primrec

example : Primrec fun m : ℕ ↦
    Nat.pair (Nat.unpair (Nat.unpair ((Nat.unpair m).1 - 1)).2).2
      (Nat.unpair (Nat.unpair ((Nat.unpair m).2 - 1)).2).2 := by primrec

example {u v : ℕ → ℕ} (hu : Primrec u) (hv : Primrec v) : Primrec fun a ↦ (u a, v a) := by primrec

example (hF : Primrec₂ F) : Primrec₂ fun (a : α) (q : ℕ × ℕ) ↦ max (F a q.1) q.2 := by primrec

example (hf : Primrec₂ f) : Primrec₂ fun (l : List ℕ) (b : ℕ) ↦ f (b :: l) (b + 1) := by primrec

example (hf : Primrec₂ f) (hg : Primrec₂ g) :
    Primrec₂ fun (l : List ℕ) (b : ℕ) ↦
      max (max (f l b) (g l (max b (f l b)))) (max (g l b) (f l (max b (g l b)))) := by primrec

example (hg : Primrec₂ g) : Primrec fun w : List.Vector ℕ k ↦ g w.toList 0 := by primrec

example : Primrec fun p : ℕ × ℕ ↦ (p.1 ::ᵥ p.2 ::ᵥ List.Vector.nil : List.Vector ℕ 2) := by
  primrec

example : Primrec fun w : List.Vector ℕ 2 ↦ w.get 0 + w.get 1 := by primrec

example {p : ℕ → ℕ → Prop} (hp : PrimrecRel p) :
    PrimrecPred fun a : ℕ ↦ ∀ x < a + 1, ∃ y < x, p x y := by primrec

end examples

end
