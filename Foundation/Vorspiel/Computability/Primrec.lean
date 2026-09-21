module

public import Foundation.Vorspiel.Tactic.Primrec
public import Mathlib.Computability.Primrec.List

/-!
# The rules of the `primrec` tactic

A rule of the `Primrec` rule set reads a goal `Primrec fun a ↦ e`, peels one application off `e`
and leaves `Primrec` goals for the arguments; the leaves are `fun a ↦ a`, the constants, and
whatever the context provides. The lemmas are therefore stated in the pointwise form
`Primrec fun a ↦ F (f a) (g a)` rather than Mathlib's point-free `Primrec₂ F`: it is the head
symbol `F` of the pointwise form that lets the discrimination tree key the rule.

This module states those forms for the combinators of `Mathlib.Computability.Primrec` and
populates the rule set with them. The tactic itself is `Foundation/Vorspiel/Tactic/Primrec.lean`,
and `@[primrec]` adds a lemma stated anywhere else.

Everything here is a pointwise restatement of a Mathlib combinator, so there is no informal
source to cite.
-/

@[expose] public section

variable {α β γ δ σ : Type*} [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable δ]
  [Primcodable σ]

namespace Primrec

/-! ## The leaves -/

variable (α) in
theorem id' : Primrec fun a : α ↦ a := Primrec.id

/-! ## Products -/

theorem fst' {f : α → β × γ} (hf : Primrec f) : Primrec fun a ↦ (f a).1 := fst.comp hf

theorem snd' {f : α → β × γ} (hf : Primrec f) : Primrec fun a ↦ (f a).2 := snd.comp hf

/-! ## Arithmetic -/

section nat

variable {f g : α → ℕ}

theorem succ' (hf : Primrec f) : Primrec fun a ↦ (f a).succ := succ.comp hf

theorem nat_add' (hf : Primrec f) (hg : Primrec g) : Primrec fun a ↦ f a + g a :=
  nat_add.comp hf hg

theorem nat_sub' (hf : Primrec f) (hg : Primrec g) : Primrec fun a ↦ f a - g a :=
  nat_sub.comp hf hg

theorem nat_mul' (hf : Primrec f) (hg : Primrec g) : Primrec fun a ↦ f a * g a :=
  nat_mul.comp hf hg

theorem nat_div' (hf : Primrec f) (hg : Primrec g) : Primrec fun a ↦ f a / g a :=
  nat_div.comp hf hg

theorem nat_mod' (hf : Primrec f) (hg : Primrec g) : Primrec fun a ↦ f a % g a :=
  nat_mod.comp hf hg

theorem nat_max' (hf : Primrec f) (hg : Primrec g) : Primrec fun a ↦ max (f a) (g a) :=
  nat_max.comp hf hg

theorem nat_min' (hf : Primrec f) (hg : Primrec g) : Primrec fun a ↦ min (f a) (g a) :=
  nat_min.comp hf hg

theorem nat_pair' (hf : Primrec f) (hg : Primrec g) : Primrec fun a ↦ (f a).pair (g a) :=
  Primrec₂.natPair.comp hf hg

theorem unpair' (hf : Primrec f) : Primrec fun a ↦ (f a).unpair := unpair.comp hf

theorem nat_pow' (hf : Primrec f) (hg : Primrec g) : Primrec fun a ↦ f a ^ g a :=
  (Primrec₂.unpaired'.1 Nat.Primrec.pow).comp hf hg

theorem nat_le' (hf : Primrec f) (hg : Primrec g) : PrimrecPred fun a ↦ f a ≤ g a :=
  PrimrecRel.comp nat_le hf hg

theorem nat_lt' (hf : Primrec f) (hg : Primrec g) : PrimrecPred fun a ↦ f a < g a :=
  PrimrecRel.comp nat_lt hf hg

end nat

/-! ## Lists and vectors -/

section list

variable {f : α → β} {l m : α → List β}

theorem list_cons' (hf : Primrec f) (hl : Primrec l) : Primrec fun a ↦ f a :: l a :=
  list_cons.comp hf hl

theorem list_append' (hl : Primrec l) (hm : Primrec m) : Primrec fun a ↦ l a ++ m a :=
  list_append.comp hl hm

theorem list_length' (hl : Primrec l) : Primrec fun a ↦ (l a).length := list_length.comp hl

theorem list_getD' (d : β) {n : α → ℕ} (hl : Primrec l) (hn : Primrec n) :
    Primrec fun a ↦ (l a).getD (n a) d :=
  (list_getD d).comp hl hn

theorem list_getElem?' {n : α → ℕ} (hl : Primrec l) (hn : Primrec n) :
    Primrec fun a ↦ (l a)[n a]? :=
  list_getElem?.comp hl hn

theorem vector_cons' {n : ℕ} {v : α → List.Vector β n} (hf : Primrec f) (hv : Primrec v) :
    Primrec fun a ↦ f a ::ᵥ v a :=
  vector_cons.comp hf hv

theorem vector_toList' {n : ℕ} {v : α → List.Vector β n} (hv : Primrec v) :
    Primrec fun a ↦ (v a).toList :=
  vector_toList.comp hv

/-- The pointwise form of `Primrec.vector_get`. It carries a second prime because `vector_get'`
upstream is the point-free `Primrec (List.Vector.get ·)`. -/
theorem vector_get'' {n : ℕ} {v : α → List.Vector β n} {i : α → Fin n} (hv : Primrec v)
    (hi : Primrec i) : Primrec fun a ↦ (v a).get (i a) :=
  vector_get.comp hv hi

end list

/-! ## Equality -/

theorem eq' {f g : α → β} (hf : Primrec f) (hg : Primrec g) :
    PrimrecPred fun a ↦ f a = g a :=
  PrimrecRel.comp Primrec.eq hf hg

/-! ## Encodings -/

section encodable

open Encodable

variable {f : α → β} {n : α → ℕ}

theorem encode' (hf : Primrec f) : Primrec fun a ↦ encode (f a) := Primrec.encode.comp hf

theorem decode' (hn : Primrec n) : Primrec fun a ↦ (decode (n a) : Option β) :=
  Primrec.decode.comp hn

theorem decode₂' (hn : Primrec n) : Primrec fun a ↦ decode₂ β (n a) := Primrec.decode₂.comp hn

theorem encdec' (hn : Primrec n) : Primrec fun a ↦ encode (decode (n a) : Option β) :=
  encdec.comp hn

theorem option_some' (hf : Primrec f) : Primrec fun a ↦ some (f a) := option_some.comp hf

theorem option_isSome' {o : α → Option β} (ho : Primrec o) : Primrec fun a ↦ (o a).isSome :=
  option_isSome.comp ho

theorem option_getD' {o : α → Option β} (ho : Primrec o) (hf : Primrec f) :
    Primrec fun a ↦ (o a).getD (f a) :=
  option_getD.comp ho hf

end encodable

end Primrec

/-! ## Predicates -/

namespace PrimrecPred

variable {p q : α → Prop}

theorem imp (hp : PrimrecPred p) (hq : PrimrecPred q) : PrimrecPred fun a ↦ p a → q a :=
  (hp.not.or hq).of_eq fun _ ↦ by simp [imp_iff_not_or]

theorem iff (hp : PrimrecPred p) (hq : PrimrecPred q) : PrimrecPred fun a ↦ (p a ↔ q a) :=
  ((hp.imp hq).and (hq.imp hp)).of_eq fun _ ↦ by simp [iff_iff_implies_and_implies]

theorem const (p : Prop) : PrimrecPred fun _ : α ↦ p := by
  classical
  exact Primrec.primrecPred (Primrec.const (decide p))

end PrimrecPred

/-! ## Bounded quantifiers

Mathlib's `PrimrecRel.exists_lt` and `PrimrecRel.forall_lt` fix both arguments at `ℕ` and leave
the bound as the relation's own argument. The tactic needs the bound to be an arbitrary
primitive recursive function of the ambient variable, and the parameter to range over any
`Primcodable` type.
-/

section quantifier

variable {R : ℕ → β → Prop}

/-- `PrimrecRel.exists_lt`, with the parameter of the relation in any `Primcodable` type. -/
theorem PrimrecRel.exists_lt' (h : PrimrecRel R) : PrimrecRel fun n y ↦ ∃ x < n, R x y :=
  (PrimrecRel.exists_mem_list h |>.comp (Primrec.list_range.comp .fst) .snd).of_eq (by simp)

/-- `PrimrecRel.forall_lt`, with the parameter of the relation in any `Primcodable` type. -/
theorem PrimrecRel.forall_lt' (h : PrimrecRel R) : PrimrecRel fun n y ↦ ∀ x < n, R x y :=
  (PrimrecRel.forall_mem_list h |>.comp (Primrec.list_range.comp .fst) .snd).of_eq (by simp)

end quantifier

section pointwiseQuantifier

variable {n : α → ℕ} {R : α → ℕ → Prop}

/-- A bounded existential whose bound is itself primitive recursive. -/
theorem PrimrecPred.exists_lt' (hn : Primrec n) (hR : PrimrecRel R) :
    PrimrecPred fun a ↦ ∃ x < n a, R a x := by
  have h : PrimrecRel fun (m : ℕ) (a : α) ↦ ∃ x < m, R a x := PrimrecRel.exists_lt' hR.swap;
  exact PrimrecRel.comp h hn Primrec.id

/-- A bounded universal whose bound is itself primitive recursive. -/
theorem PrimrecPred.forall_lt' (hn : Primrec n) (hR : PrimrecRel R) :
    PrimrecPred fun a ↦ ∀ x < n a, R a x := by
  have h : PrimrecRel fun (m : ℕ) (a : α) ↦ ∀ x < m, R a x := PrimrecRel.forall_lt' hR.swap;
  exact PrimrecRel.comp h hn Primrec.id

end pointwiseQuantifier

/-- A `PrimrecRel` goal becomes a `PrimrecPred` goal in one variable, the form the rules of the
set are stated in. -/
theorem PrimrecRel.mk {r : α → β → Prop} (h : PrimrecPred fun p : α × β ↦ r p.1 p.2) :
    PrimrecRel r := h

/-! ## The rule set

Every rule matches at `reducible` transparency. A goal here is a lambda over arithmetic, and
unifying its body against a rule that does not fit sends the default-transparency unifier deep
into the definitions of `Nat.unpair`, `Nat.sqrt` and their like before it gives up; with
`reducible` the same failure is immediate.

Priorities go from the leaves upwards: a rule that closes a goal outright is tried before one
that peels an application off, and the rules whose conclusions match every goal come last.
-/

attribute [aesop (rule_sets := [Primrec]) norm] Function.comp_def

-- Lean eta-reduces a goal such as `Primrec fun l ↦ l.length` to `Primrec List.length` before
-- indexing it, and the pointwise rules, whose conclusions are lambdas, are then not retrieved.
-- Mathlib's point-free lemmas cover exactly those goals, so the leaves carry both forms.
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

-- The rules whose conclusion is a quantified or constant predicate: their bodies are not headed
-- by a function symbol, so they are keyed no better than a `@[primrec]` lemma and share its
-- penalty.
attribute [aesop 10 (rule_sets := [Primrec]) safe apply (transparency := reducible)]
  PrimrecPred.exists_lt' PrimrecPred.forall_lt' PrimrecPred.const

-- A `Primrec₂` or `PrimrecRel` goal becomes a goal in one variable, the form every rule of the
-- set is stated in. This comes after the rules a `@[primrec]` lemma carries (penalty 10): a goal
-- `Primrec₂ f` that such a lemma closes outright must not be uncurried first, or the composition
-- rules will curry it straight back and the search will not terminate.
attribute [aesop 20 (rule_sets := [Primrec]) safe apply (transparency := reducible)]
  Primrec₂.mk PrimrecRel.mk

-- Lean's eta for structures makes `Primrec.pair` match every goal whose value is a pair, a
-- projection `fun a ↦ (f a).2` included, and following it there splits the goal into its two
-- components and reassembles them, forever. The rule is therefore unsafe: Aesop reaches for it
-- only once the keyed rules have failed, and backs out of it when it leads nowhere.
attribute [aesop 50% (rule_sets := [Primrec]) unsafe apply (transparency := reducible)]
  Primrec.pair

-- The generic composition rules. Their conclusions are headed by a metavariable, so they match
-- every goal; a goal needs them to reach the hypotheses `Primrec f` and `Primrec₂ f` of the
-- context and the point-free lemmas of the rule set.
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
