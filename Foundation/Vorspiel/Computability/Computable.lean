module

public import Foundation.Vorspiel.Computability.Primrec
public import Foundation.Vorspiel.Tactic.Computable
public import Mathlib.Computability.Partrec

/-!
# The rules of the `computable` tactic

Primitive recursive subterms are left to the `Primrec` rules, reached through `Primrec.to_comp`.
These rules cover the shapes where a computable but not primitive recursive argument can sit.
-/

@[expose] public section

open Encodable

variable {α β γ σ : Type*} [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

namespace Computable

/-! ## The leaves -/

variable (α) in
lemma id' : Computable fun a : α ↦ a := Computable.id

/-! ## Products -/

lemma fst' {f : α → β × γ} (hf : Computable f) : Computable fun a ↦ (f a).1 := fst.comp hf

lemma snd' {f : α → β × γ} (hf : Computable f) : Computable fun a ↦ (f a).2 := snd.comp hf

/-! ## Arithmetic -/

section nat

variable {f g : α → ℕ}

lemma succ' (hf : Computable f) : Computable fun a ↦ (f a).succ := succ.comp hf

lemma pred' (hf : Computable f) : Computable fun a ↦ (f a).pred := pred.comp hf

lemma nat_add' (hf : Computable f) (hg : Computable g) : Computable fun a ↦ f a + g a :=
  Primrec.nat_add.to_comp.comp hf hg

lemma nat_sub' (hf : Computable f) (hg : Computable g) : Computable fun a ↦ f a - g a :=
  Primrec.nat_sub.to_comp.comp hf hg

lemma nat_mul' (hf : Computable f) (hg : Computable g) : Computable fun a ↦ f a * g a :=
  Primrec.nat_mul.to_comp.comp hf hg

lemma nat_max' (hf : Computable f) (hg : Computable g) : Computable fun a ↦ max (f a) (g a) :=
  Primrec.nat_max.to_comp.comp hf hg

lemma nat_min' (hf : Computable f) (hg : Computable g) : Computable fun a ↦ min (f a) (g a) :=
  Primrec.nat_min.to_comp.comp hf hg

lemma nat_pair' (hf : Computable f) (hg : Computable g) : Computable fun a ↦ (f a).pair (g a) :=
  Primrec₂.natPair.to_comp.comp hf hg

lemma unpair' (hf : Computable f) : Computable fun a ↦ (f a).unpair := unpair.comp hf

end nat

/-! ## Lists and vectors -/

section list

variable {f : α → β} {l m : α → List β}

lemma list_cons' (hf : Computable f) (hl : Computable l) : Computable fun a ↦ f a :: l a :=
  list_cons.comp hf hl

lemma list_append' (hl : Computable l) (hm : Computable m) : Computable fun a ↦ l a ++ m a :=
  list_append.comp hl hm

lemma list_length' (hl : Computable l) : Computable fun a ↦ (l a).length := list_length.comp hl

lemma list_getElem?' {n : α → ℕ} (hl : Computable l) (hn : Computable n) :
    Computable fun a ↦ (l a)[n a]? :=
  list_getElem?.comp hl hn

lemma vector_cons' {n : ℕ} {v : α → List.Vector β n} (hf : Computable f) (hv : Computable v) :
    Computable fun a ↦ f a ::ᵥ v a :=
  vector_cons.comp hf hv

lemma vector_toList' {n : ℕ} {v : α → List.Vector β n} (hv : Computable v) :
    Computable fun a ↦ (v a).toList :=
  vector_toList.comp hv

-- `vector_get'` is taken upstream.
lemma vector_get'' {n : ℕ} {v : α → List.Vector β n} {i : α → Fin n} (hv : Computable v)
    (hi : Computable i) : Computable fun a ↦ (v a).get (i a) :=
  vector_get.comp hv hi

end list

/-! ## Encodings -/

section encodable

variable {f : α → β} {n : α → ℕ}

lemma encode' (hf : Computable f) : Computable fun a ↦ encode (f a) := Computable.encode.comp hf

lemma decode' (hn : Computable n) : Computable fun a ↦ (decode (n a) : Option β) :=
  Computable.decode.comp hn

lemma option_some' (hf : Computable f) : Computable fun a ↦ some (f a) := option_some.comp hf

lemma option_getD' {o : α → Option β} (ho : Computable o) (hf : Computable f) :
    Computable fun a ↦ (o a).getD (f a) :=
  option_getD ho hf

end encodable

end Computable

/-! ## The rule set

Priorities mirror those in `Foundation/Vorspiel/Computability/Primrec.lean`.
-/

attribute [aesop (rule_sets := [Computable]) norm] Function.comp_def

attribute [aesop 1 (rule_sets := [Computable]) safe apply (transparency := reducible)]
  Computable.id' Computable.id Computable.const
  Computable.fst Computable.snd Computable.succ Computable.pred Computable.unpair
  Computable.list_length Computable.list_reverse Computable.vector_toList Computable.vector_ofFn'
  Computable.vector_head Computable.vector_tail
  Computable.encode Computable.decode Computable.option_some

attribute [aesop 2 (rule_sets := [Computable]) safe apply (transparency := reducible)]
  Computable.fst' Computable.snd'
  Computable.succ' Computable.pred' Computable.nat_add' Computable.nat_sub' Computable.nat_mul'
  Computable.nat_max' Computable.nat_min' Computable.nat_pair' Computable.unpair'
  Computable.list_cons' Computable.list_append' Computable.list_length'
  Computable.list_getElem?' Computable.vector_cons' Computable.vector_toList'
  Computable.vector_get'' Computable.vector_ofFn
  Computable.encode' Computable.decode' Computable.option_some' Computable.option_getD'

attribute [aesop 3 (rule_sets := [Computable]) safe apply (transparency := reducible)]
  Computable.cond Computable.nat_rec Computable.nat_casesOn
  Computable.option_casesOn Computable.option_map Computable.option_bind Computable.sumCasesOn

attribute [aesop 20 (rule_sets := [Computable]) safe apply (transparency := reducible)]
  Computable₂.mk

-- Unsafe: by structure eta it matches projections too, and loops.
attribute [aesop 50% (rule_sets := [Computable]) unsafe apply (transparency := reducible)]
  Computable.pair

-- Unsafe: a computable function need not be primitive recursive.
attribute [aesop 40% (rule_sets := [Computable]) unsafe apply (transparency := reducible)]
  Primrec.to_comp Primrec₂.to_comp

attribute [aesop 20% (rule_sets := [Computable]) unsafe apply (transparency := reducible)]
  Computable.comp Computable₂.comp

section examples

variable {F : ℕ → ℕ} {G : ℕ → ℕ → ℕ}

example : Computable fun v : List.Vector ℕ 2 ↦ (v.get 0, v.get 1) := by computable

example : Computable fun v : List.Vector ℕ 1 ↦ v.get 0 := by computable

example : Computable fun p : ℕ × ℕ ↦ (p.2 ::ᵥ p.1 ::ᵥ List.Vector.nil : List.Vector ℕ 2) := by
  computable

example (hF : Computable F) : Computable fun a : ℕ ↦ Nat.pair (F a) (encode a) := by computable

example (hF : Computable F) : Computable fun p : ℕ × ℕ ↦ max (F p.1) (p.2 + 1) := by computable

example (hG : Computable₂ G) : Computable₂ fun a b : ℕ ↦ G b (a + 1) := by computable

example (hF : Computable F) : Computable fun a : ℕ ↦ (decode (F a) : Option ℕ) := by computable

example : Computable fun m : ℕ ↦ Nat.pair (Nat.unpair (m - 1)).2 m := by computable

end examples

end
