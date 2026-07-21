module

public import Foundation.FirstOrder.Basic.Coding
public import Mathlib.Computability.Primrec.List

@[expose] public section
/-!
# Groundwork for `Primcodable` on syntax (issue #506)

`Semiterm.ofNat`/`Semiformula.ofNat` are strong recursions on the code: the `func` branch reads an
argument vector out of the code and calls itself on each entry, each of which is smaller. Turning
them into `Primrec` therefore goes through `Primrec.nat_strong_rec`, whose step function is handed
the table of all previously computed values. This file is the layer that step function is built
from.

Two design points are worth stating, because they are what make the rest routine.

**Everything happens at the level of codes.** The table entry for a sub-code `j` is
`encode (ofNat n j)`, and `encode` on `Option` is `0` for `none` and `encode t + 1` for `some t`.
So a successful entry already *contains* the argument's `toNat`, one less than itself, and the
argument-vector code can be rebuilt by arithmetic alone. No term is ever reconstructed, and none of
this needs `L` or `ξ` decidable.

**`Option` is kept out of the fold.** `stepVec` returns `ℕ` with `0` meaning failure and `r + 1`
meaning success with value `r`, rather than `Option ℕ`. This is not cosmetic: with `Option ℕ` as the
fold's accumulator the `Primrec` combinators must synthesise `Primcodable` for towers of products
ending in `Option ℕ`, and elaboration diverges. The `ℕ` encoding costs one `- 1` per lookup and
elaborates immediately.

The list bridges are here for the same reason: `Nat.natToVec` produces a `Fin k → ℕ` whose length
lives in its type, which no `Primrec` combinator can consume. `Nat.natToList` is the same decoding
without the dependency, and `natToVec_eq_some_iff` is what lets the correctness proof move between
them.
-/

namespace Nat

/-- List form of `Matrix.vecToNat`. -/
def listToNat : List ℕ → ℕ
  | [] => 0
  | a :: l => Nat.pair a (listToNat l) + 1

/-- List form of `Nat.natToVec`: the same decoding, with the length out of the type. -/
def natToList : ℕ → List ℕ
  | 0 => []
  | e + 1 => e.unpair.1 :: natToList e.unpair.2
  decreasing_by exact Nat.lt_succ_of_le (Nat.unpair_right_le e)

lemma listToNat_ofFn {n : ℕ} (v : Fin n → ℕ) : listToNat (List.ofFn v) = Matrix.vecToNat v := by
  induction n with
  | zero => simp [listToNat, Matrix.vecToNat]
  | succ n ih =>
    rw [List.ofFn_succ, listToNat, ih]
    simpa using (Matrix.encode_succ (v 0) (fun i ↦ v i.succ)).symm

lemma natToVec_eq_some_iff {e k : ℕ} {v : Fin k → ℕ} :
    e.natToVec k = some v ↔ natToList e = List.ofFn v := by
  induction k generalizing e with
  | zero =>
    cases e with
    | zero => simp [natToVec, natToList, Matrix.empty_eq]
    | succ e => simp [natToVec, natToList]
  | succ k ih =>
    cases e with
    | zero => simp [natToVec, natToList]
    | succ e =>
      rw [natToVec, natToList, List.ofFn_succ]
      constructor
      · rintro h
        rw [Option.map_eq_some_iff] at h
        obtain ⟨w, hw, rfl⟩ := h
        rw [ih.mp hw]
        simp
      · rintro h
        rw [List.cons.injEq] at h
        obtain ⟨h0, hl⟩ := h
        refine Option.map_eq_some_iff.mpr ⟨fun i ↦ v i.succ, ih.mpr hl, ?_⟩
        exact funext fun i ↦ i.cases (by simp [h0]) (by simp)

/-- The shape the correctness proof tests: `natToVec` succeeds exactly when the undependent
decoding has the expected length. -/
lemma natToVec_eq_none_of_length {e k : ℕ} (h : (natToList e).length ≠ k) :
    e.natToVec k = none := by
  rcases hv : e.natToVec k with _ | v
  · rfl
  · exact absurd (by rw [natToVec_eq_some_iff.mp hv]; simp) h

lemma natToVec_isSome_of_length {e k : ℕ} (h : (natToList e).length = k) :
    ∃ v : Fin k → ℕ, e.natToVec k = some v := by
  subst h
  refine ⟨fun i ↦ (natToList e).get i, natToVec_eq_some_iff.mpr ?_⟩
  exact (List.ofFn_get _).symm

end Nat

section
open Primrec

theorem Primrec.nat_natToList : Primrec Nat.natToList := by
  have step : Primrec₂ fun (_ : Unit) (l : List (List ℕ)) ↦
      (Nat.casesOn l.length (some []) fun e ↦
        (l[e.unpair.2]?).map fun t ↦ e.unpair.1 :: t : Option (List ℕ)) :=
    Primrec.to₂ <| Primrec.nat_casesOn
      (list_length.comp <| snd.comp .id)
      (const (some ([] : List ℕ)))
      (Primrec.to₂ <| option_map
        (list_getElem?.comp (snd.comp fst) (snd.comp <| Primrec.unpair.comp snd))
        (Primrec.to₂ <| list_cons.comp
          (fst.comp <| Primrec.unpair.comp <| snd.comp fst) snd))
  have main : Primrec₂ fun (_ : Unit) (n : ℕ) ↦ Nat.natToList n := by
    refine Primrec.nat_strong_rec _ step ?_
    rintro ⟨⟩ (_ | e)
    · simp [Nat.natToList]
    · have hlen : ((List.range (e + 1)).map Nat.natToList).length = e + 1 := by simp
      have hlt : e.unpair.2 < e + 1 := Nat.lt_succ_of_le (Nat.unpair_right_le e)
      simp [hlen, List.getElem?_map, hlt, Nat.natToList]
  simpa using main.comp (const ()) Primrec.id

end

namespace Matrix

/-- The equation lemma that keeps reasoning out of `Option`'s applicative layer: at `Option`,
`getM`'s recursive step is a `bind` of a `map`. -/
lemma getM_option_succ {n : ℕ} {β : Type*} (f : Fin (n + 1) → Option β) :
    Matrix.getM f
      = (f 0).bind fun a ↦ (Matrix.getM fun j ↦ f j.succ).map fun w ↦ Fin.cases a w := by
  rw [Matrix.getM]
  rcases f 0 with _ | a
  · rfl
  · rcases Matrix.getM (fun j ↦ f j.succ) with _ | w <;> rfl

/-- `getM` at `Option` succeeds exactly when every component does. This is what turns the `func`
branch of `ofNat` into a statement about each argument separately. -/
lemma getM_option_eq_some_iff {n : ℕ} {β : Type*} {f : Fin n → Option β} {v : Fin n → β} :
    Matrix.getM f = some v ↔ ∀ i, f i = some (v i) := by
  induction n with
  | zero =>
    refine ⟨fun _ i ↦ i.elim0, fun _ ↦ ?_⟩
    rw [Matrix.getM]
    exact congrArg some (funext fun i ↦ i.elim0)
  | succ n ih =>
    rw [getM_option_succ]
    constructor
    · intro h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨a, ha, hm⟩ := h
      rw [Option.map_eq_some_iff] at hm
      obtain ⟨w, hw, rfl⟩ := hm
      intro i
      exact i.cases (by simpa using ha) (by simpa using ih.mp hw)
    · intro h
      refine Option.bind_eq_some_iff.mpr ⟨v 0, by simpa using h 0, ?_⟩
      refine Option.map_eq_some_iff.mpr
        ⟨fun j ↦ v j.succ, ih.mpr fun j ↦ by simpa using h j.succ, ?_⟩
      exact funext fun i ↦ i.cases (by simp) (by simp)

end Matrix

namespace LO.FirstOrder

open Encodable Nat

/-- Primitive-recursiveness of a language's symbol encodings, **uniformly in the arity**.

This is strictly stronger than `[(k : ℕ) → Primcodable (L.Func k)]`, and the strengthening is
forced rather than convenient: `Semiterm.ofNat` reads the arity `k` *out of the code being
decoded* and then calls `decode : ℕ → Option (L.Func k)` at that `k`. Simulating `ofNat` therefore
needs `(k, e) ↦ encode (decode e : Option (L.Func k))` to be primitive recursive as a function of
the *pair*. A per-arity family gives primitive recursiveness only for each fixed `k`, with no
uniformity across `k`, and no amount of assembling those gives the function of the pair. -/
protected class Language.Primcodable (L : Language) [L.Encodable] where
  func : Primrec₂ fun k e : ℕ ↦ Encodable.encode (Encodable.decode e : Option (L.Func k))
  rel : Primrec₂ fun k e : ℕ ↦ Encodable.encode (Encodable.decode e : Option (L.Rel k))

section

variable (L : Language) [L.Encodable] [L.Primcodable]

instance (k : ℕ) : Primcodable (L.Func k) where
  toEncodable := Language.Encodable.func k
  prim := Primrec.nat_iff.mp <| (Language.Primcodable.func (L := L)).comp
    (Primrec.const k) Primrec.id

instance (k : ℕ) : Primcodable (L.Rel k) where
  toEncodable := Language.Encodable.rel k
  prim := Primrec.nat_iff.mp <| (Language.Primcodable.rel (L := L)).comp
    (Primrec.const k) Primrec.id

example (k : ℕ) : (inferInstance : Primcodable (L.Func k)).toEncodable
    = (inferInstance : Encodable (L.Func k)) := by with_reducible_and_instances rfl

end

/-- `ℒₒᵣ` satisfies the uniform condition: `encode ∘ decode` is
`fun k e ↦ if (k = 0 ∨ k = 2) ∧ e < 2 then e + 1 else 0`. -/
instance : Language.Primcodable ℒₒᵣ where
  func := by
    have h : Primrec fun p : ℕ × ℕ ↦ if (p.1 = 0 ∨ p.1 = 2) ∧ p.2 < 2 then p.2 + 1 else 0 :=
      Primrec.ite
        (PrimrecPred.and
          (PrimrecPred.or
            (Primrec.eq.comp Primrec.fst (Primrec.const 0))
            (Primrec.eq.comp Primrec.fst (Primrec.const 2)))
          (Primrec.nat_lt.comp Primrec.snd (Primrec.const 2)))
        (Primrec.succ.comp Primrec.snd) (Primrec.const 0)
    refine h.of_eq ?_
    rintro ⟨k, e⟩
    match k, e with
    |     0,     0 => rfl
    |     0,     1 => rfl
    |     0, _ + 2 => simp [Encodable.decode]
    |     1,     _ => simp [Encodable.decode]
    |     2,     0 => rfl
    |     2,     1 => rfl
    |     2, _ + 2 => simp [Encodable.decode]
    | _ + 3,     _ => simp [Encodable.decode]
  rel := by
    have h : Primrec fun p : ℕ × ℕ ↦ if p.1 = 2 ∧ p.2 < 2 then p.2 + 1 else 0 :=
      Primrec.ite
        (PrimrecPred.and
          (Primrec.eq.comp Primrec.fst (Primrec.const 2))
          (Primrec.nat_lt.comp Primrec.snd (Primrec.const 2)))
        (Primrec.succ.comp Primrec.snd) (Primrec.const 0)
    refine h.of_eq ?_
    rintro ⟨k, e⟩
    match k, e with
    |     0,     _ => simp [Encodable.decode]
    |     1,     _ => simp [Encodable.decode]
    |     2,     0 => rfl
    |     2,     1 => rfl
    |     2, _ + 2 => simp [Encodable.decode]
    | _ + 3,     _ => simp [Encodable.decode]

namespace Semiterm

/-- The argument-vector fold of the `func` branch. `T` is the table of values already computed by
the strong recursion, `l` the list of argument codes.

The result is `0` for failure and `r + 1` for success with vector code `r`; see the module
docstring for why this is `ℕ` and not `Option ℕ`. A lookup that is absent or `0` — that is, an
argument whose own decoding failed — fails the whole fold. -/
def stepVec (T : List ℕ) (l : List ℕ) : ℕ :=
  l.foldr (fun j acc ↦
    if T.getD j 0 = 0 ∨ acc = 0 then 0
    else Nat.pair (T.getD j 0 - 1) (acc - 1) + 2) 1

@[simp] lemma stepVec_nil (T : List ℕ) : stepVec T [] = 1 := rfl

lemma stepVec_cons (T : List ℕ) (j : ℕ) (l : List ℕ) :
    stepVec T (j :: l) =
      if T.getD j 0 = 0 ∨ stepVec T l = 0 then 0
      else Nat.pair (T.getD j 0 - 1) (stepVec T l - 1) + 2 := rfl

/-- Value fact, success: with every lookup present and non-zero the fold rebuilds exactly the
`vecToNat` code of the arguments. -/
lemma stepVec_ofFn {T : List ℕ} {a : ℕ} {w u : Fin a → ℕ}
    (h : ∀ i, T.getD (w i) 0 = u i + 1) :
    stepVec T (List.ofFn w) = Matrix.vecToNat u + 1 := by
  induction a with
  | zero => simp [Matrix.vecToNat]
  | succ a ih =>
    rw [List.ofFn_succ, stepVec_cons,
      ih (w := fun i ↦ w i.succ) (u := fun i ↦ u i.succ) fun i ↦ by simpa using h i.succ,
      h 0, if_neg (by simp)]
    simp only [Nat.add_sub_cancel]
    simpa using (Matrix.encode_succ (u 0) (fun i ↦ u i.succ)).symm

/-- Value fact, failure: one absent-or-zero lookup anywhere kills the fold. -/
lemma stepVec_eq_zero {T : List ℕ} {l : List ℕ} {j : ℕ} (hj : j ∈ l)
    (h : T.getD j 0 = 0) : stepVec T l = 0 := by
  induction l with
  | nil => simp at hj
  | cons b l ih =>
    rw [stepVec_cons]
    rcases List.mem_cons.mp hj with rfl | hj'
    · exact if_pos (Or.inl h)
    · exact if_pos (Or.inr (ih hj'))

open Primrec in
theorem primrec_stepVec : Primrec₂ stepVec := by
  have hp : Primrec fun p : List ℕ × List ℕ ↦
      p.2.foldr (fun j acc ↦
        if p.1.getD j 0 = 0 ∨ acc = 0 then 0
        else Nat.pair (p.1.getD j 0 - 1) (acc - 1) + 2) 1 := by
    refine Primrec.list_foldr (β := ℕ) (σ := ℕ)
      (f := fun p : List ℕ × List ℕ ↦ p.2) (g := fun _ ↦ (1 : ℕ))
      (h := fun p x ↦ if p.1.getD x.1 0 = 0 ∨ x.2 = 0 then 0
        else Nat.pair (p.1.getD x.1 0 - 1) (x.2 - 1) + 2)
      snd (const _) ?_
    have hget : Primrec fun y : (List ℕ × List ℕ) × ℕ × ℕ ↦ y.1.1.getD y.2.1 0 :=
      (Primrec.list_getD 0).comp (fst.comp fst) (fst.comp snd)
    refine Primrec.ite (PrimrecPred.or (Primrec.eq.comp hget (const 0))
      (Primrec.eq.comp (snd.comp snd) (const 0))) (const 0) ?_
    exact Primrec.nat_add.comp
      (Primrec₂.natPair.comp (nat_sub.comp hget (const 1))
        (nat_sub.comp (snd.comp snd) (const 1))) (const 2)
  exact hp.of_eq fun p ↦ rfl

variable {L : Language} [L.Encodable] [L.Primcodable] {ξ : Type*} [Primcodable ξ]

/-- The four branches of `Semiterm.ofNat` at the level of codes, with `d + 1` the code being
decoded. Branch `2` is the `func` case: it checks that the argument vector decodes to the recorded
arity, that the function symbol decodes, and that every argument's own decoding succeeded — the
last through `stepVec`, reading the table. -/
def stepBody (n : ℕ) (T : List ℕ) (d : ℕ) : ℕ :=
    if d.unpair.1 = 0 then
      (if d.unpair.2 < n then Nat.pair 0 d.unpair.2 + 2 else 0)
    else if d.unpair.1 = 1 then
      (if (encode (decode d.unpair.2 : Option ξ)) = 0 then 0
        else Nat.pair 1 ((encode (decode d.unpair.2 : Option ξ)) - 1) + 2)
    else if d.unpair.1 = 2 then
      (if (Nat.natToList d.unpair.2.unpair.2.unpair.2).length = d.unpair.2.unpair.1 ∧
          (encode (decode d.unpair.2.unpair.2.unpair.1 :
            Option (L.Func d.unpair.2.unpair.1))) ≠ 0 ∧
          stepVec T (Nat.natToList d.unpair.2.unpair.2.unpair.2) ≠ 0 then
        Nat.pair 2 (Nat.pair d.unpair.2.unpair.1
          (Nat.pair ((encode (decode d.unpair.2.unpair.2.unpair.1 :
            Option (L.Func d.unpair.2.unpair.1))) - 1)
            (stepVec T (Nat.natToList d.unpair.2.unpair.2.unpair.2) - 1))) + 2
        else 0)
    else 0

/-- One step of the course-of-values recursion, at the level of codes: given the table `T` of the
values `encode (ofNat n j)` for every `j < T.length`, it returns `encode (ofNat n T.length)`. -/
def step (n : ℕ) (T : List ℕ) : ℕ :=
  Nat.casesOn (motive := fun _ ↦ ℕ) T.length 0 (stepBody (L := L) (ξ := ξ) n T)

open Primrec in
theorem primrec_step : Primrec₂ (step (L := L) (ξ := ξ)) := by
  set A := (ℕ × List ℕ) × ℕ with hA
  have hn : Primrec fun q : A ↦ q.1.1 := fst.comp fst
  have hT : Primrec fun q : A ↦ q.1.2 := snd.comp fst
  have hd : Primrec fun q : A ↦ q.2 := snd
  have hi : Primrec fun q : A ↦ q.2.unpair.1 := fst.comp (Primrec.unpair.comp hd)
  have hc : Primrec fun q : A ↦ q.2.unpair.2 := snd.comp (Primrec.unpair.comp hd)
  have ha : Primrec fun q : A ↦ q.2.unpair.2.unpair.1 := fst.comp (Primrec.unpair.comp hc)
  have hr : Primrec fun q : A ↦ q.2.unpair.2.unpair.2 := snd.comp (Primrec.unpair.comp hc)
  have hef : Primrec fun q : A ↦ q.2.unpair.2.unpair.2.unpair.1 :=
    fst.comp (Primrec.unpair.comp hr)
  have hev : Primrec fun q : A ↦ q.2.unpair.2.unpair.2.unpair.2 :=
    snd.comp (Primrec.unpair.comp hr)
  have hxi : Primrec fun q : A ↦ (encode (decode q.2.unpair.2 : Option ξ)) :=
    Primrec.nat_iff.mpr (Primcodable.prim ξ) |>.comp hc
  have hF : Primrec fun q : A ↦ (encode (decode q.2.unpair.2.unpair.2.unpair.1 :
      Option (L.Func q.2.unpair.2.unpair.1))) :=
    (Language.Primcodable.func (L := L)).comp ha hef
  have hl : Primrec fun q : A ↦ Nat.natToList q.2.unpair.2.unpair.2.unpair.2 :=
    Primrec.nat_natToList.comp hev
  have hsv : Primrec fun q : A ↦ stepVec q.1.2 (Nat.natToList q.2.unpair.2.unpair.2.unpair.2) :=
    primrec_stepVec.comp hT hl
  -- branch 0
  have b0 : Primrec fun q : A ↦
      (if q.2.unpair.2 < q.1.1 then Nat.pair 0 q.2.unpair.2 + 2 else 0) :=
    Primrec.ite (nat_lt.comp hc hn)
      (Primrec.nat_add.comp (Primrec₂.natPair.comp (const 0) hc) (const 2)) (const 0)
  -- branch 1
  have b1 : Primrec fun q : A ↦
      (if (encode (decode q.2.unpair.2 : Option ξ)) = 0 then 0
        else Nat.pair 1 ((encode (decode q.2.unpair.2 : Option ξ)) - 1) + 2) :=
    Primrec.ite (Primrec.eq.comp hxi (const 0)) (const 0)
      (Primrec.nat_add.comp
        (Primrec₂.natPair.comp (const 1) (nat_sub.comp hxi (const 1))) (const 2))
  -- branch 2
  have b2 : Primrec fun q : A ↦
      (if (Nat.natToList q.2.unpair.2.unpair.2.unpair.2).length = q.2.unpair.2.unpair.1 ∧
          (encode (decode q.2.unpair.2.unpair.2.unpair.1 :
            Option (L.Func q.2.unpair.2.unpair.1))) ≠ 0 ∧
          stepVec q.1.2 (Nat.natToList q.2.unpair.2.unpair.2.unpair.2) ≠ 0 then
        Nat.pair 2 (Nat.pair q.2.unpair.2.unpair.1
          (Nat.pair ((encode (decode q.2.unpair.2.unpair.2.unpair.1 :
            Option (L.Func q.2.unpair.2.unpair.1))) - 1)
            (stepVec q.1.2 (Nat.natToList q.2.unpair.2.unpair.2.unpair.2) - 1))) + 2
        else 0) :=
    Primrec.ite
      (PrimrecPred.and (Primrec.eq.comp (list_length.comp hl) ha)
        (PrimrecPred.and (PrimrecPred.not (Primrec.eq.comp hF (const 0)))
          (PrimrecPred.not (Primrec.eq.comp hsv (const 0)))))
      (Primrec.nat_add.comp
        (Primrec₂.natPair.comp (const 2)
          (Primrec₂.natPair.comp ha
            (Primrec₂.natPair.comp (nat_sub.comp hF (const 1))
              (nat_sub.comp hsv (const 1))))) (const 2))
      (const 0)
  have body : Primrec fun q : A ↦ stepBody (L := L) (ξ := ξ) q.1.1 q.1.2 q.2 :=
    (Primrec.ite (Primrec.eq.comp hi (const 0)) b0
      (Primrec.ite (Primrec.eq.comp hi (const 1)) b1
        (Primrec.ite (Primrec.eq.comp hi (const 2)) b2 (const 0)))).of_eq fun q ↦ rfl
  exact (Primrec.nat_casesOn (f := fun p : ℕ × List ℕ ↦ p.2.length) (g := fun _ ↦ (0 : ℕ))
    (h := fun p d ↦ stepBody (L := L) (ξ := ξ) p.1 p.2 d)
    (list_length.comp snd) (const 0) body).of_eq fun p ↦ rfl

abbrev table (n e : ℕ) : List ℕ :=
  (List.range e).map fun j ↦ encode (ofNat (L := L) (ξ := ξ) n j)

omit [L.Primcodable] in
@[simp] lemma table_length (n e : ℕ) : (table (L := L) (ξ := ξ) n e).length = e := by simp [table]

omit [L.Primcodable] in
lemma table_getD {n e j : ℕ} (h : j < e) :
    (table (L := L) (ξ := ξ) n e).getD j 0 = encode (ofNat (L := L) (ξ := ξ) n j) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]
  rfl

omit [L.Primcodable] in
/-- The correctness of the step function: on the table of all previously computed values it
returns the next one. This is what `Primrec.nat_strong_rec` asks for.

Four branches, matching `ofNat`'s. The two atomic ones are arithmetic. The `func` branch is where
the design pays off: `natToVec` succeeding is tested as `natToList` having the recorded length
(`natToVec_isSome_of_length` and `natToVec_eq_none_of_length` are the two directions), the function
symbol's decoding is read off `encode ∘ decode` being non-zero, and each argument's decoding is
read out of the table — so the branch never reconstructs a term, and the argument-vector code comes
straight from `stepVec_ofFn`. When any argument fails to decode, its table entry is `0` and
`stepVec_eq_zero` collapses the fold, matching `Matrix.getM` returning `none` on the other side. -/
theorem step_table (n e : ℕ) :
    step (L := L) (ξ := ξ) n (table (L := L) (ξ := ξ) n e) = encode (ofNat (L := L) (ξ := ξ) n e) := by
  rw [step, table_length]
  cases e with
  | zero => simp [ofNat]
  | succ d =>
  show stepBody (L := L) (ξ := ξ) n (table (L := L) (ξ := ξ) n (d + 1)) d = _
  rw [stepBody, ofNat]
  by_cases h0 : (Nat.unpair d).1 = 0
  · rw [if_pos h0, h0]
    by_cases hz : (Nat.unpair d).2 < n
    · rw [if_pos hz, dif_pos hz]
      simp [encode_eq_toNat, toNat]
    · rw [if_neg hz, dif_neg hz]
      simp
  by_cases h1 : (Nat.unpair d).1 = 1
  · rw [if_neg h0, if_pos h1, h1]
    rcases hx : (decode (Nat.unpair d).2 : Option ξ) with _ | x
    · simp
    · rw [if_neg (by simp)]
      simp [encode_eq_toNat, toNat]
  by_cases h2 : (Nat.unpair d).1 = 2
  · rw [if_neg h0, if_neg h1, if_pos h2, h2]
    simp only []
    rcases hv : (Nat.unpair (Nat.unpair (Nat.unpair d).2).2).2.natToVec
        (Nat.unpair (Nat.unpair d).2).1 with _ | v'
    · rw [if_neg ?_]
      · simp
      · rintro ⟨hlen, -, -⟩
        obtain ⟨w, hw⟩ := Nat.natToVec_isSome_of_length hlen
        rw [hw] at hv
        exact absurd hv (by simp)
    · have hl : (Nat.unpair (Nat.unpair (Nat.unpair d).2).2).2.natToList = List.ofFn v' :=
        Nat.natToVec_eq_some_iff.mp hv
      have hlen : (Nat.unpair (Nat.unpair (Nat.unpair d).2).2).2.natToList.length
          = (Nat.unpair (Nat.unpair d).2).1 := by rw [hl]; simp
      have hlt : ∀ i, v' i < d + 1 := fun i ↦
        Nat.lt_succ_iff.mpr <| le_trans (le_of_lt <| Nat.lt_of_eq_natToVec hv i)
          <| le_trans (Nat.unpair_right_le _) <| le_trans (Nat.unpair_right_le _)
          <| Nat.unpair_right_le _
      rcases hf : (decode (Nat.unpair (Nat.unpair (Nat.unpair d).2).2).1 :
          Option (L.Func (Nat.unpair (Nat.unpair d).2).1)) with _ | f
      · rw [if_neg ?_]
        · simp
        · rintro ⟨-, hne, -⟩
          exact hne (by simp)
      · rcases hg : (Matrix.getM fun i ↦ ofNat (L := L) (ξ := ξ) n (v' i)) with _ | t
        · obtain ⟨i₀, hi₀⟩ : ∃ i, ofNat (L := L) (ξ := ξ) n (v' i) = none := by
            by_contra hcon
            push Not at hcon
            choose t ht using fun i ↦ Option.ne_none_iff_exists'.mp (hcon i)
            rw [Matrix.getM_option_eq_some_iff.mpr ht] at hg
            exact absurd hg (by simp)
          rw [if_neg ?_]
          · simp [hg]
          · rintro ⟨-, -, hne⟩
            refine hne (stepVec_eq_zero (j := v' i₀) ?_ ?_)
            · rw [hl]; exact List.mem_ofFn.mpr ⟨i₀, rfl⟩
            · rw [table_getD (hlt i₀), hi₀]; simp
        · have hT : ∀ i, (table (L := L) (ξ := ξ) n (d + 1)).getD (v' i) 0
              = encode (t i) + 1 := fun i ↦ by
            rw [table_getD (hlt i), Matrix.getM_option_eq_some_iff.mp hg i]
            simp
          have hsv : stepVec (table (L := L) (ξ := ξ) n (d + 1))
              (Nat.natToList (Nat.unpair (Nat.unpair (Nat.unpair d).2).2).2)
              = Matrix.vecToNat (fun i ↦ encode (t i)) + 1 := by
            rw [hl]; exact stepVec_ofFn hT
          rw [if_pos ⟨hlen, by simp, by rw [hsv]; simp⟩, hsv]
          simp [hg, encode_eq_toNat, toNat]
  · rw [if_neg h0, if_neg h1, if_neg h2]
    match hi : (Nat.unpair d).1 with
    | 0 => exact absurd hi h0
    | 1 => exact absurd hi h1
    | 2 => exact absurd hi h2
    | k + 3 => simp

/-- **Issue #506, term half.** -/
theorem encode_ofNat_primrec :
    Primrec₂ fun n e : ℕ ↦ encode (ofNat (L := L) (ξ := ξ) n e) :=
  Primrec.nat_strong_rec _ (g := fun n T ↦ some (step (L := L) (ξ := ξ) n T))
    (Primrec.option_some.comp primrec_step) fun n e ↦ congrArg some (step_table n e)

/-- **Issue #506, first headline.** The instance sits on the `Encodable` instance already in
`Basic/Coding.lean`, so nothing downstream sees a new `encode`; the checks below confirm that, and
that `decode` is still `ofNat`. -/
instance primcodable {n : ℕ} : Primcodable (Semiterm L ξ n) where
  toEncodable := Semiterm.encodable
  prim := Primrec.nat_iff.mp <|
    (encode_ofNat_primrec (L := L) (ξ := ξ)).comp (Primrec.const n) Primrec.id

example {n : ℕ} : (Semiterm.primcodable (L := L) (ξ := ξ) (n := n)).toEncodable
    = Semiterm.encodable := by with_reducible_and_instances rfl

example {n : ℕ} (t : Semiterm L ξ n) : encode t = toNat t := rfl

example {n : ℕ} (e : ℕ) : (decode e : Option (Semiterm L ξ n)) = ofNat n e := rfl

example {n : ℕ} (t : Semiterm L ξ n) : (decode (encode t) : Option (Semiterm L ξ n)) = some t :=
  Encodable.encodek t


end Semiterm

namespace Semiformula

open LO.FirstOrder.Semiterm

variable {L : Language} [L.Encodable] [L.Primcodable] {ξ : Type*} [Primcodable ξ]

/-- The `rel`/`nrel` argument fold, the term-decoding sibling of `Semiterm.stepVec`. Where the term
version reads each argument out of the strong-recursion table, this decodes each argument code as a
term of `Semiterm L ξ n` — the arguments of a relation are terms, not sub-formulas, so they are not
in any table. `0` is failure and `r + 1` success, exactly as there, and for the same reason. -/
def stepVecT (n : ℕ) (l : List ℕ) : ℕ :=
  l.foldr (fun j acc ↦
    if encode (decode j : Option (Semiterm L ξ n)) = 0 ∨ acc = 0 then 0
    else Nat.pair (encode (decode j : Option (Semiterm L ξ n)) - 1) (acc - 1) + 2) 1

omit [L.Primcodable] in
@[simp] lemma stepVecT_nil (n : ℕ) : stepVecT (L := L) (ξ := ξ) n [] = 1 := rfl

omit [L.Primcodable] in
lemma stepVecT_cons (n : ℕ) (j : ℕ) (l : List ℕ) :
    stepVecT (L := L) (ξ := ξ) n (j :: l) =
      if encode (decode j : Option (Semiterm L ξ n)) = 0 ∨ stepVecT (L := L) (ξ := ξ) n l = 0 then 0
      else Nat.pair (encode (decode j : Option (Semiterm L ξ n)) - 1)
        (stepVecT (L := L) (ξ := ξ) n l - 1) + 2 := rfl

omit [L.Primcodable] in
/-- Value fact, success. -/
lemma stepVecT_ofFn {n a : ℕ} {w u : Fin a → ℕ}
    (h : ∀ i, encode (decode (w i) : Option (Semiterm L ξ n)) = u i + 1) :
    stepVecT (L := L) (ξ := ξ) n (List.ofFn w) = Matrix.vecToNat u + 1 := by
  induction a with
  | zero => simp [Matrix.vecToNat]
  | succ a ih =>
    rw [List.ofFn_succ, stepVecT_cons,
      ih (w := fun i ↦ w i.succ) (u := fun i ↦ u i.succ) fun i ↦ by simpa using h i.succ,
      h 0, if_neg (by simp)]
    simp only [Nat.add_sub_cancel]
    simpa using (Matrix.encode_succ (u 0) (fun i ↦ u i.succ)).symm

omit [L.Primcodable] in
/-- Value fact, failure. -/
lemma stepVecT_eq_zero {n : ℕ} {l : List ℕ} {j : ℕ} (hj : j ∈ l)
    (h : encode (decode j : Option (Semiterm L ξ n)) = 0) : stepVecT (L := L) (ξ := ξ) n l = 0 := by
  induction l with
  | nil => simp at hj
  | cons b l ih =>
    rw [stepVecT_cons]
    rcases List.mem_cons.mp hj with rfl | hj'
    · exact if_pos (Or.inl h)
    · exact if_pos (Or.inr (ih hj'))

open Primrec in
theorem primrec_stepVecT : Primrec₂ (stepVecT (L := L) (ξ := ξ)) := by
  have hp : Primrec fun p : ℕ × List ℕ ↦
      p.2.foldr (fun j acc ↦
        if encode (decode j : Option (Semiterm L ξ p.1)) = 0 ∨ acc = 0 then 0
        else Nat.pair (encode (decode j : Option (Semiterm L ξ p.1)) - 1) (acc - 1) + 2) 1 := by
    refine Primrec.list_foldr (β := ℕ) (σ := ℕ)
      (f := fun p : ℕ × List ℕ ↦ p.2) (g := fun _ ↦ (1 : ℕ))
      (h := fun p x ↦ if encode (decode x.1 : Option (Semiterm L ξ p.1)) = 0 ∨ x.2 = 0 then 0
        else Nat.pair (encode (decode x.1 : Option (Semiterm L ξ p.1)) - 1) (x.2 - 1) + 2)
      snd (const _) ?_
    have hdec : Primrec fun y : (ℕ × List ℕ) × ℕ × ℕ ↦
        encode (decode y.2.1 : Option (Semiterm L ξ y.1.1)) :=
      (Semiterm.encode_ofNat_primrec (L := L) (ξ := ξ)).comp (fst.comp fst) (fst.comp snd)
        |>.of_eq fun _ ↦ rfl
    refine Primrec.ite (PrimrecPred.or (Primrec.eq.comp hdec (const 0))
      (Primrec.eq.comp (snd.comp snd) (const 0))) (const 0) ?_
    exact Primrec.nat_add.comp
      (Primrec₂.natPair.comp (nat_sub.comp hdec (const 1))
        (nat_sub.comp (snd.comp snd) (const 1))) (const 2)
  exact hp.of_eq fun p ↦ rfl


/-! ### The formula step function

`Semiformula.ofNat` cannot use `Primrec.nat_strong_rec`, and the reason is structural rather than
incidental: the `∀`/`∃` branches recurse at `ofNat (n + 1)`, so the arity changes as the recursion
descends, while `nat_strong_rec` holds its parameter fixed and tabulates one arity only. The
recursion is therefore run by `Primrec.nat_omega_rec'` over pairs `(n, e)`, with `e` as the measure
and `subArgs` naming the immediate sub-formulas — two at the same arity for `⋏`/`⋎`, one at the
successor arity for `∀`/`∃`, and none elsewhere. The measure obligation is discharged by
`subArgs_ord`, which is just `ofNat`'s own internal `< e + 1` proofs read back.

`step` is written with an `if` rather than a `Nat.casesOn` deliberately. The `Primrec` combinators
have to synthesise `Primcodable` for the tower of products the ambient argument lives in, and a
`casesOn` adds a level: with it the tower is `((ℕ × ℕ) × List ℕ) × ℕ` and elaboration diverges,
exactly as an `Option`-valued fold did in the term half. The `if` keeps it at `(ℕ × ℕ) × List ℕ`
and elaborates. -/

def stepBody (n d : ℕ) (vs : List ℕ) : ℕ :=
    if d.unpair.1 = 0 then
      (if (Nat.natToList d.unpair.2.unpair.2.unpair.2).length = d.unpair.2.unpair.1 ∧
          (encode (decode d.unpair.2.unpair.2.unpair.1 :
            Option (L.Rel d.unpair.2.unpair.1))) ≠ 0 ∧
          stepVecT (L := L) (ξ := ξ) n (Nat.natToList d.unpair.2.unpair.2.unpair.2) ≠ 0 then
        Nat.pair 0 (Nat.pair d.unpair.2.unpair.1
          (Nat.pair ((encode (decode d.unpair.2.unpair.2.unpair.1 :
            Option (L.Rel d.unpair.2.unpair.1))) - 1)
            (stepVecT (L := L) (ξ := ξ) n (Nat.natToList d.unpair.2.unpair.2.unpair.2) - 1))) + 2
        else 0)
    else if d.unpair.1 = 1 then
      (if (Nat.natToList d.unpair.2.unpair.2.unpair.2).length = d.unpair.2.unpair.1 ∧
          (encode (decode d.unpair.2.unpair.2.unpair.1 :
            Option (L.Rel d.unpair.2.unpair.1))) ≠ 0 ∧
          stepVecT (L := L) (ξ := ξ) n (Nat.natToList d.unpair.2.unpair.2.unpair.2) ≠ 0 then
        Nat.pair 1 (Nat.pair d.unpair.2.unpair.1
          (Nat.pair ((encode (decode d.unpair.2.unpair.2.unpair.1 :
            Option (L.Rel d.unpair.2.unpair.1))) - 1)
            (stepVecT (L := L) (ξ := ξ) n (Nat.natToList d.unpair.2.unpair.2.unpair.2) - 1))) + 2
        else 0)
    else if d.unpair.1 = 2 then Nat.pair 2 0 + 2
    else if d.unpair.1 = 3 then Nat.pair 3 0 + 2
    else if d.unpair.1 = 4 then
      (if vs.getD 0 0 = 0 ∨ vs.getD 1 0 = 0 then 0
        else Nat.pair 4 (Nat.pair (vs.getD 0 0 - 1) (vs.getD 1 0 - 1)) + 2)
    else if d.unpair.1 = 5 then
      (if vs.getD 0 0 = 0 ∨ vs.getD 1 0 = 0 then 0
        else Nat.pair 5 (Nat.pair (vs.getD 0 0 - 1) (vs.getD 1 0 - 1)) + 2)
    else if d.unpair.1 = 6 then
      (if vs.getD 0 0 = 0 then 0 else Nat.pair 6 (vs.getD 0 0 - 1) + 2)
    else if d.unpair.1 = 7 then
      (if vs.getD 0 0 = 0 then 0 else Nat.pair 7 (vs.getD 0 0 - 1) + 2)
    else 0

def step (n e : ℕ) (vs : List ℕ) : ℕ :=
  if e = 0 then 0 else stepBody (L := L) (ξ := ξ) n (e - 1) vs

def subArgs (b : ℕ × ℕ) : List (ℕ × ℕ) :=
  Nat.casesOn (motive := fun _ ↦ List (ℕ × ℕ)) b.2 [] fun d ↦
    if d.unpair.1 = 4 ∨ d.unpair.1 = 5 then [(b.1, d.unpair.2.unpair.1), (b.1, d.unpair.2.unpair.2)]
    else if d.unpair.1 = 6 ∨ d.unpair.1 = 7 then [(b.1 + 1, d.unpair.2)]
    else []

omit [L.Primcodable] in
lemma subArgs_succ (n d : ℕ) : subArgs (n, d + 1) =
    (if d.unpair.1 = 4 ∨ d.unpair.1 = 5 then
        [(n, d.unpair.2.unpair.1), (n, d.unpair.2.unpair.2)]
      else if d.unpair.1 = 6 ∨ d.unpair.1 = 7 then [(n + 1, d.unpair.2)] else []) := rfl

omit [L.Primcodable] in
lemma vs_bin (n d : ℕ) (h : d.unpair.1 = 4 ∨ d.unpair.1 = 5) :
    (subArgs (n, d + 1)).map (fun b ↦ encode (ofNat (L := L) (ξ := ξ) b.1 b.2))
      = [encode (ofNat (L := L) (ξ := ξ) n d.unpair.2.unpair.1),
         encode (ofNat (L := L) (ξ := ξ) n d.unpair.2.unpair.2)] := by
  rw [subArgs_succ, if_pos h]; simp

omit [L.Primcodable] in
lemma vs_quant (n d : ℕ) (h45 : ¬(d.unpair.1 = 4 ∨ d.unpair.1 = 5))
    (h : d.unpair.1 = 6 ∨ d.unpair.1 = 7) :
    (subArgs (n, d + 1)).map (fun b ↦ encode (ofNat (L := L) (ξ := ξ) b.1 b.2))
      = [encode (ofNat (L := L) (ξ := ξ) (n + 1) d.unpair.2)] := by
  rw [subArgs_succ, if_neg h45, if_pos h]; simp

lemma subArgs_ord (b : ℕ × ℕ) : ∀ b' ∈ subArgs b, b'.2 < b.2 := by
  rcases b with ⟨n, e⟩
  cases e with
  | zero => simp [subArgs]
  | succ d =>
    rw [subArgs_succ]
    by_cases h4 : d.unpair.1 = 4 ∨ d.unpair.1 = 5
    · rw [if_pos h4]
      intro b' hb'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb'
      have h1 : d.unpair.2.unpair.1 ≤ d := le_trans (Nat.unpair_left_le _) (Nat.unpair_right_le _)
      have h2 : d.unpair.2.unpair.2 ≤ d := le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _)
      rcases hb' with rfl | rfl <;> simp <;> omega
    · rw [if_neg h4]
      by_cases h6 : d.unpair.1 = 6 ∨ d.unpair.1 = 7
      · rw [if_pos h6]
        intro b' hb'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb'
        have : d.unpair.2 ≤ d := Nat.unpair_right_le _
        rcases hb' with rfl; simp; omega
      · rw [if_neg h6]; simp

omit [L.Primcodable] in
theorem step_correct (n e : ℕ) :
    step (L := L) (ξ := ξ) n e
      ((subArgs (n, e)).map (fun b ↦ encode (ofNat (L := L) (ξ := ξ) b.1 b.2)))
      = encode (ofNat (L := L) (ξ := ξ) n e) := by
  cases e with
  | zero => simp [step, ofNat]
  | succ d =>
  rw [step, if_neg (Nat.succ_ne_zero d), Nat.add_sub_cancel, stepBody, ofNat]
  by_cases h4 : d.unpair.1 = 4
  · rw [vs_bin n d (Or.inl h4), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_pos h4, h4]
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    rcases hφ : ofNat (L := L) (ξ := ξ) n d.unpair.2.unpair.1 with _ | φ
    · simp
    · rcases hψ : ofNat (L := L) (ξ := ξ) n d.unpair.2.unpair.2 with _ | ψ
      · simp
      · rw [if_neg (by simp)]
        simp [encode_eq_toNat, toNat]
  by_cases h5 : d.unpair.1 = 5
  · rw [vs_bin n d (Or.inr h5), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_pos h5, h5]
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    rcases hφ : ofNat (L := L) (ξ := ξ) n d.unpair.2.unpair.1 with _ | φ
    · simp
    · rcases hψ : ofNat (L := L) (ξ := ξ) n d.unpair.2.unpair.2 with _ | ψ
      · simp
      · rw [if_neg (by simp)]
        simp [encode_eq_toNat, toNat]
  by_cases h6 : d.unpair.1 = 6
  · rw [vs_quant n d (by simp [h6]) (Or.inl h6), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h6, h6]
    simp only [List.getD_cons_zero]
    rcases hφ : ofNat (L := L) (ξ := ξ) (n + 1) d.unpair.2 with _ | φ
    · simp
    · rw [if_neg (by simp)]
      simp [encode_eq_toNat, toNat]
  by_cases h7 : d.unpair.1 = 7
  · rw [vs_quant n d (by simp [h7]) (Or.inr h7), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_pos h7, h7]
    simp only [List.getD_cons_zero]
    rcases hφ : ofNat (L := L) (ξ := ξ) (n + 1) d.unpair.2 with _ | φ
    · simp
    · rw [if_neg (by simp)]
      simp [encode_eq_toNat, toNat]
  by_cases h2 : d.unpair.1 = 2
  · rw [if_neg (by omega), if_neg (by omega), if_pos h2, h2]
    simp [encode_eq_toNat, toNat]
  by_cases h3 : d.unpair.1 = 3
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h3, h3]
    simp [encode_eq_toNat, toNat]
  by_cases h0 : d.unpair.1 = 0
  · rw [if_pos h0, h0]
    simp only []
    rcases hv : (Nat.unpair (Nat.unpair (Nat.unpair d).2).2).2.natToVec
        (Nat.unpair (Nat.unpair d).2).1 with _ | v'
    · rw [if_neg ?_]
      · simp
      · rintro ⟨hlen, -, -⟩
        obtain ⟨w, hw⟩ := Nat.natToVec_isSome_of_length hlen
        rw [hw] at hv; exact absurd hv (by simp)
    · have hl : (Nat.unpair (Nat.unpair (Nat.unpair d).2).2).2.natToList = List.ofFn v' :=
        Nat.natToVec_eq_some_iff.mp hv
      have hlen : (Nat.unpair (Nat.unpair (Nat.unpair d).2).2).2.natToList.length
          = (Nat.unpair (Nat.unpair d).2).1 := by rw [hl]; simp
      rcases hR : (decode (Nat.unpair (Nat.unpair (Nat.unpair d).2).2).1 :
          Option (L.Rel (Nat.unpair (Nat.unpair d).2).1)) with _ | R
      · rw [if_neg ?_]
        · simp
        · rintro ⟨-, hne, -⟩; exact hne (by simp)
      · rcases hg : (Matrix.getM fun i ↦ (decode (v' i) : Option (Semiterm L ξ n))) with _ | t
        · obtain ⟨i₀, hi₀⟩ : ∃ i, (decode (v' i) : Option (Semiterm L ξ n)) = none := by
            by_contra hcon
            push Not at hcon
            choose t ht using fun i ↦ Option.ne_none_iff_exists'.mp (hcon i)
            rw [Matrix.getM_option_eq_some_iff.mpr ht] at hg; exact absurd hg (by simp)
          rw [if_neg ?_]
          · simp [hg]
          · rintro ⟨-, -, hne⟩
            refine hne (stepVecT_eq_zero (j := v' i₀) ?_ ?_)
            · rw [hl]; exact List.mem_ofFn.mpr ⟨i₀, rfl⟩
            · rw [hi₀]; simp
        · have hT : ∀ i, encode (decode (v' i) : Option (Semiterm L ξ n)) = encode (t i) + 1 :=
            fun i ↦ by rw [Matrix.getM_option_eq_some_iff.mp hg i]; simp
          have hsv : stepVecT (L := L) (ξ := ξ) n
              (Nat.natToList (Nat.unpair (Nat.unpair (Nat.unpair d).2).2).2)
              = Matrix.vecToNat (fun i ↦ encode (t i)) + 1 := by rw [hl]; exact stepVecT_ofFn hT
          rw [if_pos ⟨hlen, by simp, by rw [hsv]; simp⟩, hsv]
          simp [hg, encode_eq_toNat, toNat]
  by_cases h1 : d.unpair.1 = 1
  · rw [if_neg h0, if_pos h1, h1]
    simp only []
    rcases hv : (Nat.unpair (Nat.unpair (Nat.unpair d).2).2).2.natToVec
        (Nat.unpair (Nat.unpair d).2).1 with _ | v'
    · rw [if_neg ?_]
      · simp
      · rintro ⟨hlen, -, -⟩
        obtain ⟨w, hw⟩ := Nat.natToVec_isSome_of_length hlen
        rw [hw] at hv; exact absurd hv (by simp)
    · have hl : (Nat.unpair (Nat.unpair (Nat.unpair d).2).2).2.natToList = List.ofFn v' :=
        Nat.natToVec_eq_some_iff.mp hv
      have hlen : (Nat.unpair (Nat.unpair (Nat.unpair d).2).2).2.natToList.length
          = (Nat.unpair (Nat.unpair d).2).1 := by rw [hl]; simp
      rcases hR : (decode (Nat.unpair (Nat.unpair (Nat.unpair d).2).2).1 :
          Option (L.Rel (Nat.unpair (Nat.unpair d).2).1)) with _ | R
      · rw [if_neg ?_]
        · simp
        · rintro ⟨-, hne, -⟩; exact hne (by simp)
      · rcases hg : (Matrix.getM fun i ↦ (decode (v' i) : Option (Semiterm L ξ n))) with _ | t
        · obtain ⟨i₀, hi₀⟩ : ∃ i, (decode (v' i) : Option (Semiterm L ξ n)) = none := by
            by_contra hcon
            push Not at hcon
            choose t ht using fun i ↦ Option.ne_none_iff_exists'.mp (hcon i)
            rw [Matrix.getM_option_eq_some_iff.mpr ht] at hg; exact absurd hg (by simp)
          rw [if_neg ?_]
          · simp [hg]
          · rintro ⟨-, -, hne⟩
            refine hne (stepVecT_eq_zero (j := v' i₀) ?_ ?_)
            · rw [hl]; exact List.mem_ofFn.mpr ⟨i₀, rfl⟩
            · rw [hi₀]; simp
        · have hT : ∀ i, encode (decode (v' i) : Option (Semiterm L ξ n)) = encode (t i) + 1 :=
            fun i ↦ by rw [Matrix.getM_option_eq_some_iff.mp hg i]; simp
          have hsv : stepVecT (L := L) (ξ := ξ) n
              (Nat.natToList (Nat.unpair (Nat.unpair (Nat.unpair d).2).2).2)
              = Matrix.vecToNat (fun i ↦ encode (t i)) + 1 := by rw [hl]; exact stepVecT_ofFn hT
          rw [if_pos ⟨hlen, by simp, by rw [hsv]; simp⟩, hsv]
          simp [hg, encode_eq_toNat, toNat]
  · rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7]
    match hi : d.unpair.1 with
    | 0 => exact absurd hi h0
    | 1 => exact absurd hi h1
    | 2 => exact absurd hi h2
    | 3 => exact absurd hi h3
    | 4 => exact absurd hi h4
    | 5 => exact absurd hi h5
    | 6 => exact absurd hi h6
    | 7 => exact absurd hi h7
    | k + 8 => simp


open Primrec in
theorem primrec_subArgs : Primrec subArgs := by
  have hbody : Primrec fun r : (ℕ × ℕ) × ℕ ↦
      (if r.2.unpair.1 = 4 ∨ r.2.unpair.1 = 5 then
          [(r.1.1, r.2.unpair.2.unpair.1), (r.1.1, r.2.unpair.2.unpair.2)]
        else if r.2.unpair.1 = 6 ∨ r.2.unpair.1 = 7 then [(r.1.1 + 1, r.2.unpair.2)]
        else ([] : List (ℕ × ℕ))) := by
    have hn : Primrec fun r : (ℕ × ℕ) × ℕ ↦ r.1.1 := fst.comp fst
    have hi : Primrec fun r : (ℕ × ℕ) × ℕ ↦ r.2.unpair.1 := fst.comp (Primrec.unpair.comp snd)
    have hc : Primrec fun r : (ℕ × ℕ) × ℕ ↦ r.2.unpair.2 := snd.comp (Primrec.unpair.comp snd)
    have hc1 : Primrec fun r : (ℕ × ℕ) × ℕ ↦ r.2.unpair.2.unpair.1 :=
      fst.comp (Primrec.unpair.comp hc)
    have hc2 : Primrec fun r : (ℕ × ℕ) × ℕ ↦ r.2.unpair.2.unpair.2 :=
      snd.comp (Primrec.unpair.comp hc)
    refine Primrec.ite (PrimrecPred.or (Primrec.eq.comp hi (const 4))
      (Primrec.eq.comp hi (const 5)))
      (list_cons.comp (Primrec₂.pair.comp hn hc1)
        (list_cons.comp (Primrec₂.pair.comp hn hc2) (Primrec.const ([] : List (ℕ × ℕ))))) ?_
    exact Primrec.ite (PrimrecPred.or (Primrec.eq.comp hi (const 6))
      (Primrec.eq.comp hi (const 7)))
      (list_cons.comp (Primrec₂.pair.comp (succ.comp hn) hc)
        (Primrec.const ([] : List (ℕ × ℕ)))) (Primrec.const ([] : List (ℕ × ℕ)))
  exact (Primrec.nat_casesOn (f := fun b : ℕ × ℕ ↦ b.2) (g := fun _ ↦ ([] : List (ℕ × ℕ)))
    (h := fun b d ↦ if d.unpair.1 = 4 ∨ d.unpair.1 = 5 then
        [(b.1, d.unpair.2.unpair.1), (b.1, d.unpair.2.unpair.2)]
      else if d.unpair.1 = 6 ∨ d.unpair.1 = 7 then [(b.1 + 1, d.unpair.2)] else [])
    snd (Primrec.const _) hbody).of_eq fun b ↦ rfl

open Primrec in
theorem primrec_step :
    Primrec fun q : (ℕ × ℕ) × List ℕ ↦ step (L := L) (ξ := ξ) q.1.1 q.1.2 q.2 := by
  unfold step
  have hn : Primrec fun q : (ℕ × ℕ) × List ℕ ↦ q.1.1 := fst.comp fst
  have he : Primrec fun q : (ℕ × ℕ) × List ℕ ↦ q.1.2 := snd.comp fst
  have hvs : Primrec fun q : (ℕ × ℕ) × List ℕ ↦ q.2 := snd
  have hd : Primrec fun q : (ℕ × ℕ) × List ℕ ↦ q.1.2 - 1 := nat_sub.comp he (const 1)
  have hi : Primrec fun q : (ℕ × ℕ) × List ℕ ↦ (q.1.2 - 1).unpair.1 :=
    fst.comp (Primrec.unpair.comp hd)
  have hc : Primrec fun q : (ℕ × ℕ) × List ℕ ↦ (q.1.2 - 1).unpair.2 :=
    snd.comp (Primrec.unpair.comp hd)
  have ha : Primrec fun q : (ℕ × ℕ) × List ℕ ↦ (q.1.2 - 1).unpair.2.unpair.1 :=
    fst.comp (Primrec.unpair.comp hc)
  have hrest : Primrec fun q : (ℕ × ℕ) × List ℕ ↦ (q.1.2 - 1).unpair.2.unpair.2 :=
    snd.comp (Primrec.unpair.comp hc)
  have heR : Primrec fun q : (ℕ × ℕ) × List ℕ ↦ (q.1.2 - 1).unpair.2.unpair.2.unpair.1 :=
    fst.comp (Primrec.unpair.comp hrest)
  have hev : Primrec fun q : (ℕ × ℕ) × List ℕ ↦ (q.1.2 - 1).unpair.2.unpair.2.unpair.2 :=
    snd.comp (Primrec.unpair.comp hrest)
  have hR : Primrec fun q : (ℕ × ℕ) × List ℕ ↦
      (encode (decode (q.1.2 - 1).unpair.2.unpair.2.unpair.1 :
        Option (L.Rel (q.1.2 - 1).unpair.2.unpair.1))) :=
    (Language.Primcodable.rel (L := L)).comp ha heR
  have hl : Primrec fun q : (ℕ × ℕ) × List ℕ ↦
      Nat.natToList (q.1.2 - 1).unpair.2.unpair.2.unpair.2 := Primrec.nat_natToList.comp hev
  have hsv : Primrec fun q : (ℕ × ℕ) × List ℕ ↦
      stepVecT (L := L) (ξ := ξ) q.1.1 (Nat.natToList (q.1.2 - 1).unpair.2.unpair.2.unpair.2) :=
    primrec_stepVecT.comp hn hl
  have hv0 : Primrec fun q : (ℕ × ℕ) × List ℕ ↦ q.2.getD 0 0 :=
    (Primrec.list_getD 0).comp hvs (const 0)
  have hv1 : Primrec fun q : (ℕ × ℕ) × List ℕ ↦ q.2.getD 1 0 :=
    (Primrec.list_getD 0).comp hvs (const 1)
  have hrelArm : ∀ tag : ℕ, Primrec fun q : (ℕ × ℕ) × List ℕ ↦
      (if (Nat.natToList (q.1.2 - 1).unpair.2.unpair.2.unpair.2).length
            = (q.1.2 - 1).unpair.2.unpair.1 ∧
          (encode (decode (q.1.2 - 1).unpair.2.unpair.2.unpair.1 :
            Option (L.Rel (q.1.2 - 1).unpair.2.unpair.1))) ≠ 0 ∧
          stepVecT (L := L) (ξ := ξ) q.1.1
            (Nat.natToList (q.1.2 - 1).unpair.2.unpair.2.unpair.2) ≠ 0 then
        Nat.pair tag (Nat.pair (q.1.2 - 1).unpair.2.unpair.1
          (Nat.pair ((encode (decode (q.1.2 - 1).unpair.2.unpair.2.unpair.1 :
            Option (L.Rel (q.1.2 - 1).unpair.2.unpair.1))) - 1)
            (stepVecT (L := L) (ξ := ξ) q.1.1
              (Nat.natToList (q.1.2 - 1).unpair.2.unpair.2.unpair.2) - 1))) + 2
        else 0) := fun tag ↦
    Primrec.ite
      (PrimrecPred.and (Primrec.eq.comp (list_length.comp hl) ha)
        (PrimrecPred.and (PrimrecPred.not (Primrec.eq.comp hR (const 0)))
          (PrimrecPred.not (Primrec.eq.comp hsv (const 0)))))
      (Primrec.nat_add.comp
        (Primrec₂.natPair.comp (const tag)
          (Primrec₂.natPair.comp ha
            (Primrec₂.natPair.comp (nat_sub.comp hR (const 1))
              (nat_sub.comp hsv (const 1))))) (const 2))
      (const 0)
  have hbinArm : ∀ tag : ℕ, Primrec fun q : (ℕ × ℕ) × List ℕ ↦
      (if q.2.getD 0 0 = 0 ∨ q.2.getD 1 0 = 0 then 0
        else Nat.pair tag (Nat.pair (q.2.getD 0 0 - 1) (q.2.getD 1 0 - 1)) + 2) := fun tag ↦
    Primrec.ite (PrimrecPred.or (Primrec.eq.comp hv0 (const 0))
      (Primrec.eq.comp hv1 (const 0))) (const 0)
      (Primrec.nat_add.comp
        (Primrec₂.natPair.comp (const tag)
          (Primrec₂.natPair.comp (nat_sub.comp hv0 (const 1))
            (nat_sub.comp hv1 (const 1)))) (const 2))
  have hqArm : ∀ tag : ℕ, Primrec fun q : (ℕ × ℕ) × List ℕ ↦
      (if q.2.getD 0 0 = 0 then 0 else Nat.pair tag (q.2.getD 0 0 - 1) + 2) := fun tag ↦
    Primrec.ite (Primrec.eq.comp hv0 (const 0)) (const 0)
      (Primrec.nat_add.comp
        (Primrec₂.natPair.comp (const tag) (nat_sub.comp hv0 (const 1))) (const 2))
  refine Primrec.ite (Primrec.eq.comp he (const 0)) (const 0) ?_
  unfold stepBody
  exact Primrec.ite (Primrec.eq.comp hi (const 0)) (hrelArm 0)
    (Primrec.ite (Primrec.eq.comp hi (const 1)) (hrelArm 1)
      (Primrec.ite (Primrec.eq.comp hi (const 2)) (const (Nat.pair 2 0 + 2))
        (Primrec.ite (Primrec.eq.comp hi (const 3)) (const (Nat.pair 3 0 + 2))
          (Primrec.ite (Primrec.eq.comp hi (const 4)) (hbinArm 4)
            (Primrec.ite (Primrec.eq.comp hi (const 5)) (hbinArm 5)
              (Primrec.ite (Primrec.eq.comp hi (const 6)) (hqArm 6)
                (Primrec.ite (Primrec.eq.comp hi (const 7)) (hqArm 7)
                  (const 0))))))))

/-- **Issue #506, formula half.**

With `Semiterm.encode_ofNat_primrec` this closes the issue: `Primcodable` instances for both
`Semiterm L ξ n` and `Semiformula L ξ n`, for every language satisfying `Language.Primcodable` —
the uniform-in-arity condition, which `ℒₒᵣ` satisfies. Both instances sit on the `Encodable`
instances already in `Basic/Coding.lean`, so no existing `encode` or `decode` changes. -/
theorem encode_ofNat_primrec :
    Primrec₂ fun n e : ℕ ↦ encode (ofNat (L := L) (ξ := ξ) n e) :=
  Primrec.nat_omega_rec' (fun b : ℕ × ℕ ↦ encode (ofNat (L := L) (ξ := ξ) b.1 b.2))
    (m := fun b ↦ b.2) (l := subArgs)
    (g := fun b vs ↦ some (step (L := L) (ξ := ξ) b.1 b.2 vs))
    Primrec.snd primrec_subArgs (Primrec.option_some.comp primrec_step)
    subArgs_ord (fun b ↦ congrArg some (step_correct b.1 b.2))

/-- **Issue #506, second headline.** As with the term instance, this sits on
`Semiformula.encodable` rather than introducing a second `Encodable`; the checks below confirm
that, and that `encode` and `decode` are still `toNat` and `ofNat` definitionally. -/
instance primcodable {n : ℕ} : Primcodable (Semiformula L ξ n) where
  toEncodable := Semiformula.encodable
  prim := Primrec.nat_iff.mp <|
    (encode_ofNat_primrec (L := L) (ξ := ξ)).comp (Primrec.const n) Primrec.id

example {n : ℕ} : (Semiformula.primcodable (L := L) (ξ := ξ) (n := n)).toEncodable
    = Semiformula.encodable := by with_reducible_and_instances rfl

example {n : ℕ} (φ : Semiformula L ξ n) : encode φ = toNat φ := rfl

example {n : ℕ} (e : ℕ) : (decode e : Option (Semiformula L ξ n)) = ofNat n e := rfl

example {n : ℕ} (φ : Semiformula L ξ n) :
    (decode (encode φ) : Option (Semiformula L ξ n)) = some φ := Encodable.encodek φ


end Semiformula

end LO.FirstOrder

end
