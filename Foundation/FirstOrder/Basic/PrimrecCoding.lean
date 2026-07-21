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

end Semiterm

end LO.FirstOrder

end
