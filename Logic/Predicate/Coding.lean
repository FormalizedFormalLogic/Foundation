import Logic.Predicate.Term
import Mathlib.Data.W.Basic

universe u v

variable {L : Language.{u}} [∀ k, Encodable (L.func k)] {μ : Type v} [Encodable μ]

namespace SubTerm
open Encodable
variable {n : ℕ}

-- 本来 " + 1"は必要ないがofNatの停止性の証明がより簡易になるためつけている
def toNat : SubTerm L μ n → ℕ 
  | #x                    => (Nat.bit false $ Nat.bit false (encode x)) + 1
  | &x                    => (Nat.bit false $ Nat.bit true (encode x)) + 1
  | func (arity := k) f v => (Nat.bit true  $ Nat.mkpair k $
      Nat.mkpair (encode f) (Matrix.vecToNat $ fun i => (v i).toNat)) + 1

def ofNat : ℕ → Option (SubTerm L μ n)
| 0  => none
| e + 1 =>
  match e.bodd with
  | false => 
    match e.div2.bodd with
    | false => (decode₂ (Fin n) e.div2.div2).map fixedVar
    | true  => (decode₂ μ e.div2.div2).map freeVar
  | true  =>
      let x := e.div2
      let k := x.unpair.1
      let f' : Option (L.func k) := decode₂ (L.func k) x.unpair.2.unpair.1
      let w : Fin k → ℕ := Nat.unvector x.unpair.2.unpair.2
      have : ∀ i, w i < e + 1 := fun i =>
        Nat.lt_succ_of_le (le_trans (Nat.unvector_le x.unpair.2.unpair.2 i)
          (le_trans (Nat.unpair_right_le _) $
            le_trans (Nat.unpair_right_le _) $ by simp[Nat.div2_val]; exact Nat.div_le_self e 2))
      let v' : Option (Fin k → SubTerm L μ n) := Matrix.toOptionVec (fun i => ofNat (w i))
      f'.bind fun f => v'.map fun v => func f v
  decreasing_by exact this i

@[simp] lemma ofNat_toNat : ∀ t : SubTerm L μ n, ofNat (toNat t) = some t
  | #x => by simp[ofNat, toNat]; rw[Nat.bodd_bit, Nat.div2_bit]; simp; rw[Nat.bodd_bit, Nat.div2_bit]; simp
  | &x => by simp[ofNat, toNat]; rw[Nat.bodd_bit, Nat.div2_bit]; simp; rw[Nat.bodd_bit, Nat.div2_bit]; simp
  | func f v => by
      simp[ofNat, toNat]
      rw[Nat.bodd_bit, Nat.div2_bit, Nat.unpair_mkpair]; simp[fun i => ofNat_toNat (v i)];

instance : Encodable (SubTerm L μ n) where
  encode := toNat
  decode := ofNat
  encodek := ofNat_toNat

variable [∀ k, DecidableEq (L.func k)]

def enumLtList : ℕ → List (SyntacticTerm L)
| 0     => []
| s + 1 => (Encodable.decode₂ (SyntacticTerm L) s).toList ++ enumLtList s

lemma mem_enumLtList_of_lt {i} {t : SyntacticTerm L} (h : encode t < i) : t ∈ enumLtList i := by
  induction' i with i ih <;> simp[enumLtList]
  · contradiction
  · have : encode t < i ∨ encode t = i := lt_or_eq_of_le (Nat.lt_succ.mp h)
    rcases this with (h | rfl) <;> simp[*]

def enumLt (s : ℕ) : Finset (SyntacticTerm L) := (enumLtList s).toFinset

@[simp] lemma enumLt_zero : (enumLt 0 : Finset (SyntacticTerm L)) = ∅ := rfl 

lemma mem_enumLt_of_lt {i} {t : SyntacticTerm L} (h : encode t < i) : t ∈ enumLt i :=
  by simp[enumLt]; exact mem_enumLtList_of_lt h

#eval enumLt (L := Language.ring) 100

end SubTerm