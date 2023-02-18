import Logic.Predicate.Term
import Mathlib.Data.W.Basic

variable {L : Language} [∀ k, Encodable (L.func k)] {μ : Type _} [Inhabited μ] [Encodable μ]

namespace SubTerm
open Encodable
variable {n : ℕ}

-- 本来 " + 1"は必要ないがofNatの停止性の証明がより簡易になるためつけている
def toNat : SubTerm L μ n → ℕ 
  | #x                    => (Nat.bit false $ Nat.bit false (encode x)) + 1
  | &x                    => (Nat.bit false $ Nat.bit true (encode x)) + 1
  | func (arity := k) f v => (Nat.bit true  $ Nat.mkpair k $
      Nat.mkpair (encode f) (Fin.finitaryToNat $ fun i => (v i).toNat)) + 1

#eval toNat (&9 : SyntacticSubTerm Language.equal 0)

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
            le_trans (Nat.unpair_right_le _) $ by simpa[Nat.div2_val] using Nat.div_le_self e 2))
      let v' : Option (Fin k → SubTerm L μ n) := Fin.toOptionFinTo (fun i => ofNat (w i))
      func <$> f' <*> v'
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

end SubTerm


