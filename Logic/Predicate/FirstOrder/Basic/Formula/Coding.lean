import Logic.Predicate.FirstOrder.Basic.Formula.Formula
import Logic.Predicate.FirstOrder.Basic.Term.Coding

namespace LO

namespace FirstOrder

variable {L : Language.{u}} [∀ k : ℕ, Encodable (L.func k)] [∀ k, Encodable (L.rel k)] {μ : Type v} [Encodable μ]

namespace SubFormula
open Encodable

def toNat : {n : ℕ} → SubFormula L μ n → ℕ
  | _, ⊤                     => 0
  | _, ⊥                     => 1
  | _, rel (arity := k) r v  => (Nat.bit false $ Nat.bit false $ Nat.pair k  $ Nat.pair (encode r) (encode v)) + 2
  | _, nrel (arity := k) r v => (Nat.bit false $ Nat.bit true  $ Nat.pair k  $ Nat.pair (encode r) (encode v)) + 2
  | _, p ⋏ q                 => (Nat.bit true  $ Nat.bit false $ Nat.bit false $ Nat.pair p.toNat q.toNat) + 2
  | _, p ⋎ q                 => (Nat.bit true  $ Nat.bit false $ Nat.bit true  $ Nat.pair p.toNat q.toNat) + 2
  | _, ∀' p                  => (Nat.bit true  $ Nat.bit true  $ Nat.bit false p.toNat) + 2
  | _, ∃' p                  => (Nat.bit true  $ Nat.bit true  $ Nat.bit true  p.toNat) + 2

def ofNat : (n : ℕ) → ℕ → Option (SubFormula L μ n)
  | n, 0     => some ⊤
  | n, 1     => some ⊥
  | n, (e + 2) =>
    match e.bodd with
    | false =>
      let x := e.div2.div2
      let k := x.unpair.1
      let r' := decode₂ (L.rel k) x.unpair.2.unpair.1
      let v' := decode₂ (Fin k → SubTerm L μ n) x.unpair.2.unpair.2
      match e.div2.bodd with
      | false => r'.bind fun r => v'.map fun v => rel r v
      | true  => r'.bind fun r => v'.map fun v => nrel r v
    | true  =>
      let x := e.div2.div2.div2
      have div8 : x ≤ e := by
        simp[Nat.div2_val]
        exact le_trans (Nat.div_le_self (e / 2 / 2) 2) (le_trans (Nat.div_le_self (e/2) 2) (Nat.div_le_self e 2))
      have h : x < e + 2 := Nat.lt.step $ Nat.lt_succ_iff.mpr div8
      have : x.unpair.1 < e + 2 := lt_of_le_of_lt (Nat.unpair_left_le _) h
      have : x.unpair.2 < e + 2 := lt_of_le_of_lt (Nat.unpair_right_le _) h
      match e.div2.bodd with
      | false =>  
        let p' := ofNat n x.unpair.1
        let q' := ofNat n x.unpair.2
        match e.div2.div2.bodd with
        | false => p'.bind fun p => q'.map fun q => p ⋏ q
        | true  => p'.bind fun p => q'.map fun q => p ⋎ q
      | true  =>
        let p' := ofNat (n + 1) x
        match e.div2.div2.bodd with
        | false => p'.bind fun p => ∀' p
        | true  => p'.bind fun p => ∃' p
  termination_by ofNat n e => e

lemma ofNat_toNat : ∀ {n} (p : SubFormula L μ n), ofNat n p.toNat = some p
  | _, ⊤ => by simp[toNat, ofNat]
  | _, ⊥ => by simp[toNat, ofNat]
  | n, rel r v => by
      simp[toNat, ofNat]
      rw[Nat.bodd_bit, Nat.div2_bit]; simp
      rw[Nat.bodd_bit, Nat.div2_bit, Nat.unpair_pair]; simp
  | n, nrel r v => by
      simp[toNat, ofNat]
      rw[Nat.bodd_bit, Nat.div2_bit]; simp
      rw[Nat.bodd_bit, Nat.div2_bit, Nat.unpair_pair]; simp     
  | n, p ⋏ q => by
      simp[toNat, ofNat]
      rw[Nat.bodd_bit, Nat.div2_bit]; simp
      rw[Nat.bodd_bit, Nat.div2_bit]; simp
      rw[Nat.bodd_bit, Nat.div2_bit]; simp[ofNat_toNat p, ofNat_toNat q]
  | n, p ⋎ q => by
      simp[toNat, ofNat]
      rw[Nat.bodd_bit, Nat.div2_bit]; simp
      rw[Nat.bodd_bit, Nat.div2_bit]; simp
      rw[Nat.bodd_bit, Nat.div2_bit]; simp[ofNat_toNat p, ofNat_toNat q]    
  | n, ∀' p => by
      simp[toNat, ofNat]
      rw[Nat.bodd_bit, Nat.div2_bit]; simp
      rw[Nat.bodd_bit, Nat.div2_bit]; simp
      rw[Nat.bodd_bit, Nat.div2_bit]; simp[ofNat_toNat p]
  | n, ∃' p => by
      simp[toNat, ofNat]
      rw[Nat.bodd_bit, Nat.div2_bit]; simp
      rw[Nat.bodd_bit, Nat.div2_bit]; simp
      rw[Nat.bodd_bit, Nat.div2_bit]; simp[ofNat_toNat p]

instance (n) : Encodable (SubFormula L μ n) where
  encode  := toNat
  decode  := ofNat n
  encodek := ofNat_toNat

end SubFormula

end FirstOrder

end LO