import Logic.FirstOrder.Basic.BinderNotation

namespace LO.FirstOrder

variable {L : Language} [(k : ℕ) → Encodable (L.Func k)] [(k : ℕ) → Encodable (L.Rel k)]

variable {ξ : Type*} [Encodable ξ]

open Encodable

namespace Semiterm

def toNat {n : ℕ} : Semiterm L ξ n → ℕ
  | #z                        => Nat.pair 0 z + 1
  | &x                        => Nat.pair 1 (encode x) + 1
  | func (arity := arity) f v => (Nat.pair 2 <| Nat.pair arity <| Nat.pair (encode f) <| Matrix.vecToNat fun i ↦ toNat (v i)) + 1

def ofNat (n : ℕ) : ℕ → Option (Semiterm L ξ n)
  | 0 => none
  | e + 1 =>
    match e.unpair.1 with
    | 0 => if h : e.unpair.2 < n then some #⟨e.unpair.2, h⟩ else none
    | 1 => (decode e.unpair.2).map (&·)
    | 2 =>
      let arity := e.unpair.2.unpair.1
      let ef := e.unpair.2.unpair.2.unpair.1
      let ev := e.unpair.2.unpair.2.unpair.2
      match hv : ev.natToVec arity with
      | some v' =>
        (decode ef).bind fun f : L.Func arity ↦
        (Matrix.getM fun i ↦
          have : v' i < e + 1 :=
            Nat.lt_succ.mpr
              <| le_trans (le_of_lt <| Nat.lt_of_eq_natToVec hv i)
              <| le_trans (Nat.unpair_right_le _)
              <| le_trans (Nat.unpair_right_le _)
              <| Nat.unpair_right_le _
          ofNat n (v' i)).map fun v : Fin arity → Semiterm L ξ n ↦
        func f v
      | none => none
    | _ => none

lemma ofNat_toNat {n : ℕ} : ∀ t : Semiterm L ξ n, ofNat n (toNat t) = some t
  | #z => by simp [toNat, ofNat]
  | &x => by simp [toNat, ofNat]
  | func f v => by
      simp only [toNat, ofNat, Nat.unpair_pair, Option.pure_def, Option.bind_eq_bind]
      rw [Nat.unpair_pair, Nat.unpair_pair, Nat.unpair_pair, Nat.natToVec_vecToNat]
      simp
      have : (fun i ↦ ofNat n (toNat (v i))) = (fun i ↦ pure (v i)) := funext <| fun i ↦ ofNat_toNat (v i)
      rw [this, Matrix.getM_pure]
      simp

instance encodable : Encodable (Semiterm L ξ n) where
  encode := toNat
  decode := ofNat n
  encodek := ofNat_toNat

end Semiterm

namespace Semiformula

def toNat : {n : ℕ} → Semiformula L ξ n → ℕ
  | _, rel (arity := arity) R v  => (Nat.pair 0 <| arity.pair <| (encode R).pair <| Matrix.vecToNat fun i ↦ encode (v i)) + 1
  | _, nrel (arity := arity) R v => (Nat.pair 1 <| arity.pair <| (encode R).pair <| Matrix.vecToNat fun i ↦ encode (v i)) + 1
  | _, ⊤                         => (Nat.pair 2 0) + 1
  | _, ⊥                         => (Nat.pair 3 0) + 1
  | _, p ⋏ q                     => (Nat.pair 4 <| p.toNat.pair q.toNat) + 1
  | _, p ⋎ q                     => (Nat.pair 5 <| p.toNat.pair q.toNat) + 1
  | _, ∀' p                      => (Nat.pair 6 <| p.toNat) + 1
  | _, ∃' p                      => (Nat.pair 7 <| p.toNat) + 1

def ofNat : (n : ℕ) → ℕ → Option (Semiformula L ξ n)
  | _, 0 => none
  | n, e + 1 =>
    let idx := e.unpair.1
    let c := e.unpair.2
    match idx with
    | 0 =>
      let arity := c.unpair.1
      let eR := c.unpair.2.unpair.1
      let ev := c.unpair.2.unpair.2
      match ev.natToVec arity with
      | some v' =>
          (decode eR).bind fun R : L.Rel arity ↦
          (Matrix.getM fun i ↦ decode (v' i)).map fun v : Fin arity → Semiterm L ξ n ↦
          rel R v
      | none => none
    | 1 =>
      let arity := c.unpair.1
      let eR := c.unpair.2.unpair.1
      let ev := c.unpair.2.unpair.2
      match ev.natToVec arity with
      | some v' =>
          (decode eR).bind fun R : L.Rel arity ↦
          (Matrix.getM fun i ↦ decode (v' i)).map fun v : Fin arity → Semiterm L ξ n ↦
          nrel R v
      | none => none
    | 2 => some ⊤
    | 3 => some ⊥
    | 4 =>
      have : c.unpair.1 < e + 1 := Nat.lt_succ.mpr <| le_trans (Nat.unpair_left_le _) <| Nat.unpair_right_le _
      have : c.unpair.2 < e + 1 := Nat.lt_succ.mpr <| le_trans (Nat.unpair_right_le _) <| Nat.unpair_right_le _
      do
        let p ← ofNat n c.unpair.1
        let q ← ofNat n c.unpair.2
        return p ⋏ q
    | 5 =>
      have : c.unpair.1 < e + 1 := Nat.lt_succ.mpr <| le_trans (Nat.unpair_left_le _) <| Nat.unpair_right_le _
      have : c.unpair.2 < e + 1 := Nat.lt_succ.mpr <| le_trans (Nat.unpair_right_le _) <| Nat.unpair_right_le _
      do
        let p ← ofNat n c.unpair.1
        let q ← ofNat n c.unpair.2
        return p ⋎ q
    | 6 =>
      have : c < e + 1 := Nat.lt_succ.mpr <| Nat.unpair_right_le _
      do
        let p ← ofNat (n + 1) c
        return ∀' p
    | 7 =>
      have : c < e + 1 := Nat.lt_succ.mpr <| Nat.unpair_right_le _
      do
        let p ← ofNat (n + 1) c
        return ∃' p
    | _ => none

lemma ofNat_toNat : {n : ℕ} → ∀ p : Semiformula L ξ n, ofNat n (toNat p) = some p
  | _, rel R v  => by
    simp only [toNat, ofNat, Nat.unpair_pair, Option.pure_def, Option.bind_eq_bind]
    rw [Nat.unpair_pair, Nat.unpair_pair]
    simp [Matrix.getM_pure]
  | _, nrel R v => by
    simp only [toNat, ofNat, Nat.unpair_pair, Option.pure_def, Option.bind_eq_bind]
    rw [Nat.unpair_pair, Nat.unpair_pair]
    simp [Matrix.getM_pure]
  | _, ⊤        => by simp [toNat, ofNat]
  | _, ⊥        => by simp [toNat, ofNat]
  | _, p ⋎ q    => by simp [toNat, ofNat, ofNat_toNat p, ofNat_toNat q]
  | _, p ⋏ q    => by simp [toNat, ofNat, ofNat_toNat p, ofNat_toNat q]
  | _, ∀' p     => by simp [toNat, ofNat, ofNat_toNat p]
  | _, ∃' p     => by simp [toNat, ofNat, ofNat_toNat p]

instance encodable : Encodable (Semiformula L ξ n) where
  encode := toNat
  decode := ofNat n
  encodek := ofNat_toNat

#eval encode (“0 = 1” : Sentence ℒₒᵣ)
-- 197238223176519750397888674610667118222730

end Semiformula

end LO.FirstOrder
