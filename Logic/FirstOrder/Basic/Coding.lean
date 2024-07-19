import Logic.FirstOrder.Basic.Calculus2

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
    | 1 => (&·) <$> decode e.unpair.2
    | 2 =>
      let arity := e.unpair.2.unpair.1
      let ef := e.unpair.2.unpair.2.unpair.1
      let ev := e.unpair.2.unpair.2.unpair.2
      match hv : ev.natToVec arity with
      | some v' =>
        do
          let f : L.Func arity ← decode ef
          let v : Fin arity → Semiterm L ξ n ← Matrix.getM fun i ↦
            have : v' i < e + 1 :=
              Nat.lt_succ.mpr
                <| le_trans (le_of_lt <| Nat.lt_of_eq_natToVec hv i)
                <| le_trans (Nat.unpair_right_le _)
                <| le_trans (Nat.unpair_right_le _)
                <| Nat.unpair_right_le _
            ofNat n (v' i)
          return func f v
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

instance : Encodable (Semiterm L ξ n) where
  encode := toNat
  decode := ofNat n
  encodek := ofNat_toNat

end Semiterm

/-
namespace Semiformula

def toNat : {n : ℕ} → Semiformula L ξ n → ℕ
  | n, rel (arity := arity) R v  => (n.pair <| Nat.pair 0 <| arity.pair <| (encode R).pair <| Matrix.vecToNat fun i ↦ encode (v i)) + 1
  | n, nrel (arity := arity) R v => (n.pair <| Nat.pair 1 <| arity.pair <| (encode R).pair <| Matrix.vecToNat fun i ↦ encode (v i)) + 1
  | n, ⊤                         => (n.pair <| Nat.pair 2 0) + 1
  | n, ⊥                         => (n.pair <| Nat.pair 3 0) + 1
  | n, p ⋏ q                     => (n.pair <| Nat.pair 4 <| p.toNat.pair q.toNat) + 1
  | n, p ⋎ q                     => (n.pair <| Nat.pair 5 <| p.toNat.pair q.toNat) + 1
  | n, ∀' p                      => (n.pair <| Nat.pair 6 <| p.toNat) + 1
  | n, ∃' p                      => (n.pair <| Nat.pair 7 <| p.toNat) + 1

def bcast {n n' : ℕ} (p : Semiformula L ξ n) (h : n = n') : Semiformula L ξ n' := h ▸ p

def ofNatAux : ℕ → Option ((n : ℕ) × Semiformula L ξ n)
  | 0 => none
  | e + 1 =>
    let n := e.unpair.1
    let idx := e.unpair.2.unpair.1
    let c := e.unpair.2.unpair.2
    match idx with
    | 0 =>
      let arity := c.unpair.1
      let eR := c.unpair.2.unpair.1
      let ev := c.unpair.2.unpair.2
      match ev.natToVec arity with
      | some v' =>
          do
            let R : L.Rel arity ← decode eR
            let v : Fin arity → Semiterm L ξ n ← Matrix.getM fun i ↦ decode (v' i)
            return ⟨n, rel R v⟩
      | none => none
    | 1 =>
      let arity := c.unpair.1
      let eR := c.unpair.2.unpair.1
      let ev := c.unpair.2.unpair.2
      match ev.natToVec arity with
      | some v' =>
          do
            let R : L.Rel arity ← decode eR
            let v : Fin arity → Semiterm L ξ n ← Matrix.getM fun i ↦ decode (v' i)
            return ⟨n, nrel R v⟩
      | none => none
    | 2 => some ⟨n, ⊤⟩
    | 3 => some ⟨n, ⊥⟩
    | 4 =>
      have : c.unpair.1 < e + 1 :=
        Nat.lt_succ.mpr <| le_trans (Nat.unpair_left_le _) <| le_trans (Nat.unpair_right_le _) <| Nat.unpair_right_le _
      have : c.unpair.2 < e + 1 :=
        Nat.lt_succ.mpr <| le_trans (Nat.unpair_right_le _) <| le_trans (Nat.unpair_right_le _) <| Nat.unpair_right_le _
      do
        let ⟨n', p⟩ ← ofNatAux c.unpair.1
        let ⟨n'', q⟩ ← ofNatAux c.unpair.2
        if h : n' = n ∧ n'' = n then return ⟨n, p.bcast h.1 ⋏ q.bcast h.2⟩ else none
    | 5 =>
      have : c.unpair.1 < e + 1 :=
        Nat.lt_succ.mpr <| le_trans (Nat.unpair_left_le _) <| le_trans (Nat.unpair_right_le _) <| Nat.unpair_right_le _
      have : c.unpair.2 < e + 1 :=
        Nat.lt_succ.mpr <| le_trans (Nat.unpair_right_le _) <| le_trans (Nat.unpair_right_le _) <| Nat.unpair_right_le _
      do
        let ⟨n', p⟩ ← ofNatAux c.unpair.1
        let ⟨n'', q⟩ ← ofNatAux c.unpair.2
        if h : n' = n ∧ n'' = n then return ⟨n, (p.bcast h.1) ⋎ q.bcast h.2⟩ else none
    | 6 =>
      have : c < e + 1 :=
        Nat.lt_succ.mpr <| le_trans (Nat.unpair_right_le _) <| Nat.unpair_right_le _
      do
        let ⟨n', p⟩ ← ofNatAux c
        if h : n' = n + 1 then return ⟨n, ∀' (p.bcast h)⟩ else none
    | 7 =>
      have : c < e + 1 :=
        Nat.lt_succ.mpr <| le_trans (Nat.unpair_right_le _) <| Nat.unpair_right_le _
      do
        let ⟨n', p⟩ ← ofNatAux c
        if h : n' = n + 1 then return ⟨n, ∃' (p.bcast h)⟩ else none
    | _ => none

lemma ofNat_toNat : {n : ℕ} → ∀ p : Semiformula L ξ n, ofNatAux (toNat p) = some ⟨n, p⟩
  | _, p ⋏ q => by {
    simp only [toNat, ofNatAux, Nat.unpair_pair, ofNat_toNat p, ofNat_toNat q, Option.pure_def,
      Option.bind_eq_bind, Option.some_bind, and_true, ↓reduceDite, Option.some.injEq,
      Sigma.mk.inj_iff, true_and]
    simp only [bcast]
    congr
   }

end Semiformula
-/

end LO.FirstOrder
