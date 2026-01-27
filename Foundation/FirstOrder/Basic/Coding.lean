module

public import Foundation.FirstOrder.Basic.BinderNotation

@[expose] public section

namespace LO.FirstOrder

variable {L : Language} [(k : ℕ) → Encodable (L.Func k)]

variable {ξ : Type*} [Encodable ξ]

open Encodable
namespace Semiterm

def toNat {n : ℕ} : Semiterm L ξ n → ℕ
  |                        #z => Nat.pair 0 z + 1
  |                        &x => Nat.pair 1 (encode x) + 1
  | func (arity := arity) f v => (Nat.pair 2 <| Nat.pair arity <| Nat.pair (encode f) <| Matrix.vecToNat fun i ↦ toNat (v i)) + 1

def ofNat (n : ℕ) : ℕ → Option (Semiterm L ξ n)
  |     0 => none
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
            Nat.lt_succ_iff.mpr
              <| le_trans (le_of_lt <| Nat.lt_of_eq_natToVec hv i)
              <| le_trans (Nat.unpair_right_le _)
              <| le_trans (Nat.unpair_right_le _)
              <| Nat.unpair_right_le _
          ofNat n (v' i)).map fun v : Fin arity → Semiterm L ξ n ↦
        func f v
      | none => none
    | _ => none

lemma ofNat_toNat {n : ℕ} : ∀ t : Semiterm L ξ n, ofNat n (toNat t) = some t
  |       #z => by simp [toNat, ofNat]
  |       &x => by simp [toNat, ofNat]
  | func f v => by
      suffices (Matrix.getM fun i ↦ ofNat n (v i).toNat) = some v by
        simp only [toNat, ofNat, Nat.unpair_pair]
        rw [Nat.unpair_pair, Nat.unpair_pair, Nat.unpair_pair, Nat.natToVec_vecToNat]
        simpa
      have : (fun i ↦ ofNat n (toNat (v i))) = (fun i ↦ pure (v i)) := funext <| fun i ↦ ofNat_toNat (v i)
      simp [this]

instance encodable : Encodable (Semiterm L ξ n) where
  encode := toNat
  decode := ofNat n
  encodek := ofNat_toNat

lemma encode_eq_toNat (t : Semiterm L ξ n) : encode t = toNat t := rfl

lemma toNat_func {k} (f : L.Func k) (v : Fin k → Semiterm L ξ n) :
    toNat (func f v) = (Nat.pair 2 <| Nat.pair k <| Nat.pair (encode f) <| Matrix.vecToNat fun i ↦ toNat (v i)) + 1 := rfl

@[simp] lemma encode_emb (t : ClosedSemiterm L n) : encode (Rew.emb t : Semiterm L ξ n) = encode t := by
  simp only [encode_eq_toNat]
  induction t
  · simp [toNat]
  · contradiction
  · simp [Rew.func, toNat_func, *]

end Semiterm

namespace Semiformula

variable [(k : ℕ) → Encodable (L.Rel k)]

def toNat {n : ℕ} : Semiformula L ξ n → ℕ
  |  rel (arity := arity) R v => (Nat.pair 0 <| arity.pair <| (encode R).pair <| Matrix.vecToNat fun i ↦ encode (v i)) + 1
  | nrel (arity := arity) R v => (Nat.pair 1 <| arity.pair <| (encode R).pair <| Matrix.vecToNat fun i ↦ encode (v i)) + 1
  |                         ⊤ => (Nat.pair 2 0) + 1
  |                         ⊥ => (Nat.pair 3 0) + 1
  |                     φ ⋏ ψ => (Nat.pair 4 <| φ.toNat.pair ψ.toNat) + 1
  |                     φ ⋎ ψ => (Nat.pair 5 <| φ.toNat.pair ψ.toNat) + 1
  |                      ∀' φ => (Nat.pair 6 <| φ.toNat) + 1
  |                      ∃' φ => (Nat.pair 7 <| φ.toNat) + 1

def ofNat : (n : ℕ) → ℕ → Option (Semiformula L ξ n)
  | _,     0 => none
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
      have : c.unpair.1 < e + 1 := Nat.lt_succ_iff.mpr <| le_trans (Nat.unpair_left_le _) <| Nat.unpair_right_le _
      have : c.unpair.2 < e + 1 := Nat.lt_succ_iff.mpr <| le_trans (Nat.unpair_right_le _) <| Nat.unpair_right_le _
      do
        let φ ← ofNat n c.unpair.1
        let ψ ← ofNat n c.unpair.2
        return φ ⋏ ψ
    | 5 =>
      have : c.unpair.1 < e + 1 := Nat.lt_succ_iff.mpr <| le_trans (Nat.unpair_left_le _) <| Nat.unpair_right_le _
      have : c.unpair.2 < e + 1 := Nat.lt_succ_iff.mpr <| le_trans (Nat.unpair_right_le _) <| Nat.unpair_right_le _
      do
        let φ ← ofNat n c.unpair.1
        let ψ ← ofNat n c.unpair.2
        return φ ⋎ ψ
    | 6 =>
      have : c < e + 1 := Nat.lt_succ_iff.mpr <| Nat.unpair_right_le _
      do
        let φ ← ofNat (n + 1) c
        return ∀' φ
    | 7 =>
      have : c < e + 1 := Nat.lt_succ_iff.mpr <| Nat.unpair_right_le _
      do
        let φ ← ofNat (n + 1) c
        return ∃' φ
    | _ => none

lemma ofNat_toNat {n : ℕ} : ∀ φ : Semiformula L ξ n, ofNat n (toNat φ) = some φ
  |  rel R v => by
    simp only [toNat, ofNat, Nat.unpair_pair]
    rw [Nat.unpair_pair, Nat.unpair_pair]
    simp
  | nrel R v => by
    simp only [toNat, ofNat, Nat.unpair_pair]
    rw [Nat.unpair_pair, Nat.unpair_pair]
    simp
  |        ⊤ => by simp [toNat, ofNat]
  |        ⊥ => by simp [toNat, ofNat]
  |    φ ⋎ ψ => by simp [toNat, ofNat, ofNat_toNat φ, ofNat_toNat ψ]
  |    φ ⋏ ψ => by simp [toNat, ofNat, ofNat_toNat φ, ofNat_toNat ψ]
  |     ∀' φ => by simp [toNat, ofNat, ofNat_toNat φ]
  |     ∃' φ => by simp [toNat, ofNat, ofNat_toNat φ]

instance encodable : Encodable (Semiformula L ξ n) where
  encode := toNat
  decode := ofNat n
  encodek := ofNat_toNat

open Encodable

lemma encode_eq_toNat
    (φ : Semiformula L ξ n) : encode φ = toNat φ := rfl

lemma encode_rel {arity : ℕ} (R : L.Rel arity) (v : Fin arity → Semiterm L ξ n) :
    encode (Semiformula.rel R v) = (Nat.pair 0 <| arity.pair <| (encode R).pair <| Matrix.vecToNat fun i ↦ encode (v i)) + 1 := rfl

lemma encode_nrel {arity : ℕ} (R : L.Rel arity) (v : Fin arity → Semiterm L ξ n) :
    encode (Semiformula.nrel R v) = (Nat.pair 1 <| arity.pair <| (encode R).pair <| Matrix.vecToNat fun i ↦ encode (v i)) + 1 := rfl

lemma encode_verum : encode (⊤ : Semiformula L ξ n) = (Nat.pair 2 0) + 1 := rfl

lemma encode_falsum : encode (⊥ : Semiformula L ξ n) = (Nat.pair 3 0) + 1 := rfl

lemma encode_and (φ ψ : Semiformula L ξ n) : encode (φ ⋏ ψ) = (Nat.pair 4 <| φ.toNat.pair ψ.toNat) + 1 := rfl

lemma encode_or (φ ψ : Semiformula L ξ n) : encode (φ ⋎ ψ) = (Nat.pair 5 <| φ.toNat.pair ψ.toNat) + 1 := rfl

lemma encode_all (φ : Semiformula L ξ (n + 1)) : encode (∀' φ) = (Nat.pair 6 <| φ.toNat) + 1 := rfl

lemma encode_ex (φ : Semiformula L ξ (n + 1)) : encode (∃' φ) = (Nat.pair 7 <| φ.toNat) + 1 := rfl

@[simp] lemma encode_emb (σ : Semisentence L n) :
    encode (Rewriting.emb σ : Semiformula L ξ n) = encode σ := by
  induction σ using rec' <;>
    simp [coe_rel, coe_nrel,
      encode_rel, encode_nrel, encode_verum, encode_falsum, encode_and, encode_or, encode_all, encode_ex,
      ← encode_eq_toNat, *]

@[simp] lemma encode_inj_sentence {σ : Semisentence L n} {φ : Semiformula L ξ n} :
    encode φ = encode σ ↔ φ = Rewriting.emb σ := by
  constructor
  · intro h; apply encode_inj.mp; simpa
  · rintro rfl; simp

@[simp] lemma encode_inj_sentence' {σ : Semisentence L n} {φ : Semiformula L ξ n} :
    encode σ = encode φ ↔ φ = Rewriting.emb σ := by rw [←encode_inj_sentence, eq_comm]

end Semiformula

section

variable {L : Language} [L.Encodable]

instance Semiterm.countable [Countable ξ] : Countable (Semiterm L ξ n) := by
  have : Encodable ξ := Encodable.ofCountable ξ
  exact Encodable.countable

instance Semiformula.countable [Countable ξ] : Countable (Semiformula L ξ n) := by
  have : Encodable ξ := Encodable.ofCountable ξ
  exact Encodable.countable

end

end LO.FirstOrder

end
