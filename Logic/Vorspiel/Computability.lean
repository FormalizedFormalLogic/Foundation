import Logic.Vorspiel.Vorspiel

variable {α : Type u}

namespace Nat

def predO : ℕ → Option ℕ
  | 0     => none
  | n + 1 => some n

@[simp] lemma predO_zero : predO 0 = none := rfl

@[simp] lemma predO_succ {n} : predO (n + 1) = some n := rfl

end Nat

namespace Encodable

variable {α : Type _} [Encodable α]

@[reducible] def encodeDecode (α : Type _) [Encodable α] (e : ℕ) : Option ℕ := (encode (decode e : Option α)).predO

lemma encodeDecode_of_none {e : ℕ} (h : decode (α := α) e = none) : encodeDecode α e = none := by simp[encodeDecode, h]

lemma encodeDecode_of_some {e : ℕ} {a : α} (h : decode e = some a) : encodeDecode α e = some (encode a) := by simp[encodeDecode, h]

variable {α : Type u_1} {P : α → Prop} [Encodable α] [DecidablePred P]

lemma encode_decode_subtype (e : ℕ) :
    encode (decode (α := {x // P x}) e) = encode ((decode (α := α) e).bind (fun a => if P a then some a else none)) := by
  rcases h : decode (α := α) e with (_ | s) <;> simp[*, decode, decodeSubtype, encode, encodeSubtype]
  { by_cases hs : P s <;> simp[hs] }

end Encodable

namespace Primrec

open Encodable
variable {α : Type _} [Primcodable α]

lemma nat_predO : Primrec Nat.predO :=
  (Primrec.nat_casesOn₁ none (Primrec.option_some_iff.mpr Primrec.id)).of_eq (by intro n; cases n <;> simp)

class Uniform {α : Type u} (β : α → Type v) [Primcodable α] [∀ a, Primcodable (β a)] where
  uniformly_prim : Primrec₂ (fun a n => Encodable.encode (Encodable.decode (α := β a) n))

namespace Uniform

variable {α : Type u} {β γ : α → Type v} [Primcodable α] [(a : α) → Primcodable (β a)]

lemma _root_.Primrec₂.encodeDecode [Uniform β] : Primrec₂ (fun a e => encodeDecode (β a) e) :=
  (nat_predO.comp $ Uniform.uniformly_prim.comp fst snd)

instance {β : Type _} [Primcodable β] : Uniform (Vector β) where
  uniformly_prim := by
    have e : ∀ n e, encode ((decode (α := List β) e).bind (fun a => if a.length = n then some a else none)) =
        encode (decode (α := Vector β n) e) := by intro n e; rw[Encodable.encode_decode_subtype]
    have : Primrec₂ (fun n e => encode ((decode (α := List β) e).bind (fun a => if a.length = n then some a else none))) :=
      Primrec.encode.comp
        (Primrec.option_bind
          (Primrec.decode.comp snd)
          (Primrec.ite (Primrec.eq.comp (Primrec.list_length.comp snd) (fst.comp fst)) (Primrec.option_some.comp snd) (const none)))
    exact this.of_eq e

attribute [-instance] Encodable.finPi

instance {β : Type _} [Primcodable β] : Uniform (Fin · → β) where
  uniformly_prim := by
    have : ∀ n e, encode (decode (α := Vector β n) e) = encode (decode (α := Fin n → β) e) := by
      intro n e; simp[Encodable.decode_ofEquiv]
      rcases h : decode (α := Vector β n) e with (_ | v) <;> simp
      { have : ∀ b : Fin n → β, encode b = encode ((Equiv.vectorEquivFin β n).symm b) := 
          fun b => encode_ofEquiv (Equiv.vectorEquivFin β n).symm b
        simpa using (this (Equiv.vectorEquivFin β n v)).symm }
    exact uniformly_prim.of_eq this

attribute [instance] Encodable.finPi

instance : Uniform Fin where
  uniformly_prim := by
    have : ∀ e n, encode (decode (α := Fin n) e) = if e < n then e + 1 else 0 := by
      intro e n
      by_cases h : e < n <;> simp[h, Encodable.decode_ofEquiv, decode, decodeSubtype, Encodable.encode_ofEquiv, encode, encodeSubtype]
    exact (Primrec.ite (Primrec.nat_lt.comp snd fst) (Primrec.succ.comp $ snd) (Primrec.const 0)).of_eq (by simp[this])

instance {β : α → Type _} {γ : α → Type _} [(a : α) → Primcodable (β a)] [(a : α) → Primcodable (γ a)] [Uniform β] [Uniform γ] :
    Uniform (fun a => β a × γ a) where
  uniformly_prim := by
    have e : ∀ a e, encode ((encodeDecode (β a) e.unpair.1).bind $ fun b => (encodeDecode (γ a) e.unpair.2).map $ fun c => Nat.pair b c) =
        encode (decode (α := β a × γ a) e) := by
      intro a e; simp
      rcases hb : (decode e.unpair.1 : Option (β a)) with (_ | b) <;> simp[*, encodeDecode_of_none, encodeDecode_of_some]
      rcases hc : (decode e.unpair.2 : Option (γ a)) with (_ | c) <;> simp[*, encodeDecode_of_none, encodeDecode_of_some hb]
      { simp[encodeDecode_of_some hc] }
    have : Primrec₂ (fun a e => encode ((encodeDecode (β a) e.unpair.1).bind $ fun b => (encodeDecode (γ a) e.unpair.2).map $ fun c => Nat.pair b c) : α → ℕ → ℕ) :=
      Primrec.encode.comp
        (Primrec.option_bind
          (Primrec₂.encodeDecode.comp fst (fst.comp $ Primrec.unpair.comp $ snd))
          (Primrec.option_map
            (Primrec₂.encodeDecode.comp (fst.comp $ fst) (snd.comp $ Primrec.unpair.comp $ snd.comp $ fst))
            (Primrec₂.natPair.comp₂ (snd.comp $ fst) Primrec₂.right)))
    exact this.of_eq e

instance {β : Type _} [Primcodable β] : Uniform (fun (_ : α) => β) where
  uniformly_prim := (nat_iff.mpr Primcodable.prim).comp snd

end Uniform

open Encodable
variable {α : Type u} {β : α → Type v} [Primcodable α] [(a : α) → Primcodable (β a)]

instance sigma [Uniform β] : Primcodable (Sigma β) where
  prim := by
    have e : ∀ e, encode ((decode e.unpair.1 : Option α).bind (fun a => (encodeDecode (β a) e.unpair.2).map (Nat.pair (encode a)))) =
        encode (decode e : Option (Sigma β)) := by
      intro e; simp
      rcases ha : (decode e.unpair.1 : Option α) with (_ | a) <;> simp
      rcases hb : (decode e.unpair.2 : Option (β a)) with (_ | b) <;> simp[*, encodeDecode_of_none]
      { simp[encodeDecode_of_some hb] }
    have p₁ : Primrec (fun e => decode e.unpair.1 : ℕ → Option α) := (Primrec.decode.comp $ fst.comp $ Primrec.unpair)
    have p₂ : Primrec₂ (fun e a => (encodeDecode (β a) e.unpair.2).map (Nat.pair (encode a)) : ℕ → α → Option ℕ) :=
      (Primrec.option_map
        (Primrec₂.encodeDecode.comp snd (snd.comp $ Primrec.unpair.comp $ fst))
        (Primrec₂.natPair.comp₂ (Primrec.encode.comp $ snd.comp $ fst) Primrec₂.right))
    exact Primrec.nat_iff.mp ((Primrec.encode.comp $ p₁.option_bind p₂).of_eq e)

end Primrec

