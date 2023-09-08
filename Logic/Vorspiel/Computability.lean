import Logic.Vorspiel.Vorspiel

variable {α : Type u}

namespace Nat

def predO : ℕ → Option ℕ
  | 0     => none
  | n + 1 => some n

@[simp] lemma predO_zero : predO 0 = none := rfl

@[simp] lemma predO_succ {n} : predO (n + 1) = some n := rfl

end Nat

namespace List

def range2 (n m : ℕ) : List (ℕ × ℕ) := (·, ·) <$> range n <*> range m

@[simp] lemma mem_range2_iff {n m i j : ℕ} : (i, j) ∈ range2 n m ↔ i < n ∧ j < m := by simp[range2, seq_eq_bind]

end List

namespace Encodable

variable {α : Type _} [Encodable α]

@[reducible] def encodeDecode (α : Type _) [Encodable α] (e : ℕ) : Option ℕ := (encode (decode e : Option α)).predO

lemma encodeDecode_of_none {e : ℕ} (h : decode (α := α) e = none) : encodeDecode α e = none := by simp[encodeDecode, h]

lemma encodeDecode_of_some {e : ℕ} {a : α} (h : decode e = some a) : encodeDecode α e = some (encode a) := by simp[encodeDecode, h]

lemma decode_encodeDecode : encodeDecode α e = some i → ∃ a : α, decode i = some a := by
  simp[encodeDecode]
  cases h : (decode e : Option α) <;> simp
  rintro rfl; simp

variable {α : Type u_1} {P : α → Prop} [Encodable α] [DecidablePred P]

lemma encode_decode_subtype (e : ℕ) :
    encode (decode (α := {x // P x}) e) = encode ((decode (α := α) e).bind (fun a => if P a then some a else none)) := by
  rcases h : decode (α := α) e with (_ | s) <;> simp[*, decode, decodeSubtype, encode, encodeSubtype]
  { by_cases hs : P s <;> simp[hs] }

lemma encodeDecode_subtype' (e : ℕ) :
    encodeDecode {x // P x} e = (decode (α := α) e).bind (fun a => if P a then some (encode a) else none) := by
  simp[encodeDecode, encode_decode_subtype]
  rcases h : (decode e : Option α) with (_ | a) <;> simp
  { by_cases ha : P a <;> simp[*] }

lemma encodeDecode_subtype (e : ℕ) :
    encodeDecode {x // P x} e = (encodeDecode α e).bind (fun c => if ∃ a ∈ (decode c : Option α), P a then some c else none) := by
  simp[encodeDecode_subtype', encodeDecode]
  rcases (decode e : Option α) <;> simp

-- todo: delete
lemma encode_decode_ofEquiv {β} (e : β ≃ α) (n : ℕ) :
    haveI : Encodable β := Encodable.ofEquiv α e
    encode (decode (α := β) n) = encode (decode (α := α) n) := by
  simp[Encodable.decode_ofEquiv e]
  rcases h : (decode n : Option α) with (_ | ⟨a⟩) <;> simp
  { exact @Encodable.encode_none _ (Encodable.ofEquiv α e) }
  { have := @Encodable.encode_some _ (Encodable.ofEquiv α e) (e.symm a); rw[this];
    simpa using Encodable.encode_ofEquiv e (e.symm a) }

-- todo: delete
lemma encode_decode_ofEquiv_prim {α β} [Primcodable α] (e : β ≃ α) (n : ℕ) :
    haveI : Primcodable β := Primcodable.ofEquiv α e
    encode (decode (α := β) n) = encode (decode (α := α) n) := encode_decode_ofEquiv e n

lemma encodeDecode_ofEquiv {β} (e : β ≃ α) :
    haveI : Encodable β := Encodable.ofEquiv α e
    encodeDecode β = encodeDecode α := by
  funext n; simp[encodeDecode, Encodable.decode_ofEquiv e]
  rcases h : (decode n : Option α) with (_ | ⟨a⟩) <;> simp
  { simp[@Encodable.encode_none _ (Encodable.ofEquiv α e)] }
  { have := @Encodable.encode_some _ (Encodable.ofEquiv α e) (e.symm a); rw[this];
    simpa using Encodable.encode_ofEquiv e (e.symm a) } 

lemma encode_decode_eq_encodeDecode : encode (decode e : Option α) = encode (encodeDecode α e) := by
  simp[encodeDecode]; cases (decode e : Option α) <;> simp

lemma encode_decode_sigma_s {β : α → Type _} [(a : α) → Encodable (β a)] {e : ℕ} :
    encodeDecode ((a : α) × β a) e = ((decode e.unpair.1 : Option α).bind $ fun a => (encodeDecode (β a) e.unpair.2).map $ fun b => (encode a).pair b) := by
  rcases ha : (decode e.unpair.1 : Option α) with (_ | a) <;> simp[*, encodeDecode]
  { rcases (decode e.unpair.2 : Option (β a)) with (_ | b) <;> simp[*] }

lemma encode_decode_sigma_of_none {β : α → Type _} [(a : α) → Encodable (β a)] {e : ℕ} (h : (decode e.unpair.1 : Option α) = none) :
    encodeDecode (α := (a : α) × β a) e = none := by
  simp[encodeDecode, h]

lemma encode_decode_sigma_of_some {β : α → Type _} [(a : α) → Encodable (β a)] {e : ℕ} {a : α} (h : decode e.unpair.1 = some a) :
    encodeDecode ((a : α) × β a) e = (encodeDecode (β a) e.unpair.2).map fun b => (encode a).pair b := by
  simp[encodeDecode, h]; rcases h : decode e.unpair.2 with (_ | b) <;> simp

end Encodable

namespace Primcodable

open Encodable

instance fintypeArrow [DecidableEq α] [Fintype α] [Encodable α] {β : Type _} [Primcodable β] : Primcodable (α → β) :=
    Primcodable.ofEquiv (Fin (Fintype.card α) → β) (Equiv.arrowCongr Encodable.fintypeEquivFin (Equiv.refl _))

lemma ofEquiv_toEncodable {α : Type _} {β : Type _} [Primcodable α] (e : β ≃ α) :
  (ofEquiv α e).toEncodable = Encodable.ofEquiv α e := rfl

end Primcodable

namespace Primrec

lemma nat_strong_rec' [Primcodable α] [Primcodable σ] (f : α → ℕ → σ) {g : α × ℕ → List σ → Option σ} (hg : Primrec₂ g)
  (H : ∀ a n, g (a, n) ((List.range n).map (f a)) = some (f a n)) : Primrec₂ f := by
  let g' : α → List σ → Option σ := fun a l => g (a, l.length) l
  have : Primrec₂ g' := hg.comp₂ (pair fst (list_length.comp snd)) Primrec₂.right
  exact nat_strong_rec f this (by simpa using H)

lemma nat_strong_rec'2 [Primcodable α] [Primcodable σ] (f : α → ℕ × ℕ → σ) {g : α × (ℕ × ℕ) → List σ → Option σ} (hg : Primrec₂ g)
  (H : ∀ a n m, g (a, (n, m)) ((List.range (n.pair m)).map (fun i => f a i.unpair)) = some (f a (n, m))) : Primrec₂ f := by
  let g' : α × ℕ → List σ → Option σ := fun (a, n) => g (a, n.unpair)
  have : Primrec₂ g' := hg.comp₂ (pair (fst.comp fst) (unpair.comp $ snd.comp fst)) Primrec₂.right
  have : Primrec₂ (fun a n => f a n.unpair : α → ℕ → σ) := nat_strong_rec' (fun a n => f a n.unpair : α → ℕ → σ) this (fun a n => by simpa using H a n.unpair.1 n.unpair.2)
  have : Primrec₂ (fun a p => (fun a n => f a n.unpair : α → ℕ → σ) a (p.1.pair p.2) : α → ℕ × ℕ → σ) :=
    this.comp₂ Primrec₂.left (Primrec₂.natPair.comp (fst.comp snd) (snd.comp snd))
  exact this.of_eq (by simp)

lemma nat_strong_rec'2' [Primcodable σ] (f : ℕ → ℕ → σ) {g : ℕ × ℕ → List σ → Option σ} (hg : Primrec₂ g)
  (H : ∀ n m, g (n, m) ((List.range (n.pair m)).map (fun i => f i.unpair.1 i.unpair.2)) = some (f n m)) : Primrec₂ f := by
  have : Primrec₂ (fun p => g p.2 : Unit × (ℕ × ℕ) → List σ → Option σ) := hg.comp (snd.comp fst) snd
  have := nat_strong_rec'2 (fun _ i => f i.1 i.2 : Unit → ℕ × ℕ → σ) this (by simpa using H)
  have : Primrec₂ (fun n m => (fun _ i => f i.1 i.2 : Unit → ℕ × ℕ → σ) () (n, m)) := this.comp (const ()) Primrec.id
  exact this.of_eq (by simp)

lemma option_list_mapM' [Primcodable α] [Primcodable β] [Primcodable γ]
  {f : α → List β} {g : α → β → Option γ} (hf : Primrec f) (hg : Primrec₂ g) : Primrec (fun a => (f a).mapM' (g a)) := by
  have : Primrec₂ (fun a p => (g a p.1).bind $ fun c => p.2.2.map $ fun l => c :: l : α → β × List β × Option (List γ) → Option (List γ)) :=
    Primrec.option_bind (hg.comp fst (fst.comp snd)) (Primrec.option_map (snd.comp $ snd.comp $ snd.comp fst) (Primrec.list_cons.comp₂ (snd.comp fst) Primrec₂.right))
  let F : α → Option (List γ) := fun a => List.recOn (f a) (some []) (fun b _ ih => (g a b).bind $ fun c => ih.map $ fun l => c :: l)
  have : Primrec F := Primrec.list_rec hf (const (some [] : Option (List γ))) this
  have e : ∀ (k : β → Option γ) (bs : List β),
    List.recOn bs (some [] : Option (List γ)) (fun b _ ih => (k b).bind $ fun c => ih.map $ fun l => c :: l) = bs.mapM' k := by
    intro k bs
    induction bs <;> simp[Option.pure_eq_some, Option.bind_eq_bind, *]
    { simp[Option.map_eq_bind, Function.comp] }
  exact this.of_eq (by simp[e])

open Encodable
variable {α : Type _} [Primcodable α]

lemma nat_predO : Primrec Nat.predO :=
  (Primrec.nat_casesOn₁ none (Primrec.option_some_iff.mpr Primrec.id)).of_eq (by intro n; cases n <;> simp)

protected lemma encodeDecode : Primrec (fun e => encodeDecode α e) := nat_predO.comp (Primrec.encode.comp Primrec.decode)

class Uniform {α : Type u} (β : α → Type v) [Primcodable α] [∀ a, Primcodable (β a)] where
  uniformly_prim : Primrec₂ (fun a n => Encodable.encode (Encodable.decode (α := β a) n))

class CardUniform {α : Type u} (β : α → Type v) [∀ a, Fintype (β a)] [Primcodable α] [∀ a, Primcodable (β a)] where
  card_prim : Primrec fun a => Fintype.card (β a)

namespace Uniform

variable {α : Type u} {β γ : α → Type v} [Primcodable α] [(a : α) → Primcodable (β a)]

lemma _root_.Primrec₂.encodeDecode_u [Uniform β] : Primrec₂ (fun a e => encodeDecode (β a) e) :=
  (nat_predO.comp $ Uniform.uniformly_prim.comp fst snd)

def ofEncodeDecode (h : Primrec₂ (fun a n => encodeDecode (β a) n)) : Uniform β where
  uniformly_prim := (Primrec.encode.comp₂ h).of_eq (by simp[encode_decode_eq_encodeDecode])

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

instance fintypeArrow [DecidableEq α] [Fintype α] {β : Type _} [Primcodable β] : Primcodable (α → β) :=
    Primcodable.ofEquiv (Fin (Fintype.card α) → β) (Equiv.arrowCongr fintypeEquivFin (Equiv.refl _))

instance {γ : α → Type _} [(a : α) → Fintype (γ a)] [(a : α) → DecidableEq (γ a)] [(a : α) → Primcodable (γ a)] [CardUniform γ]
  {β : Type _} [Primcodable β] : Uniform (γ · → β) where
  uniformly_prim := by
    simp[Encodable.encode_decode_ofEquiv_prim]
    exact (Uniform.uniformly_prim (β := Vector β)).comp₂ (CardUniform.card_prim.comp fst) Primrec₂.right

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
          (Primrec₂.encodeDecode_u.comp fst (fst.comp $ Primrec.unpair.comp $ snd))
          (Primrec.option_map
            (Primrec₂.encodeDecode_u.comp (fst.comp $ fst) (snd.comp $ Primrec.unpair.comp $ snd.comp $ fst))
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
        (Primrec₂.encodeDecode_u.comp snd (snd.comp $ Primrec.unpair.comp $ fst))
        (Primrec₂.natPair.comp₂ (Primrec.encode.comp $ snd.comp $ fst) Primrec₂.right))
    exact Primrec.nat_iff.mp ((Primrec.encode.comp $ p₁.option_bind p₂).of_eq e)

@[simp] lemma sigma_toEncodable_eq [Uniform β] : (sigma : Primcodable (Sigma β)).toEncodable = Sigma.encodable := rfl

end Primrec

namespace Encodable

open Primcodable Primrec.Uniform
attribute [-instance] Encodable.finPi Encodable.fintypeArrowOfEncodable

lemma decode_list {β : Type _} [Encodable β] :
    (e : ℕ) → (decode e : Option (List β)) = (Denumerable.ofNat (List ℕ) e).mapM' (decode : ℕ → Option β)
  | 0     => by simp; rfl
  | e + 1 =>
    have : e.unpair.2 < e + 1 := Nat.lt_succ_of_le e.unpair_right_le
    by  simp; rcases h : (decode e.unpair.1 : Option β) with (_ | b) <;> simp[seq_eq_bind, Option.bind_eq_bind]
        have := decode_list (β := β) (e.unpair.2)
        simp[this, Option.pure_eq_some, Option.map_eq_bind, Function.comp]

lemma encodeDecode_list {β : Type _} [Encodable β] (e : ℕ) :
    encodeDecode (List β) e = ((Denumerable.ofNat (List ℕ) e).mapM' (encodeDecode β : ℕ → Option ℕ)).map encode := by
  simp[encodeDecode, decode_list]
  generalize hr : (Denumerable.ofNat (List ℕ) e) = r
  induction' r with rh rt ih generalizing e <;> simp[Option.pure_eq_some, Option.bind_eq_bind, Option.map_bind']
  rcases hb : (decode rh) with (_ | b) <;> simp
  rcases hbs : (mapM' decode rt) with (_ | bs) <;> simp
  { have : mapM' (fun e => (encode (decode e : Option β)).predO) rt = none
    { simp[encodeDecode, List.mapM'_eq_none_iff] at hbs ⊢
      rcases hbs with ⟨a, ha, da⟩
      exact ⟨a, ha, by simp[da]⟩  }
    simp[this] }
  { have ih : some (encode bs) = (mapM' (encodeDecode β) rt).map encode := by simpa[hbs] using ih (encode rt) (by simp)
    suffices : some ((encode b).pair (encode bs) + 1) = ((mapM' (encodeDecode β) rt).map encode).map ((encode b).pair · + 1)
    { simp[this]; simp[Option.map_eq_bind, Function.comp] }
    simp[←ih] }

lemma encodeDecode_finArrow {β : Type _} [Encodable β] {e : ℕ} :
    encodeDecode (Fin k → β) e =
    (((Denumerable.ofNat (List ℕ) e).mapM' (encodeDecode β)).bind $ fun l' => if l'.length = k then some (encode l') else none) := by
  rw[encodeDecode_ofEquiv, encodeDecode_subtype, encodeDecode_list]; simp
  rcases h : (mapM' (encodeDecode β) (Denumerable.ofNat (List ℕ) e)) with (_ | l) <;> simp
  rcases hbs : decode (encode l) with (_ | bs)
  { simp[decode_list] at hbs
    have : ∃ a ∈ l, (decode a : Option β) = none := by simpa[List.mapM'_eq_none_iff] using hbs
    rcases this with ⟨a, hal, ha⟩
    have : ∃ a', encodeDecode β a' = some a := List.mapM'_mem_inversion h hal
    rcases this with ⟨a', ha'⟩
    simpa [ha] using decode_encodeDecode ha' }
  { have : bs.length = l.length := by
      simp[decode_list] at hbs; exact List.length_mapM' hbs
    simp[this] }

lemma encodeDecode_fintypeArrow (α : Type _) (β : Type _) [DecidableEq α] [Fintype α] [Primcodable α] [Primcodable β] (e : ℕ) :
    encodeDecode (α → β) e =
    (((Denumerable.ofNat (List ℕ) e).mapM' (encodeDecode β)).bind $ fun l' => if l'.length = Fintype.card α then some (encode l') else none) := by
  simp[Primcodable.ofEquiv_toEncodable, fintypeArrow]; rw[encodeDecode_ofEquiv]
  exact encodeDecode_finArrow (β := β)

end Encodable

namespace WType

attribute [-instance] WType.instEncodableWType

open Encodable Primrec
variable {α : Type _} {β : α → Type _} [(a : α) → Fintype (β a)] [(a : α) → DecidableEq (β a)] [(a : α) → Primcodable (β a)] [Primcodable α] [Primrec.CardUniform β]

@[reducible]
private def WType' {α : Type _} (β : α → Type _) [(a : α) → Fintype (β a)] [(a : α) → Primcodable (β a)] (n : ℕ) :=
  { t : WType β // t.depth ≤ n }

def WType'.depth' : WType' β n → Fin (n + 1) := fun ⟨t, h⟩ => ⟨t.depth, Iff.mpr Nat.lt_succ h⟩

def WType'.equiv_zero : WType' β 0 ≃ Empty where
  toFun := fun ⟨x, h⟩ => False.elim (not_lt_of_ge h $ WType.depth_pos _)
  invFun := by rintro ⟨⟩
  left_inv := fun ⟨x, h⟩ => False.elim (not_lt_of_ge h $ WType.depth_pos _)
  right_inv := by rintro ⟨⟩

def WType'.equiv_succ : WType' β (n + 1) ≃ (Σ a : α, β a → WType' β n) where
  toFun := fun ⟨t, h⟩ => by rcases t with ⟨a, f⟩; exact ⟨a, fun b => ⟨f b, by simp[WType.depth] at h; exact h b⟩⟩
  invFun := fun ⟨a, f⟩ => ⟨WType.mk a (fun b => (f b).val), by simp[depth]; intro b; exact (f b).property⟩
  left_inv := fun ⟨t, h⟩ => by rcases t with ⟨a, f⟩; simp
  right_inv := fun ⟨a, f⟩ => by simp

def WType'.primcodable_zero : Primcodable (WType' β 0) := Primcodable.ofEquiv _ WType'.equiv_zero

def WType'.primcodable_succ (n) (i : Primcodable (WType' β n)) : Primcodable (WType' β (n + 1)) := Primcodable.ofEquiv _ WType'.equiv_succ

instance WType'.primcodable (n : ℕ) : Primcodable (WType' β n) := Nat.rec WType'.primcodable_zero WType'.primcodable_succ n

--instance : Encodable (WType β) := by
--  haveI h' : ∀ n, Primcodable (WType' β n) := fun n => Nat.rec WType'.primcodable_zero WType'.primcodable_succ n
--  let f : WType β → Σ n, WType' β n := fun t => ⟨t.depth, ⟨t, le_rfl⟩⟩
--  let finv : (Σn, WType' β n) → WType β := fun p => p.2.1
--  have : ∀ t, finv (f t) = t := fun t => rfl
--  exact Encodable.ofLeftInverse f finv this

attribute [-instance] Subtype.encodable Encodable.fintypeArrowOfEncodable

lemma testeq {α : Type _} {a b c d : α} : a = b → b = c → c = d → a = d := by
  intro hab hbc hcd; simp[hab, hbc, hcd]

lemma WType'.encodeDecode_EType' (s e) :
    encodeDecode (WType' β s) e =
    Nat.casesOn s (encodeDecode (WType' β 0) e)
      (fun s => (decode e.unpair.1 : Option α).bind
        $ fun a => (((Denumerable.ofNat (List ℕ) e.unpair.2).mapM' (encodeDecode (WType' β s))).bind
          $ fun l => if l.length = Fintype.card (β a) then some (encode l) else none).map
            $ fun b => (encode a).pair b) := by
  rcases s with (_ | s)
  · simp
  · have := Encodable.decode_sigma_val (γ := fun a => β a → WType' β s) e
    simp[WType'.primcodable, primcodable_succ, Primcodable.ofEquiv_toEncodable]
    rw[encodeDecode_ofEquiv equiv_succ, encode_decode_sigma_s]
    rcases ha : (decode e.unpair.1 : Option α) with (_ | a)
    · simp
    · simp[encode_decode_ofEquiv, encodeDecode_fintypeArrow (β a) (WType' β s)]

variable (β)

private def strongRecE {γ : Type _} [Encodable γ] (zero : ℕ → γ) (succ : α → List γ → Option γ) : ℕ × ℕ → List (Option γ) → Option γ := fun (s, e) ih =>
  Nat.casesOn s (zero e)
    (fun s => (decode e.unpair.1 : Option α).bind
      $ fun a => (((Denumerable.ofNat (List ℕ) e.unpair.2).mapM' (fun c => ih.getI (s.pair c))).bind
        $ fun l => if l.length = Fintype.card (β a) then some l else none).bind
          $ fun v => succ a v)

@[reducible]
private def g : ℕ × ℕ → List (Option ℕ) → Option ℕ := fun (s, e) ih =>
  Nat.casesOn s (encodeDecode (WType' β 0) e)
    (fun s => (decode e.unpair.1 : Option α).bind
      $ fun a => (((Denumerable.ofNat (List ℕ) e.unpair.2).mapM' (fun c => ih.getI (s.pair c))).bind
        $ fun l => if l.length = Fintype.card (β a) then some (encode l) else none).map
          $ fun v => (encode a).pair v)

variable {β}

private lemma gh : g β (s, e) ((List.range (s.pair e)).map (fun i => encodeDecode (WType' β i.unpair.1) i.unpair.2)) = encodeDecode (WType' β s) e := by
  simp[WType'.encodeDecode_EType' s e, g]
  rcases s with (_ | s) <;> simp
  have :
    mapM' (fun c =>
            List.getI
              (List.map (fun i => encodeDecode (WType.WType' β i.unpair.1) i.unpair.2) (List.range ((s + 1).pair e)))
            (s.pair c))
          (Denumerable.ofNat (List ℕ) e.unpair.2) =
    mapM' (encodeDecode (WType.WType' β s)) (Denumerable.ofNat (List ℕ) e.unpair.2) :=
    List.mapM'_eq_mapM'_of_eq _ (by
      { intro c hc
        have : s.pair c < (s + 1).pair e := by
          have : c < e.unpair.2 := Denumerable.lt_of_mem_list _ _ hc
          exact lt_of_lt_of_le (Nat.pair_lt_pair_right s this) (Nat.pair_le_pair_of_le (Nat.le_succ s) (Nat.unpair_right_le e))
        simp[List.getI_map_range _ this]; rw[Nat.unpair_pair s c] })
  rw[this]

/-
-- 以下の証明はチェックに異常な時間がかかる（なぜ？）：
example [Primcodable α] : Primrec₂ (fun a b => Nat.pair (Encodable.encode a.snd) b : (ℕ × ℕ × ℕ) × α → ℕ → ℕ) :=
  Primrec₂.natPair.comp (Primrec.encode.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd

-- 以下はうまく行く
example [Primcodable α] : Primrec₂ (fun a b => Nat.pair (Encodable.encode a.snd) b : (ℕ × ℕ × ℕ) × α → ℕ → ℕ) :=
  by apply Primrec₂.natPair.comp (Primrec.encode.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd
-/

private lemma g_primrec : Primrec₂ (g β) :=
  have h₁ : Primrec₂ (fun a b => Nat.pair (encode a.snd) b : (((ℕ × ℕ) × List (Option ℕ)) × ℕ) × α → ℕ → ℕ) := by 
    apply Primrec₂.natPair.comp (Primrec.encode.comp (snd.comp fst)) snd
  have h₂ : Primrec₂ (fun a l => if l.length = Fintype.card (β a.snd) then some (encode l) else none
    : (((ℕ × ℕ) × List (Option ℕ)) × ℕ) × α → List ℕ → Option ℕ) := by
    apply Primrec.ite (Primrec.eq.comp (list_length.comp snd) (CardUniform.card_prim.comp $ snd.comp fst))
      (Primrec.option_some.comp $ Primrec.encode.comp snd) (const none)
  have h₃ : Primrec (fun a => mapM' (fun c => a.1.1.2.getI (a.1.2.pair c)) (Denumerable.ofNat (List ℕ) a.1.1.1.2.unpair.2)
    : (((ℕ × ℕ) × List (Option ℕ)) × ℕ) × α → Option (List ℕ)) := by
    apply option_list_mapM'
      (by apply (Primrec.ofNat _).comp $ snd.comp $ Primrec.unpair.comp $ snd.comp $ fst.comp $ fst.comp $ fst)
      (by apply Primrec.list_getI.comp (snd.comp $ fst.comp $ fst.comp $ fst) (Primrec₂.natPair.comp (snd.comp $ fst.comp fst) snd))
  by apply Primrec.nat_casesOn (fst.comp fst) (Primrec.encodeDecode.comp (snd.comp fst))
      (by apply
            Primrec.option_bind (Primrec.decode.comp $ fst.comp $ Primrec.unpair.comp $ snd.comp $ fst.comp fst)
            (by apply Primrec.option_map (by apply Primrec.option_bind (by apply h₃) (by apply h₂)) h₁))

lemma WType'.uniform : Primrec.Uniform (WType' β) :=
  have : Primrec₂ (fun p t => some (g β p t)) := option_some.comp g_primrec
  Uniform.ofEncodeDecode (nat_strong_rec'2' _ this (by simp[gh]))

end WType

