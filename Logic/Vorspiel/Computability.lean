import Logic.Vorspiel.Vorspiel

attribute [-instance] WType.instEncodableWType Encodable.finPi Encodable.fintypeArrowOfEncodable

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

def toVector (n : ℕ) : List α → Option (Vector α n) := fun l => if h : l.length = n then some ⟨l, h⟩ else none

end List

namespace Encodable

variable {ι : Type _} [Fintype ι] [DecidableEq ι] [Encodable ι]

def fintypeArrowEquivFinArrow : (ι → α) ≃ (Fin (Fintype.card ι) → α) :=
  Equiv.arrowCongr fintypeEquivFin (Equiv.refl α)

def fintypeArrowEquivFinArrow' {k} (hk : Fintype.card ι = k) : (ι → α) ≃ (Fin k → α) :=
  hk ▸ fintypeArrowEquivFinArrow

def fintypeArrowEquivVector : (ι → α) ≃ (Vector α (Fintype.card ι)) :=
  fintypeArrowEquivFinArrow.trans (Equiv.vectorEquivFin α (Fintype.card ι)).symm

lemma fintypeArrowEquivFinArrow_eq (f : ι → α) : fintypeArrowEquivFinArrow f = fun i => f (fintypeEquivFin.symm i) := by rfl

@[simp] lemma fintypeArrowEquivFinArrow_app (f : ι → α) (i) : fintypeArrowEquivFinArrow f i = f (fintypeEquivFin.symm i) := by rfl

@[simp] lemma fintypeArrowEquivFinArrow_symm_app (v : Fin (Fintype.card ι) → α) :
    fintypeArrowEquivFinArrow.symm v i = v (fintypeEquivFin i) := by rfl

@[simp] lemma fintypeArrowEquivFinArrow'_app {k} (hk : Fintype.card ι = k) (f : ι → α) (i) :
  fintypeArrowEquivFinArrow' hk f i = f (fintypeEquivFin.symm $ i.cast hk.symm) := by rcases hk with rfl; rfl

@[simp] lemma fintypeArrowEquivFinArrow'_symm_app {k} (hk : Fintype.card ι = k) (v : Fin k → α) :
    (fintypeArrowEquivFinArrow' hk).symm v i = v ((fintypeEquivFin i).cast hk) := by rcases hk with rfl; rfl

@[simp] lemma cast_fintypeEquivFin_fin {k : ℕ} (i : Fin k) : (fintypeEquivFin i).cast (Fintype.card_fin _) = i := by
  ext
  simp [Encodable.fintypeEquivFin, Fin.cast_eq_cast',
    ←Fin.castIso_eq_cast, Fin.encodable, List.Nodup.getEquivOfForallMemList,
    Encodable.sortedUniv, Encodable.encode']
  convert List.indexOf_finRange i
  exact Fin.sort_univ

@[simp] lemma val_fintypeEquivFin_fin {k : ℕ} (i : Fin k) : (fintypeEquivFin i).val = i.val :=
  congr_arg Fin.val (cast_fintypeEquivFin_fin i)

@[simp] lemma fintypeEquivFin_false : fintypeEquivFin false = 0 := rfl

@[simp] lemma fintypeEquivFin_true : fintypeEquivFin true = 1 := rfl

@[simp] lemma fintypeEquivFin_symm_cast_fin {k : ℕ} (i : Fin k) :
    fintypeEquivFin.symm (i.cast (Fintype.card_fin _).symm) = i := by
  have := congr_arg (fun j => fintypeEquivFin.symm (j.cast (Fintype.card_fin _).symm)) (cast_fintypeEquivFin_fin i)
  simpa[-cast_fintypeEquivFin_fin] using this.symm

@[simp] lemma fintypeArrowEquivFinArrow'_symm_app_fin_arrow {k} (hk) (v : Fin k → α) :
    (fintypeArrowEquivFinArrow' hk).symm v = v := by funext i; simp[hk]

@[simp] lemma fintypeArrowEquivVector_app (f : ι → α) : (fintypeArrowEquivVector f).get i = f (fintypeEquivFin.symm i) := by
  simp[fintypeArrowEquivVector, Equiv.vectorEquivFin]

@[simp] lemma fintypeArrowEquivVector_symm_app (v : Vector α (Fintype.card ι)) :
    (fintypeArrowEquivVector.symm v) i = v.get ((fintypeEquivFin i)) := by rfl

@[simp] lemma fintypeArrowEquivFinArrow_fintypeEquivFin (f : Fin (Fintype.card ι) → α) :
    fintypeArrowEquivFinArrow (fun i => f (fintypeEquivFin i)) = f := by funext i; simp

def toFinArrowOpt (f : ι → Option α) : Option (ι → α) :=
  (Matrix.toOptionVec (fintypeArrowEquivFinArrow f)).map fintypeArrowEquivFinArrow.symm

@[simp] lemma toFinArrowOpt_eq_none_iff {f : ι → Option α} : toFinArrowOpt f = none ↔ ∃ i, f i = none := by
  simp[toFinArrowOpt, fintypeArrowEquivFinArrow]; constructor
  { rintro ⟨i, hi⟩; exact ⟨_, hi⟩ }; { rintro ⟨i, hi⟩; exact ⟨fintypeEquivFin i, by simp[hi]⟩  }

@[simp] lemma toFinArrowOpt_eq_some_iff {f : ι → Option α} {g} : toFinArrowOpt f = some g ↔ ∀ i, f i = some (g i) := by
  simp[toFinArrowOpt, fintypeArrowEquivFinArrow]; constructor
  { rintro ⟨a, ha, rfl⟩; simp; intro i
    simpa using ha (fintypeEquivFin i) }
  { intro hf; exact ⟨fun i => g (fintypeEquivFin.symm i), by { simp[hf]; funext i; simp }⟩ }

@[simp] lemma vectorEquivFin_symm_val (f : Fin n → β) : ((Equiv.vectorEquivFin β n).symm f).toList = List.ofFn f := by
  ext i b; simp[Equiv.vectorEquivFin, Vector.ofFn]

-- todo: move to Vorspiel
@[simp] def getI_ofFn [Inhabited α] {n} (f : Fin n → α) (i : Fin n) : (List.ofFn f).getI i = f i := by simp[List.getI_eq_get]

end Encodable

namespace Encodable

variable {α : Type _} [Encodable α]

@[reducible] def encodeDecode (α : Type _) [Encodable α] (e : ℕ) : Option ℕ := (encode (decode e : Option α)).predO

lemma encodeDecode_of_none {e : ℕ} (h : decode (α := α) e = none) : encodeDecode α e = none := by simp[encodeDecode, h]

lemma encodeDecode_of_some {e : ℕ} {a : α} (h : decode e = some a) : encodeDecode α e = some (encode a) := by simp[encodeDecode, h]

lemma encodeDecode_eq_encode_map_decode {e : ℕ} : encodeDecode α e = (decode e : Option α).map encode := by
  simp[encodeDecode]; rcases (decode e) <;> simp

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

lemma encodeDecode_ofEquiv (α) [Encodable α] {β} (e : β ≃ α) :
    haveI : Encodable β := Encodable.ofEquiv α e
    encodeDecode β = encodeDecode α := by
  funext n; simp[encodeDecode, Encodable.decode_ofEquiv e]
  rcases h : (decode n : Option α) with (_ | ⟨a⟩) <;> simp
  { simp[@Encodable.encode_none _ (Encodable.ofEquiv α e)] }
  { have := @Encodable.encode_some _ (Encodable.ofEquiv α e) (e.symm a); rw[this];
    simpa using Encodable.encode_ofEquiv e (e.symm a) } 

lemma encodeDecode_ofEquiv_prim (α) {β} [Primcodable α] (e : β ≃ α) :
    haveI : Primcodable β := Primcodable.ofEquiv α e
    encodeDecode β = encodeDecode α := encodeDecode_ofEquiv α e

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

lemma ofEquiv_toEncodable {α : Type _} {β : Type _} [Primcodable α] (e : β ≃ α) :
  (ofEquiv α e).toEncodable = Encodable.ofEquiv α e := rfl

instance fintypeArrow [DecidableEq α] [Fintype α] [Encodable α] (β : Type _) [Primcodable β] : Primcodable (α → β) :=
    Primcodable.ofEquiv (Fin (Fintype.card α) → β) fintypeArrowEquivFinArrow

end Primcodable

namespace Primrec

open Encodable
variable {α : Type _} {β : Type _} {γ : Type _} {σ : Type _} [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

lemma decode_iff {α : Type _} {σ : Type _} [Primcodable α] [Primcodable σ] {f : α → σ} :
    Primrec (fun n => (Encodable.decode n).map f) ↔ Primrec f :=
  ⟨fun h => by simp[Primrec]; exact Primrec.nat_iff.mp (Primrec.encode.comp h),
   fun h => option_map Primrec.decode (h.comp₂ Primrec₂.right)⟩

lemma decode₂2_iff {α : Type _} {β : Type _} {σ : Type _} [Primcodable α] [Primcodable β] [Primcodable σ] {f : α → β → σ} :
    Primrec₂ (fun a n => (Encodable.decode n).map (f a)) ↔ Primrec₂ f :=
  ⟨fun h => by simp[Primrec₂, Primrec, Option.map_bind', Function.comp]
               exact Primrec.nat_iff.mp (Primrec.encode.comp $ option_bind (Primrec.decode.comp $ fst.comp Primrec.unpair)
                 (h.comp₂ Primrec₂.right (snd.comp $ Primrec.unpair.comp fst))),
   fun h => option_map (Primrec.decode.comp snd) (h.comp₂ (fst.comp fst) Primrec₂.right)⟩

section Equiv

variable {α α₁ α₂ σ τ : Type _} [Primcodable α] [Primcodable α₁] [Primcodable α₂] [Primcodable σ] [Primcodable τ] 

lemma _root_.Primrec₂.of_equiv_iff {β} (e : β ≃ α) {f : σ → τ → β} :
  haveI := Primcodable.ofEquiv α e
  (Primrec₂ fun a b => e (f a b)) ↔ Primrec₂ f := by simp[Primrec₂, Primrec.of_equiv_iff]

lemma of_equiv_iff' {β} (e : β ≃ α) {f : β → σ} :
    haveI := Primcodable.ofEquiv α e
    (Primrec fun b => (f (e.symm b))) ↔ Primrec f :=
  letI := Primcodable.ofEquiv α e
  ⟨fun h => (h.comp (of_equiv (e := e))).of_eq (by simp),
   fun h => h.comp Primrec.of_equiv_symm⟩

lemma _root_.Primrec₂.of_equiv_iff'2 {β} (e : β ≃ α₂) {f : α₁ → β → σ} :
    haveI := Primcodable.ofEquiv α₂ e
    Primrec₂ (fun a b => (f a (e.symm b))) ↔ Primrec₂ f :=
  letI := Primcodable.ofEquiv α₂ e
  ⟨fun h => (h.comp fst ((of_equiv (e := e)).comp snd)).of_eq (by simp),
   fun h => h.comp fst (of_equiv_symm.comp snd)⟩

end Equiv

lemma nat_strong_rec' (f : α → ℕ → σ) {g : α × ℕ → List σ → Option σ} (hg : Primrec₂ g)
  (H : ∀ a n, g (a, n) ((List.range n).map (f a)) = some (f a n)) : Primrec₂ f := by
  let g' : α → List σ → Option σ := fun a l => g (a, l.length) l
  have : Primrec₂ g' := hg.comp₂ (pair fst (list_length.comp snd)) Primrec₂.right
  exact nat_strong_rec f this (by simpa using H)

lemma nat_strong_rec'2 (f : α → ℕ × ℕ → σ) {g : α × (ℕ × ℕ) → List σ → Option σ} (hg : Primrec₂ g)
  (H : ∀ a n m, g (a, (n, m)) ((List.range (n.pair m)).map (fun i => f a i.unpair)) = some (f a (n, m))) : Primrec₂ f := by
  let g' : α × ℕ → List σ → Option σ := fun (a, n) => g (a, n.unpair)
  have : Primrec₂ g' := hg.comp₂ (pair (fst.comp fst) (unpair.comp $ snd.comp fst)) Primrec₂.right
  have : Primrec₂ (fun a n => f a n.unpair : α → ℕ → σ) := nat_strong_rec' (fun a n => f a n.unpair : α → ℕ → σ) this (fun a n => by simpa using H a n.unpair.1 n.unpair.2)
  have : Primrec₂ (fun a p => (fun a n => f a n.unpair : α → ℕ → σ) a (p.1.pair p.2) : α → ℕ × ℕ → σ) :=
    this.comp₂ Primrec₂.left (Primrec₂.natPair.comp (fst.comp snd) (snd.comp snd))
  exact this.of_eq (by simp)

lemma nat_strong_rec'2' (f : ℕ → ℕ → σ) {g : ℕ × ℕ → List σ → Option σ} (hg : Primrec₂ g)
  (H : ∀ n m, g (n, m) ((List.range (n.pair m)).map (fun i => f i.unpair.1 i.unpair.2)) = some (f n m)) : Primrec₂ f := by
  have : Primrec₂ (fun p => g p.2 : Unit × (ℕ × ℕ) → List σ → Option σ) := hg.comp (snd.comp fst) snd
  have := nat_strong_rec'2 (fun _ i => f i.1 i.2 : Unit → ℕ × ℕ → σ) this (by simpa using H)
  have : Primrec₂ (fun n m => (fun _ i => f i.1 i.2 : Unit → ℕ × ℕ → σ) () (n, m)) := this.comp (const ()) Primrec.id
  exact this.of_eq (by simp)

lemma option_list_mapM'
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

lemma to₂' {f : α → β → σ} (hf : Primrec (fun p => f p.1 p.2 : α × β → σ)) : Primrec₂ f := hf

lemma of_list_decode_eq_some_cons {a : α} {as : List α} {e : ℕ} : decode e = some (a :: as) →
    decode e.pred.unpair.1 = some a ∧ decode e.pred.unpair.2 = some as := by
  rcases e with (_ | e) <;> simp
  rcases (decode e.unpair.1) with (_ | a) <;> simp[seq_eq_bind_map, Option.bind_eq_bind]
  rcases (decode e.unpair.2) with (_ | as) <;> simp[seq_eq_bind_map, Option.bind_eq_bind]
  rintro rfl rfl; simp

section zipWith

@[reducible] private def decodeZipWithRec (f : σ → α × β → γ) : σ × ℕ → List (Option $ List γ) → Option (List γ) := fun p IH =>
  (decode p.2 : Option (List α × List β)).bind
    $ fun l => l.1.casesOn (some [])
      $ fun a _ => l.2.casesOn (some [])
        $ fun b _ => (IH.get? (encode (p.2.unpair.1.pred.unpair.2, p.2.unpair.2.pred.unpair.2))).map
          $ fun cs => f p.1 (a, b) :: cs.iget

private lemma casesOn_eq_uncurry (l : σ → List α) (f : σ → β) (g : σ → α → List α → β) :
    (fun x => @List.casesOn α (fun _ => β) (l x) (f x) (g x)) =
    (fun x => List.casesOn (l x) (f x) (fun a as => (Function.uncurry $ g x) (a, as))) := by rfl

private lemma decodeZipWithRec_primrec {f : σ → α × β → γ} (hf : Primrec₂ f) : Primrec₂ (decodeZipWithRec f) := by
  exact option_bind (Primrec.decode.comp $ snd.comp fst)
    (by apply to₂'; rw[casesOn_eq_uncurry]
        apply list_casesOn (fst.comp snd) (Primrec.const _)
          (by apply to₂'; simp[Function.uncurry]; rw[casesOn_eq_uncurry]
              apply list_casesOn (snd.comp $ snd.comp fst) (const _)
                (by simp[Function.uncurry]
                    apply option_map (list_get?.comp (snd.comp $ fst.comp $ fst.comp fst)
                      (Primrec₂.natPair.comp
                        (snd.comp $ unpair.comp $ pred.comp $ fst.comp $ unpair.comp $ snd.comp $ fst.comp $ fst.comp $ fst.comp fst)
                        (snd.comp $ unpair.comp $ pred.comp $ snd.comp $ unpair.comp $ snd.comp $ fst.comp $ fst.comp $ fst.comp fst)))
                      (list_cons.comp₂
                        (hf.comp₂
                          (fst.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ $ Primrec₂.left)
                          (Primrec₂.pair.comp₂
                            (fst.comp₂ $ snd.comp₂ $ fst.comp₂ Primrec₂.left)
                            (fst.comp₂ $ snd.comp₂ Primrec₂.left)))
                        (option_iget.comp₂ Primrec₂.right)))))

lemma list_zipWith_param {f : σ → α × β → γ} (hf : Primrec₂ f) :
    Primrec₂ (fun x p => List.zipWith (fun a b => f x (a, b)) p.1 p.2 : σ → List α × List β → List γ) := by
  have h : Primrec₂ (fun x p => some (decodeZipWithRec f x p)) := option_some.comp (decodeZipWithRec_primrec hf)
  let F : σ → ℕ → Option (List γ) :=
    fun x n => (decode n : Option (List α × List β)).bind
      $ fun p => List.zipWith (fun a b => f x (a, b)) p.1 p.2
  have : Primrec₂ F := nat_strong_rec' F h (fun x e => by
    simp[decodeZipWithRec]
    rcases has : (decode (e.unpair.1)) with (_ | as) <;> simp
    rcases hbs : (decode (e.unpair.2)) with (_ | bs) <;> simp
    rcases as with (_ | ⟨a, as⟩) <;> simp
    rcases bs with (_ | ⟨b, bs⟩) <;> simp
    have : e.unpair.1.pred.unpair.2.pair e.unpair.2.pred.unpair.2 < e
    { have lt₁ : e.unpair.1.pred.unpair.2 < e.unpair.1 :=
        lt_of_le_of_lt (Nat.unpair_right_le _) (Nat.pred_lt (fun eq => by simp[eq] at has))
      have lt₂ : e.unpair.2.pred.unpair.2 < e.unpair.2 :=
        lt_of_le_of_lt (Nat.unpair_right_le _) (Nat.pred_lt (fun eq => by simp[eq] at hbs))
      simpa using lt_trans (Nat.pair_lt_pair_left e.unpair.2.pred.unpair.2 lt₁) (Nat.pair_lt_pair_right e.unpair.1 lt₂) }
    rw[List.get?_range this]; simp[of_list_decode_eq_some_cons has, of_list_decode_eq_some_cons hbs])
  exact decode₂2_iff.mp (this.of_eq $ fun x e => by simp only [Option.map_eq_bind]; rfl)

lemma list_zipWith {f : α → β → γ} (hf : Primrec₂ f) : Primrec₂ (List.zipWith f) :=
  (list_zipWith_param (hf.comp₂ (fst.comp₂ Primrec₂.right) (snd.comp₂ Primrec₂.right))).comp₂
    (Primrec₂.const ())
    Primrec.id.to₂

end zipWith

open Encodable
variable {α : Type _} [Primcodable α]

lemma nat_predO : Primrec Nat.predO :=
  (Primrec.nat_casesOn₁ none (Primrec.option_some_iff.mpr Primrec.id)).of_eq (by intro n; cases n <;> simp)

protected lemma encodeDecode : Primrec (fun e => encodeDecode α e) := nat_predO.comp (Primrec.encode.comp Primrec.decode)

lemma list_sup [SemilatticeSup α] [OrderBot α] (hsup : Primrec₂ (Sup.sup : α → α → α)) : Primrec (List.sup : List α → α) := by
  have e : ∀ l : List α, l.sup = l.foldr Sup.sup ⊥ := by
    intro l; induction' l with a as ih <;> simp[sup_eq_max, *]
  have : Primrec (fun l => l.foldr Sup.sup ⊥ : List α → α) :=
    list_foldr Primrec.id (const _) (hsup.comp₂ (fst.comp₂ Primrec₂.right) (snd.comp₂ Primrec₂.right))
  exact this.of_eq (by simp[e])

end Primrec

class UniformlyPrimcodable {α : Type u} (β : α → Type v) [Primcodable α] [(a : α) → Primcodable (β a)] : Prop where
  uniformly_prim : Primrec₂ (fun a n => Encodable.encode (Encodable.decode (α := β a) n))

class PrimrecCard {α : Type u} (β : α → Type v) [∀ a, Fintype (β a)] [Primcodable α] [(a : α) → Primcodable (β a)] : Prop where
  card_prim : Primrec fun a => Fintype.card (β a)

namespace UniformlyPrimcodable

open Encodable Primcodable Primrec
variable {α : Type u} {β γ : α → Type v} [Primcodable α] [(a : α) → Primcodable (β a)] [(a : α) → Primcodable (γ a)]

lemma _root_.Primrec₂.encodeDecode_u [UniformlyPrimcodable β] : Primrec₂ (fun a e => encodeDecode (β a) e) :=
  (nat_predO.comp $ UniformlyPrimcodable.uniformly_prim.comp fst snd)

def ofEncodeDecode (h : Primrec₂ (fun a n => encodeDecode (β a) n)) : UniformlyPrimcodable β where
  uniformly_prim := (Primrec.encode.comp₂ h).of_eq (by simp[encode_decode_eq_encodeDecode])

def subtype {β} [Primcodable β] {R : α → β → Prop} [(a : α) → (b : β) → Decidable (R a b)] (hR : PrimrecRel R) :
    haveI : (a : α) → Primcodable { x // R a x } := fun a => Primcodable.subtype (hR.comp (const a) Primrec.id)
    UniformlyPrimcodable (fun a => { x // R a x }) :=
  have : Primrec₂ (fun a e => encode ((decode e : Option β).bind $ fun b => if R a b then some b else none)) :=
    (Primrec.encode.comp $
      option_bind (Primrec.decode.comp snd) (Primrec.ite (hR.comp (fst.comp fst) snd) (Primrec.option_some.comp snd) (const none)))
  @UniformlyPrimcodable.mk _ _ _ (fun a => Primcodable.subtype (hR.comp (const a) Primrec.id))
    (this.of_eq $ fun a e => by
      simp[decode, Primcodable.toEncodable, Primcodable.subtype, decodeSubtype]
      rcases (decode e) with (_ | b) <;> simp
      by_cases hr : R a b <;> simp[hr, Encodable.Subtype.encode_eq])

instance vector (β : Type _) [Primcodable β] : UniformlyPrimcodable (Vector β) where
  uniformly_prim := by
    have e : ∀ n e, encode ((decode (α := List β) e).bind (fun a => if a.length = n then some a else none)) =
        encode (decode (α := Vector β n) e) := by intro n e; rw[Encodable.encode_decode_subtype]
    have : Primrec₂ (fun n e => encode ((decode (α := List β) e).bind (fun a => if a.length = n then some a else none))) :=
      Primrec.encode.comp
        (Primrec.option_bind
          (Primrec.decode.comp snd)
          (Primrec.ite (Primrec.eq.comp (Primrec.list_length.comp snd) (fst.comp fst)) (Primrec.option_some.comp snd) (const none)))
    exact this.of_eq e

instance finArrow (β : Type _) [Primcodable β] : UniformlyPrimcodable (Fin · → β) where
  uniformly_prim := by
    have : ∀ n e, encode (decode (α := Vector β n) e) = encode (decode (α := Fin n → β) e) := by
      intro n e; simp[Encodable.decode_ofEquiv]
      rcases h : decode (α := Vector β n) e with (_ | v) <;> simp
      { have : ∀ b : Fin n → β, encode b = encode ((Equiv.vectorEquivFin β n).symm b) := 
          fun b => encode_ofEquiv (Equiv.vectorEquivFin β n).symm b
        simpa using (this (Equiv.vectorEquivFin β n v)).symm }
    exact uniformly_prim.of_eq this

instance fintypeArrow (γ : α → Type _) (β : Type _)
  [(a : α) → Fintype (γ a)] [(a : α) → DecidableEq (γ a)] [(a : α) → Primcodable (γ a)] [PrimrecCard γ] [Primcodable β] :
    UniformlyPrimcodable (γ · → β) := ofEncodeDecode
  (by { have : Primrec₂ (fun a n => encodeDecode (Fin (Fintype.card (γ a)) → β) n) :=
          (Primrec₂.encodeDecode_u (β := (Fin · → β))).comp (PrimrecCard.card_prim.comp fst) snd
        exact this.of_eq (fun a b =>
          by { simp[Primcodable.ofEquiv_toEncodable, Encodable.encodeDecode_ofEquiv]
               rw[Encodable.encodeDecode_ofEquiv (Fin (Fintype.card (γ a)) → β)] }) })

instance fin : UniformlyPrimcodable Fin where
  uniformly_prim := by
    have : ∀ e n, encode (decode (α := Fin n) e) = if e < n then e + 1 else 0 := by
      intro e n
      by_cases h : e < n <;> simp[h, Encodable.decode_ofEquiv, decode, decodeSubtype, Encodable.encode_ofEquiv, encode, encodeSubtype]
    exact (Primrec.ite (Primrec.nat_lt.comp snd fst) (Primrec.succ.comp $ snd) (Primrec.const 0)).of_eq (by simp[this])

instance prod (β : α → Type _) (γ : α → Type _)
  [(a : α) → Primcodable (β a)] [(a : α) → Primcodable (γ a)] [UniformlyPrimcodable β] [UniformlyPrimcodable γ] :
    UniformlyPrimcodable (fun a => β a × γ a) where
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

instance const {β : Type _} [Primcodable β] : UniformlyPrimcodable (fun (_ : α) => β) where
  uniformly_prim := (nat_iff.mpr Primcodable.prim).comp snd

end UniformlyPrimcodable

namespace Primcodable

open Encodable UniformlyPrimcodable Primrec
variable {α : Type u} {β : α → Type v} [Primcodable α] [(a : α) → Primcodable (β a)]

instance sigma [UniformlyPrimcodable β] : Primcodable (Sigma β) where
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

@[simp] lemma sigma_toEncodable_eq [UniformlyPrimcodable β] : (sigma : Primcodable (Sigma β)).toEncodable = Sigma.encodable := rfl

end Primcodable

namespace Encodable

open Primcodable Primrec UniformlyPrimcodable
variable {β : Type _} [Encodable β]

lemma decode_list :
    (e : ℕ) → (decode e : Option (List β)) = (Denumerable.ofNat (List ℕ) e).mapM' (decode : ℕ → Option β)
  | 0     => by simp; rfl
  | e + 1 =>
    have : e.unpair.2 < e + 1 := Nat.lt_succ_of_le e.unpair_right_le
    by  simp; rcases h : (decode e.unpair.1 : Option β) with (_ | b) <;> simp[seq_eq_bind, Option.bind_eq_bind]
        have := decode_list (e.unpair.2)
        simp[this, Option.pure_eq_some, Option.map_eq_bind, Function.comp]

lemma decode_vector (e : ℕ) :
    (decode (α := Vector β k) e) = (decode (α := List β) e).bind (List.toVector k) := by
  simp[decode, decodeSubtype, List.toVector]

lemma decode_finArrow (β : Type _) [Primcodable β] (e : ℕ) :
    (decode (α := Fin k → β) e) = (decode (α := List β) e).bind (fun l => (l.toVector k).map (Equiv.vectorEquivFin β k)) := by
  simp[Primcodable.ofEquiv_toEncodable, Encodable.decode_ofEquiv]
  rw[decode_vector];
  rcases (decode e : Option (List β)) with (_ | bs) <;> simp

lemma decode_fintypeArrow (ι : Type _) [Fintype ι] [Primcodable ι] [DecidableEq ι] (β : Type _) [Primcodable β] (e : ℕ) :
    (decode (α := ι → β) e) = (decode (α := List β) e).bind (fun l => (l.toVector (Fintype.card ι)).map fintypeArrowEquivVector.symm) := by
  simp[Primcodable.ofEquiv_toEncodable, Encodable.decode_ofEquiv]
  rw[Encodable.decode_ofEquiv, decode_vector]; simp
  rcases (decode e : Option (List β)) with (_ | bs) <;> simp; { rfl }

lemma encode_list (l : List β) :
    encode l = encode (l.map encode) := by induction l <;> simp[*]

lemma encode_vector {n} (v : Vector β n) :
    encode v = encode v.toList := Encodable.Subtype.encode_eq v

lemma encode_finArrow {n} (f : Fin n → β) :
    encode f = encode (List.ofFn f) := by simp[finArrow]; rw[Encodable.encode_ofEquiv, encode_vector]; simp

lemma encode_fintypeArrow (ι : Type _) [Fintype ι] [Primcodable ι] [DecidableEq ι] (β : Type _) [Primcodable β] (f : ι → β) :
    encode f = encode (fintypeArrowEquivFinArrow f) := by simp[Primcodable.ofEquiv_toEncodable]; rw[Encodable.encode_ofEquiv]

lemma encode_fintypeArrow' (ι : Type _) [Fintype ι] [Primcodable ι] [DecidableEq ι] (β : Type _) [Primcodable β] (f : ι → β) :
    encode f = encode (fun i => encode (f i)) := by
  simp[encode_fintypeArrow, encode_finArrow, encode_list (List.ofFn $ fintypeArrowEquivFinArrow f)]
  funext i; simp

lemma encode_fintypeArrow_isEmpty
  (ι : Type _) [Fintype ι] [Primcodable ι] [DecidableEq ι] [IsEmpty ι] (β : Type _) [Primcodable β] (f : ι → β) :
    encode f = 0 := by
  have : Fintype.card ι = 0 := Fintype.card_eq_zero
  simp[encode_fintypeArrow, encode_finArrow, this]

lemma encode_fintypeArrow_card_one
  {ι : Type _} [Fintype ι] [Primcodable ι] [DecidableEq ι] (hι : Fintype.card ι = 1) (β : Type _) [Primcodable β] (f : ι → β) (i) :
    encode f = encode [f i] := by
  have : Subsingleton ι := Fintype.card_le_one_iff_subsingleton.mp (by simp[hι])
  simp[encode_fintypeArrow, encode_finArrow, hι, (this.allEq · i)]

lemma encode_fintypeArrow_card_two
  {ι : Type _} [Fintype ι] [Primcodable ι] [DecidableEq ι] (hι : Fintype.card ι = 2) (β : Type _) [Primcodable β] (f : ι → β) :
    encode f = encode [f (fintypeEquivFin.symm ((0 : Fin 2).cast hι.symm)), f (fintypeEquivFin.symm ((1 : Fin 2).cast hι.symm))] := by
  simp[encode_fintypeArrow, encode_finArrow, hι]; exact ⟨by congr, by congr⟩

end Encodable

namespace WType

open Encodable Primrec Primcodable UniformlyPrimcodable
variable {α : Type _} {β : α → Type _}
  [Primcodable α] [(a : α) → Fintype (β a)] [(a : α) → DecidableEq (β a)] [(a : α) → Primcodable (β a)] [PrimrecCard β]

def elimOpt (γ : Type _) (fγ : (Σ a : α, β a → γ) → Option γ) : WType β → Option γ
  | ⟨a, f⟩ => (toFinArrowOpt (fun b => elimOpt γ fγ (f b))).bind fun g => fγ ⟨a, g⟩

def SubWType {α : Type _} (β : α → Type _)
  [(a : α) → Fintype (β a)] [(a : α) → Primcodable (β a)] (n : ℕ) := { t : WType β // t.depth ≤ n }

namespace SubWType

def mk (a : α) (f : β a → SubWType β s) : SubWType β (s + 1) := ⟨⟨a, fun i => (f i).val⟩, by simp[depth]; intro b; exact (f b).property ⟩

abbrev ofWType (w : WType β) (n) (h : w.depth ≤ n) : SubWType β n := ⟨w, h⟩

@[simp] lemma depth_le (t : SubWType β n) : t.val.depth ≤ n := t.property

def elim' (γ : Type*) (fγ : (Σ a : α, β a → γ) → γ) (s) : SubWType β s → γ := fun ⟨t, _⟩ => t.elim γ fγ 

lemma elim_const {w₁ : SubWType β s₁} {w₂ : SubWType β s₂} (h : w₁.val = w₂.val) (γ) (fγ : (Σ a : α, β a → γ) → γ) : 
    elim' γ fγ s₁ w₁ = elim' γ fγ s₂ w₂ := by
  rcases w₁ with ⟨w, hw₁⟩
  rcases w₂ with ⟨w, hw₂⟩
  simp at h; rcases h with rfl
  simp[elim']

def equiv_zero : SubWType β 0 ≃ Empty where
  toFun := fun ⟨x, h⟩ => False.elim (not_lt_of_ge h $ WType.depth_pos _)
  invFun := by rintro ⟨⟩
  left_inv := fun ⟨x, h⟩ => False.elim (not_lt_of_ge h $ WType.depth_pos _)
  right_inv := by rintro ⟨⟩

def equiv_succ : SubWType β (n + 1) ≃ (Σ a : α, β a → SubWType β n) where
  toFun := fun ⟨t, h⟩ => by rcases t with ⟨a, f⟩; exact ⟨a, fun b => ⟨f b, by simp[WType.depth] at h; exact h b⟩⟩
  invFun := fun ⟨a, f⟩ => ofWType (WType.mk a (fun b => (f b).val)) (n + 1) (by simp[depth])
  left_inv := fun ⟨t, h⟩ => by rcases t with ⟨a, f⟩; simp
  right_inv := fun ⟨a, f⟩ => by simp

def primcodable_zero : Primcodable (SubWType β 0) := Primcodable.ofEquiv _ equiv_zero

def primcodable_succ (n) (_ : Primcodable (SubWType β n)) : Primcodable (SubWType β (n + 1)) := Primcodable.ofEquiv _ equiv_succ

instance _root_.Primcodable.SubWType (n : ℕ) : Primcodable (SubWType β n) := Nat.rec SubWType.primcodable_zero SubWType.primcodable_succ n

@[simp] lemma decode_zero : (decode e : Option (SubWType β 0)) = none := by
  rcases (decode e) with (_ | w)
  · rfl
  · exact Empty.elim (equiv_zero w)

lemma decode_succ :
  decode (α := SubWType β (s + 1)) e =
  ((decode (α := α) e.unpair.1).bind
    $ fun a => (decode (α := List (SubWType β s)) e.unpair.2).bind
      $ fun l => (l.toVector (Fintype.card (β a))).map
        $ fun v => ofWType ⟨a, fun b => (fintypeArrowEquivVector.symm v b).val⟩ _ (by simp[depth, Equiv.vectorEquivFin])) :=
  calc
    decode (α := SubWType β (s + 1)) e
      = Option.map (fun x => ofWType ⟨x.fst, fun b => (x.snd b).val⟩ (s + 1) (by simp[depth]))
        (decode e : Option ((a : α) × (β a → SubWType β s))) :=
      by simp[Primcodable.SubWType, primcodable_succ, Primcodable.ofEquiv_toEncodable]
         rw[Encodable.decode_ofEquiv equiv_succ, equiv_succ]; simp
    _ = ((decode (Nat.unpair e).fst : Option α).bind
          $ fun a => (decode (α := (β a → SubWType β s)) (Nat.unpair e).snd).map
            $ fun x => ofWType (WType.mk a fun b => (x b).val) (s + 1) (by simp[depth])) :=
      by simp[Encodable.decode_sigma_val, Option.map_bind', Function.comp]
    _ = ((decode e.unpair.1 : Option α).bind
        $ fun a => (decode (α := List (SubWType β s)) e.unpair.2).bind
          $ fun l => (l.toVector (Fintype.card (β a))).map
            $ fun v => ofWType ⟨a, fun b => (fintypeArrowEquivVector.symm v b).val⟩ _ (by simp[depth, Equiv.vectorEquivFin])) :=
      by congr; funext a; rw[decode_fintypeArrow]; simp[Option.map_bind']; congr

lemma encode_mk (a : α) (f : β a → WType β) (h) :
    encode (ofWType ⟨a, f⟩ (s + 1) h) = (encode a).pair (encode $ fun b => encode (ofWType (f b) s (by simp[depth] at h; exact h b))) := by
  simp[Primcodable.SubWType, primcodable_succ, Primcodable.ofEquiv_toEncodable]
  rw[Encodable.encode_ofEquiv equiv_succ, equiv_succ]; simp[ofWType]
  rw[Encodable.encode_sigma_val]
  simp; exact encode_fintypeArrow' (β a) (SubWType β s) _

section elimDecode

variable {σ : Type _} {γ : Type _}
variable (β)

def elimDecode (f : α → List γ → γ) : ℕ → ℕ → Option γ :=
 fun s e => (decode e : Option (SubWType β s)).map (elim' γ (fun ⟨a, v⟩ => f a (List.ofFn $ fintypeArrowEquivFinArrow v)) s)

variable {β}

abbrev decode' (s e : ℕ) : Option (SubWType β s) := decode e

lemma elim'_eq_elimDecode [Inhabited γ] (f : (a : α) × (β a → γ) → γ) :
    (decode e).map (elim' γ f s) = elimDecode β (fun a l => f ⟨a, fintypeArrowEquivFinArrow.symm (fun i => l.getI i)⟩) s e := by
  simp[elimDecode]
  rcases (decode e) with (_ | w) <;> simp
  { congr; funext ⟨a, j⟩; simp; congr; funext b; simp }

lemma elim'_eq_elimDecode' [Inhabited γ] (f : (a : α) × (β a → γ) → γ) :
    (decode' s e).map (elim' γ f s) = elimDecode β (fun a l => f ⟨a, fintypeArrowEquivFinArrow.symm (fun i => l.getI i)⟩) s e :=
  elim'_eq_elimDecode f

variable (β)

lemma elimDecode_eq_induction (f : α → List γ → γ) (s e) :
    elimDecode β f s e =
    Nat.casesOn s none
      (fun s => (decode e.unpair.1 : Option α).bind
        $ fun a => (((Denumerable.ofNat (List ℕ) e.unpair.2).mapM' (elimDecode β f s)).bind
          $ fun l => if l.length = Fintype.card (β a) then some l else none).map
            $ fun v => f a v) := by
  rcases s with (_ | s)
  · simp[elimDecode]
  · simp[elimDecode, SubWType.decode_succ, Option.map_bind', decode_list, Function.comp, List.mapM'_option_map]; congr
    funext a
    rcases hw : List.mapM' (decode : ℕ → Option (SubWType β s)) (Denumerable.ofNat (List ℕ) e.unpair.2) with (_ | w) <;> simp
    { simp[List.toVector]
      by_cases hlw : w.length = Fintype.card (β a) <;> simp[hlw, elim, elim']
      { simp[Vector.get_mk_eq_get, List.ofFn_get_eq_map]; congr
        rw[Encodable.fintypeArrowEquivFinArrow_fintypeEquivFin (fun i =>
          WType.elim γ (fun x => f x.fst (List.ofFn (fintypeArrowEquivFinArrow x.snd))) (w.get (i.cast hlw.symm)).val)];
        rw[List.ofFn_get_eq_map (fun z => WType.elim γ (fun x => f x.fst (List.ofFn (fintypeArrowEquivFinArrow x.snd))) z.val) w];rfl } }

@[reducible]
private def elimDecodeG (f : σ → α → List γ → γ) : σ → ℕ × ℕ → List (Option γ) → Option γ := fun x (s, e) ih =>
  Nat.casesOn s none
    (fun s => (decode e.unpair.1 : Option α).bind
      $ fun a => (((Denumerable.ofNat (List ℕ) e.unpair.2).mapM' (fun c => ih.getI (s.pair c))).bind
        $ fun l => if l.length = Fintype.card (β a) then some l else none).map
          $ fun v => f x a v)

private lemma elimDecodeG_eq_elimDecode (f : σ → α → List γ → γ) (x s e) :
    elimDecodeG β f x (s, e) ((List.range (s.pair e)).map (fun i => elimDecode β (f x) i.unpair.1 i.unpair.2)) = elimDecode β (f x) s e := by
  simp[elimDecode_eq_induction β (f x) s e, elimDecodeG]
  rcases s with (_ | s) <;> simp; congr
  funext a
  have : 
    mapM' (fun c => ((List.range ((s + 1).pair e)).map $ fun i => elimDecode β (f x) i.unpair.fst i.unpair.snd).getI (s.pair c))
      (Denumerable.ofNat (List ℕ) e.unpair.2) =
    mapM' (elimDecode β (f x) s) (Denumerable.ofNat (List ℕ) e.unpair.2) :=
  List.mapM'_eq_mapM'_of_eq _ (by
  { intro c hc
    have : s.pair c < (s + 1).pair e := by
      have : c < e.unpair.2 := Denumerable.lt_of_mem_list _ _ hc
      exact lt_of_lt_of_le (Nat.pair_lt_pair_right s this) (Nat.pair_le_pair_of_le (Nat.le_succ s) (Nat.unpair_right_le e))
    simp[List.getI_map_range _ this] })
  rw[this]

variable [Primcodable σ] [Primcodable γ]

private lemma elimDecodeG_primrec {f : σ → α × List γ → γ} (hf : Primrec₂ f) :
    Primrec₂ (fun p ih => elimDecodeG β (fun x a ih => f x (a, ih)) p.1 p.2 ih : σ × (ℕ × ℕ) → List (Option γ) → Option γ) :=
  by apply Primrec.nat_casesOn (fst.comp $ snd.comp fst) (const none)
      (by apply option_bind (Primrec.decode.comp $ fst.comp $ Primrec.unpair.comp $ snd.comp $ snd.comp $ fst.comp fst)
            (by apply option_map
                  (option_bind
                    (by apply option_list_mapM'
                          (by apply (Primrec.ofNat _).comp $ snd.comp $ Primrec.unpair.comp $ snd.comp $ snd.comp $ fst.comp $ fst.comp $ fst)
                          (Primrec.list_getI.comp (snd.comp $ fst.comp $ fst.comp fst)
                                (Primrec₂.natPair.comp (snd.comp $ fst.comp fst) snd)).to₂)
                    (Primrec.ite
                          (Primrec.eq.comp (list_length.comp snd) (PrimrecCard.card_prim.comp $ snd.comp fst))
                          (option_some.comp snd)
                          (const none)).to₂)
                  (hf.comp (fst.comp $ fst.comp $ fst.comp $ fst.comp fst) (Primrec.pair (snd.comp fst) snd)).to₂))

lemma primrec_elimDecode_param {f : σ → α × List γ → γ} (hf : Primrec₂ f) :
    Primrec₂ (fun x p => elimDecode β (fun a ih => f x (a, ih)) p.1 p.2 : σ → ℕ × ℕ → Option γ) := by
  have : Primrec₂ (fun p ih => some $ elimDecodeG β (fun x a ih => f x (a, ih)) p.1 p.2 ih : σ × (ℕ × ℕ) → List (Option γ) → Option (Option γ)) :=
    option_some.comp (elimDecodeG_primrec β hf)
  exact nat_strong_rec'2 _ this (by simp[elimDecodeG_eq_elimDecode β])

lemma primrec_elimDecode {f : α → List γ → γ} (hf : Primrec₂ f) :
    Primrec₂ (fun s e => elimDecode β f s e : ℕ → ℕ → Option γ) :=
  have : Primrec₂ (fun _ p => f p.1 p.2 : Unit → α × List γ → γ) := hf.comp (fst.comp snd) (snd.comp snd)
  (primrec_elimDecode_param β this).comp₂ (const ()).to₂ (fst.pair snd)

lemma primrec_elimDecode_param_comp {f : σ → α × List γ → γ} {g : σ → ℕ} {h : σ → ℕ} (hf : Primrec₂ f) (hg : Primrec g) (hh : Primrec h) :
    Primrec (fun x => elimDecode β (fun a l => f x (a, l)) (g x) (h x) : σ → Option γ) :=
  (primrec_elimDecode_param β hf).comp Primrec.id (hg.pair hh)

end elimDecode

lemma encode_eq_elim' : ∀ w : SubWType β s, encode w = elim' ℕ encode s w := by
  { induction' s with s ih
    · simp; intro ⟨w, h⟩; simpa using lt_of_lt_of_le (depth_pos w) h
    · rintro ⟨⟨a, f⟩, hw⟩; simp[elim', elim, Primcodable.SubWType, primcodable_succ, Primcodable.ofEquiv_toEncodable]
      rw[Encodable.encode_ofEquiv equiv_succ]
      simp[equiv_succ, Encodable.encode_sigma_val]
      suffices :
        encode (⟨a, fun b => ofWType (f b) s (by simp[depth, Nat.succ_eq_add_one] at hw; exact hw b)⟩ : (a : α) × (β a → SubWType β s)) =
        encode (⟨a, fun b => elim ℕ encode (f b)⟩ : (a : α) × (β a → ℕ))
      { exact this }
      rw[Encodable.encode_sigma_val, Encodable.encode_sigma_val, encode_fintypeArrow, encode_finArrow, encode_list]
      simp[Function.comp]; rw[←encode_finArrow, encode_fintypeArrow (β a)]; simp
      congr; funext i; simp; rw[ih]; rfl }

lemma encodeDecode_eq_elimDecode (s e : ℕ) : encodeDecode (SubWType β s) e = elimDecode β (fun a l => encode (a, l)) s e := by
  simp[elimDecode, encodeDecode_eq_encode_map_decode]
  rcases (decode e) <;> simp[encode_eq_elim']; congr
  funext ⟨a, f⟩; simp[encode_fintypeArrow, encode_finArrow]

instance uniformlyPrimcodable : UniformlyPrimcodable (SubWType β) :=
  UniformlyPrimcodable.ofEncodeDecode (by
    have : Primrec₂ (elimDecode β (fun a l => encode (a, l))) :=
      primrec_elimDecode β (Primrec.encode.comp $ Primrec₂.pair.comp fst snd)
    exact this.of_eq (by simp[encodeDecode_eq_elimDecode]))

lemma depth_eq_elimDecode (s e : ℕ) :
    (decode e : Option (SubWType β s)).map (fun w => w.val.depth) = elimDecode β (fun a l => l.sup + 1) s e := by
  have : ∀ w : SubWType β s, depth w.val = elim' ℕ (fun p => Finset.sup Finset.univ p.snd + 1) s w
  { induction' s with s ih
    · simp; intro ⟨w, h⟩; simpa using lt_of_lt_of_le (depth_pos w) h
    · rintro ⟨⟨a, f⟩, hw⟩;
      simp[depth, ih, elim', elim]
      have : ∀ (b : β a), depth (f b) = elim ℕ (fun p => Finset.sup Finset.univ p.snd + 1) (f b) :=
        fun b => ih ⟨f b, by simp[depth, Nat.succ_eq_add_one] at hw; exact hw b⟩
      simp[this] }
  simp[elimDecode, encodeDecode_eq_encode_map_decode]
  rcases (decode e) <;> simp[this]; congr
  funext ⟨a, f⟩; simp[List.sup_ofFn, fintypeArrowEquivFinArrow_eq]

lemma depth_decode_primrec : Primrec₂ (fun s e => (decode e : Option (SubWType β s)).map (fun w => w.val.depth)) := by
  have : Primrec₂ (elimDecode β (fun a l => l.sup + 1)) :=
    primrec_elimDecode β (by simp[←Nat.succ_eq_add_one]; apply Primrec.succ.comp $ (list_sup nat_max).comp snd)
  exact this.of_eq (by simp[depth_eq_elimDecode])

def ofW : WType β → (s : ℕ) × SubWType β s := fun w => ⟨w.depth, ofWType w w.depth (by rfl)⟩

def toW : (s : ℕ) × SubWType β s → WType β := fun ⟨_, w⟩ => w.val

end SubWType

private lemma encode_decode_eq (e : ℕ) :
    Option.casesOn ((decode e : Option ((s : ℕ) × SubWType β s)).map SubWType.toW) 0 (fun w => encode (SubWType.ofW w) + 1) =
    encode (((encodeDecode (SubWType β e.unpair.1) e.unpair.2).bind
      $ fun c => ((decode c : Option (SubWType β e.unpair.1)).map (fun w => w.val.depth)).map
        $ fun d => d.pair c)) := by
  simp[Function.comp, encodeDecode_eq_encode_map_decode]
  rcases (decode e.unpair.2) with (_ | w) <;> simp[SubWType.toW, SubWType.ofW]
  { simp[SubWType.encode_eq_elim']; apply SubWType.elim_const; simp }

private lemma primrec_encode_decode :
    Primrec (fun e => 
      encode (((encodeDecode (SubWType β e.unpair.1) e.unpair.2).bind
        $ fun c => ((decode c : Option (SubWType β e.unpair.1)).map (fun w => w.val.depth)).map
          $ fun d => d.pair c)) : ℕ → ℕ) :=
  (Primrec.encode.comp $
    option_bind (Primrec₂.encodeDecode_u.comp (fst.comp Primrec.unpair) (snd.comp Primrec.unpair))
      (option_map (SubWType.depth_decode_primrec.comp (fst.comp $ Primrec.unpair.comp fst) snd)
        (Primrec₂.natPair.comp₂ Primrec₂.right (snd.comp fst))))

private def encodable : Encodable (WType β) where
  encode := fun w => encode (SubWType.ofW w)
  decode := fun e => (decode e).map SubWType.toW
  encodek := by rintro ⟨a, f⟩; simp[SubWType.toW, SubWType.ofW]

instance _root_.Primcodable.wtype : Primcodable (WType β) :=
  { encodable with
    prim := Primrec.nat_iff.mp <| primrec_encode_decode.of_eq (fun e => (encode_decode_eq e).symm) }

lemma encode_eq (w : WType β) : encode w = encode (SubWType.ofW w) := rfl

lemma decode_eq (e : ℕ) : decode e = (decode e : Option ((s : ℕ) × SubWType β s)).map SubWType.toW := rfl

def elimL (f : α → List γ → γ) : WType β → γ :=
 fun w => elim γ (fun ⟨a, v⟩ => f a (List.ofFn $ fintypeArrowEquivFinArrow v)) w

lemma elimL_mk (f : α → List γ → γ) (a : α) (v : β a → WType β) :
    elimL f ⟨a, v⟩ = f a (List.ofFn $ fintypeArrowEquivFinArrow $ fun b => elimL f (v b)) := by simp[elimL, elim]

lemma elim_eq_elimL [Inhabited γ] (f : (a : α) × (β a → γ) → γ) :
    elim γ f w = elimL (fun a l => f ⟨a, fintypeArrowEquivFinArrow.symm (fun i => l.getI i)⟩) w := by
  simp[elimL]; congr; funext ⟨a, j⟩; simp; congr; funext b; simp

lemma decode_elimL_eq (f : α → List γ → γ) :
    (decode e : Option (WType β)).map (elimL f) = (SubWType.elimDecode β f e.unpair.1 e.unpair.2) := by
  simp[elimL, decode_eq, Function.comp, SubWType.elimDecode, SubWType.elim']
  rcases (decode e.unpair.2) with (_ | ⟨_, _⟩) <;> simp[SubWType.toW]

def mkL (a : α) (l : List (WType β)) : Option (WType β) :=
  if h : l.length = Fintype.card (β a) then
    some (WType.mk a $ fintypeArrowEquivFinArrow.symm $ fun (i : Fin (Fintype.card (β a))) => l.get (i.cast h.symm)) else none

def mkFintype (a : α) (v : β a → WType β) : WType β := WType.mk a v

def mk₀ (a : α) : Option (WType β) := mkL a []

def mk₁ (a : α) (w : WType β) : Option (WType β) := mkL a [w]

def mkFin {k} (a : α) (v : Fin k → WType β) : Option (WType β) := mkL a (List.ofFn v)

lemma encode_mk_eq (a : α) (f : β a → WType β) :
    encode (mk a f) = (Finset.sup Finset.univ (fun n => (f n).depth) + 1).pair ((encode a).pair (encode $ fun b => (encode $ f b).unpair.2)) := by
  simp[encode_eq, SubWType.ofW, depth, SubWType.encode_mk]
  funext b; simp[SubWType.encode_eq_elim']; apply SubWType.elim_const; simp

lemma mk₀_eq (a : α) [h : IsEmpty (β a)] : mk₀ a = some (⟨a, h.elim'⟩ : WType β) := by
  simp[mk₀, mkL, Fintype.card_eq_zero_iff.mpr h]

end WType

namespace Primrec

open Encodable WType
variable {σ : Type _} {α : Type _} {β : α → Type _} {γ : Type _}
  [Primcodable σ] [Primcodable α] [(a : α) → Fintype (β a)]
  [(a : α) → DecidableEq (β a)] [(a : α) → Primcodable (β a)] [PrimrecCard β] [Primcodable γ]

lemma finArrow_list_ofFn {α} [Primcodable α] : Primrec (fun v => List.ofFn v : (Fin k → α) → List α) :=
  have : Primrec (fun e => Encodable.encode $ Encodable.decode (α := Fin k → α) e) := Primrec.encode.comp Primrec.decode
  (decode_iff.mp $ encode_iff.mp $ this.of_eq $ fun e => by rcases (Encodable.decode e) <;> simp[Encodable.encode_finArrow])

lemma sigma_finArrow_list_ofFn {α} [Primcodable α] : Primrec (fun v => List.ofFn v.2 : (Σ k, Fin k → α) → List α) :=
  have : Primrec (fun p => (encode p).unpair.2 : (Σ k, Fin k → α) → ℕ) := (snd.comp $ unpair.comp Primrec.encode)
  encode_iff.mp (this.of_eq $ fun ⟨k, v⟩ => by simp[encode_finArrow])

lemma sigma_fst [UniformlyPrimcodable β] : Primrec (Sigma.fst : ((a : α) × β a) → α) :=
  have : Primrec (fun e => (decode (α := α) e.unpair.1).bind $ fun a => (encodeDecode (β a) e.unpair.2).map (fun _ => a) : ℕ → Option α) :=
    option_bind (Primrec.decode.comp $ fst.comp unpair)
      (option_map (Primrec₂.encodeDecode_u.comp snd (snd.comp $ unpair.comp fst)) (snd.comp fst).to₂)
  decode_iff.mp (this.of_eq $
    by intro n; simp; rcases (decode n.unpair.1) with (_ | a) <;> simp
       { simp[encodeDecode_eq_encode_map_decode, Function.comp] })

lemma sigma_prod_left {α} {β γ : α → Type _} [Primcodable α]
  [(a : α) → Primcodable (β a)] [(a : α) → Primcodable (γ a)] [UniformlyPrimcodable β] [UniformlyPrimcodable γ] :
    Primrec (fun p => ⟨p.1, p.2.1⟩ : (Σ a, β a × γ a) → (Σ a, β a)) :=
  have : Primrec (fun p => Nat.pair (encode p).unpair.1 (encode p).unpair.2.unpair.1 : (Σ a, β a × γ a) → ℕ) :=
    Primrec₂.natPair.comp (fst.comp $ unpair.comp Primrec.encode) (fst.comp $ unpair.comp $ snd.comp $ unpair.comp Primrec.encode)
  encode_iff.mp (this.of_eq $ fun ⟨k, b, v⟩ => by simp[encode_finArrow])

lemma sigma_prod_right {α} {β γ : α → Type _} [Primcodable α]
  [(a : α) → Primcodable (β a)] [(a : α) → Primcodable (γ a)] [UniformlyPrimcodable β] [UniformlyPrimcodable γ] :
    Primrec (fun p => ⟨p.1, p.2.2⟩ : (Σ a, β a × γ a) → (Σ a, γ a)) :=
  have : Primrec (fun p => Nat.pair (encode p).unpair.1 (encode p).unpair.2.unpair.2 : (Σ a, β a × γ a) → ℕ) :=
    Primrec₂.natPair.comp (fst.comp $ unpair.comp Primrec.encode) (snd.comp $ unpair.comp $ snd.comp $ unpair.comp Primrec.encode)
  encode_iff.mp (this.of_eq $ fun ⟨k, b, v⟩ => by simp[encode_finArrow])

lemma sigma_pair [UniformlyPrimcodable β] (a : α) : Primrec (Sigma.mk a : β a → (a : α) × β a) :=
  encode_iff.mp (by simp; exact Primrec₂.natPair.comp (const _) Primrec.encode)

lemma finArrow_map {f} (hf : Primrec f) (k) : Primrec (fun v i => f (v i) : (Fin k → α) → (Fin k → σ)) := by
  have : Primrec (fun e => encode $ ((encodeDecode (Fin k → α) e).bind
    $ fun c => (decode c : Option (List α)).map (fun l => l.map f)) : ℕ → ℕ) :=
    (Primrec.encode.comp $ option_bind Primrec.encodeDecode
      (option_map (Primrec.decode.comp snd) (by apply list_map snd (hf.comp₂ Primrec₂.right))))
  exact decode_iff.mp (encode_iff.mp $ this.of_eq $ fun e => by
    simp[encodeDecode_eq_encode_map_decode, decode_finArrow]
    rcases has : (decode e) with (_ | as) <;> simp[Function.comp]
    { rfl }
    { rcases hv : (as.toVector k) with (_ | v) <;> simp
      { rfl }
      { rw[Encodable.encode_some]; simp[encode_finArrow, Function.comp] } })

lemma w_depth : Primrec (fun w => w.depth : WType β → ℕ) := by
  have : Primrec (fun n => (encodeDecode (WType β) n).map $ fun e => e.unpair.1) :=
    option_map Primrec.encodeDecode (fst.comp₂ $ Primrec.unpair.comp₂ Primrec₂.right)
  exact decode_iff.mp (this.of_eq $ fun n => by
    simp[encodeDecode_eq_encode_map_decode]
    rcases decode n <;> simp[WType.encode_eq, WType.SubWType.ofW])

lemma w_elimL {f : α → List γ → γ} (hf : Primrec₂ f) : Primrec (elimL f : WType β → γ) :=
  decode_iff.mp (by simp[decode_elimL_eq]; apply SubWType.primrec_elimDecode β hf)

lemma w_elimL_param {f : σ → α × List γ → γ} (hf : Primrec₂ f) : Primrec₂ (fun x w => elimL (fun p l => f x (p, l)) w : σ → WType β → γ) :=
  decode₂2_iff.mp
    (by simp[decode_elimL_eq]
        exact (SubWType.primrec_elimDecode_param β hf).comp₂ Primrec₂.left
          (Primrec.pair (fst.comp $ Primrec.unpair.comp snd) (snd.comp $ Primrec.unpair.comp snd)).to₂)

lemma w_elim [Inhabited γ] {f : (a : α) × (β a → γ) → γ}
  (hf : Primrec₂ (fun a l => f ⟨a, fintypeArrowEquivFinArrow.symm (fun i => l.getI i)⟩ : α → List γ → γ)) :
    Primrec (WType.elim γ f) := (w_elimL (β := β) hf).of_eq (fun w => by simp[elim_eq_elimL])

lemma w_elim_param [Inhabited γ] {f : σ → (a : α) × (β a → γ) → γ}
  (hf : Primrec₂ (fun x p => f x ⟨p.1, fintypeArrowEquivFinArrow.symm (fun i => p.2.getI i)⟩ : σ → α × List γ → γ)) :
    Primrec₂ (fun x => WType.elim γ (f x)) := (w_elimL_param (β := β) hf).of_eq (fun x w => by simp[elim_eq_elimL])

lemma w_mkL : Primrec₂ (WType.mkL : α → List (WType β) → Option (WType β)) :=
  have : Primrec₂ (fun a l => if l.length = Fintype.card (β a)
      then ((l.map depth).sup + 1).pair ((encode a).pair (encode $ l.map (fun w => (encode w).unpair.2))) + 1
      else 0 : α → List (WType β) → ℕ) :=
    Primrec.ite (Primrec.eq.comp (list_length.comp snd) (PrimrecCard.card_prim.comp fst))
      (succ.comp $ Primrec₂.natPair.comp
        (succ.comp $ (list_sup nat_max).comp $ list_map snd (w_depth.comp snd))
        (Primrec₂.natPair.comp (Primrec.encode.comp fst)
          (Primrec.encode.comp $ list_map snd (snd.comp $ unpair.comp $ Primrec.encode.comp snd))))
      (const 0)
  Primrec₂.encode_iff.mp (this.of_eq $ fun a l => by
  { by_cases h : l.length = Fintype.card (β a) <;> simp[WType.mkL, *]
    { simp[encode_mk_eq]; constructor
      { exact Eq.trans (by rw[Finset.sup_univ_cast (fun i => depth (l.get i))]; exact Eq.symm <| Finset.sup_univ_list_eq_sup_map _ _)
          (Eq.symm <| Finset.sup_univ_equiv (fun i => depth (l.get (i.cast h.symm)) : Fin (Fintype.card (β a)) → ℕ) fintypeEquivFin) }
      { simp[encode_fintypeArrow, encode_finArrow]
        ext i c; simp
        rcases hw : (l.get? i) with (_ | w) <;> simp[List.ofFnNthVal]
        · have : ¬i < Fintype.card (β a) := by simpa[h] using List.get?_eq_none.mp hw
          simp[this]
        · have : ∃ hi, l.get ⟨i, hi⟩ = w := List.get?_eq_some.mp hw
          rcases this with ⟨hi, rfl⟩
          have : i < Fintype.card (β a) := by simpa[h] using hi
          simp[this] } } })

lemma w_mk₀ (f : σ → α) (h : (x : σ) → IsEmpty (β (f x))) (hf : Primrec f) {v : {x : σ} → β (f x) → WType β}:
    Primrec (fun x => WType.mk (f x) v : σ → WType β) := by
  have : Primrec (fun x => Nat.pair 1 (Nat.pair (encode $ f x) 0) : σ → ℕ) :=
    Primrec₂.natPair.comp (const 1) (Primrec₂.natPair.comp (Primrec.encode.comp hf) (const 0))
  exact Primrec.encode_iff.mp (this.of_eq $ fun x => by simp[encode_mk_eq, encode_fintypeArrow_isEmpty])

lemma w_mk₁ (f : σ → α) (h : ∀ x, Fintype.card (β (f x)) = 1) (hf : Primrec f) :
    Primrec₂ (fun x w => WType.mk (f x) (fun _ => w) : σ → WType β → WType β) := by
  have : Primrec₂ (fun x w => Nat.pair (w.depth + 1) (Nat.pair (encode $ f x) (encode [(encode w).unpair.2])) : σ → WType β → ℕ) :=
    Primrec₂.natPair.comp
      (succ.comp $ w_depth.comp snd)
      (Primrec₂.natPair.comp (Primrec.encode.comp $ hf.comp fst)
        (Primrec.encode.comp $ list_cons.comp (snd.comp $ unpair.comp $ Primrec.encode.comp snd) (const [])))
  exact Primrec₂.encode_iff.mp (this.of_eq $ fun x w => by
    simp[encode_mk_eq, encode_fintypeArrow_card_one (h x) ℕ _ (fintypeEquivFin.symm ((0 : Fin 1).cast (h x).symm))]
    have : Finset.univ = {fintypeEquivFin.symm ((0 : Fin 1).cast (h x).symm)}
    { have : Subsingleton (β (f x)) := Fintype.card_le_one_iff_subsingleton.mp (by simp[h x])
      ext; simp }
    rw[this, Finset.sup_singleton])

lemma w_mk₂ (f : σ → α) (h : ∀ x, Fintype.card (β (f x)) = 2) (hf : Primrec f) :
    Primrec₂ (fun x w => WType.mk (f x) ((fintypeArrowEquivFinArrow' (h x)).symm ![w.1, w.2]) : σ → WType β × WType β → WType β) := by
  have : Primrec₂ (fun x w => Nat.pred $ encode (WType.mkL (f x) [w.1, w.2]) : σ → WType β × WType β → ℕ) :=
    (pred.comp $ Primrec.encode.comp $ w_mkL.comp (hf.comp fst) (list_cons.comp (fst.comp snd) (list_cons.comp (snd.comp snd) (const []))))
  exact Primrec₂.encode_iff.mp (this.of_eq $ fun x ⟨w₁, w₂⟩ => by
    simp[mkL, h]
    have := (fintypeArrowEquivFinArrow' (α := WType β) (h x)).injective
    apply this
    funext i; simp
    cases i using Fin.cases <;> simp)

lemma w_mkFin (f : σ → α) {k} (h : ∀ x, Fintype.card (β (f x)) = k) (hf : Primrec f) :
    Primrec₂ (fun x w => WType.mk (f x) ((fintypeArrowEquivFinArrow' (h x)).symm w) : σ → (Fin k → WType β) → WType β) := by
  have : Primrec₂ (fun x w => Nat.pred $ encode (WType.mkL (f x) (List.ofFn w)) : σ → (Fin k → WType β) → ℕ) :=
    (pred.comp $ Primrec.encode.comp $ w_mkL.comp (hf.comp fst) (finArrow_list_ofFn.comp snd))
  exact Primrec₂.encode_iff.mp (this.of_eq $ fun x w => by
    simp[mkL, h]
    have := (fintypeArrowEquivFinArrow' (α := WType β) (h x)).injective
    apply this
    funext i; simp; congr)

end Primrec
