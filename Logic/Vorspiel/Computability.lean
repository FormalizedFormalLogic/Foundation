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

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Encodable ι]

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

variable {α : Type*} [Encodable α]

@[reducible] def encodeDecode (α : Type*) [Encodable α] (e : ℕ) : Option ℕ := (encode (decode e : Option α)).predO

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

lemma encode_decode_sigma_s {β : α → Type*} [(a : α) → Encodable (β a)] {e : ℕ} :
    encodeDecode ((a : α) × β a) e = ((decode e.unpair.1 : Option α).bind $ fun a => (encodeDecode (β a) e.unpair.2).map $ fun b => (encode a).pair b) := by
  rcases ha : (decode e.unpair.1 : Option α) with (_ | a) <;> simp[*, encodeDecode]
  { rcases (decode e.unpair.2 : Option (β a)) with (_ | b) <;> simp[*] }

lemma encode_decode_sigma_of_none {β : α → Type*} [(a : α) → Encodable (β a)] {e : ℕ} (h : (decode e.unpair.1 : Option α) = none) :
    encodeDecode (α := (a : α) × β a) e = none := by
  simp[encodeDecode, h]

lemma encode_decode_sigma_of_some {β : α → Type*} [(a : α) → Encodable (β a)] {e : ℕ} {a : α} (h : decode e.unpair.1 = some a) :
    encodeDecode ((a : α) × β a) e = (encodeDecode (β a) e.unpair.2).map fun b => (encode a).pair b := by
  simp[encodeDecode, h]; rcases h : decode e.unpair.2 with (_ | b) <;> simp

end Encodable

namespace Primcodable

open Encodable

lemma ofEquiv_toEncodable {α : Type*} {β : Type*} [Primcodable α] (e : β ≃ α) :
  (ofEquiv α e).toEncodable = Encodable.ofEquiv α e := rfl

instance fintypeArrow [DecidableEq α] [Fintype α] [Encodable α] (β : Type*) [Primcodable β] : Primcodable (α → β) :=
    Primcodable.ofEquiv (Fin (Fintype.card α) → β) fintypeArrowEquivFinArrow

end Primcodable

namespace Primrec

open Encodable
variable {α α₁ α₂ β γ σ τ : Type*}
  [Primcodable α] [Primcodable α₁] [Primcodable α₂] [Primcodable β] [Primcodable γ]
  [Primcodable σ] [Primcodable τ]

lemma decode_iff {f : α → σ} :
    Primrec (fun n => (Encodable.decode n).map f) ↔ Primrec f :=
  ⟨fun h => by simp[Primrec]; exact Primrec.nat_iff.mp (Primrec.encode.comp h),
   fun h => option_map Primrec.decode (h.comp₂ Primrec₂.right)⟩

lemma _root_.Primrec₂.decode_iff₁ {f : α → β → σ} :
    Primrec₂ (fun n b => (Encodable.decode n).map (f · b)) ↔ Primrec₂ f :=
  ⟨fun h => Primrec₂.option_some_iff.mp
    ((h.comp₂ (Primrec.encode.comp₂ Primrec₂.left) Primrec₂.right).of_eq $ by simp),
   fun h => option_map (Primrec.decode.comp fst) (h.comp₂ Primrec₂.right (snd.comp₂ Primrec₂.left))⟩

lemma _root_.Primrec₂.decode_iff₂ {f : α → β → σ} :
    Primrec₂ (fun a n => (Encodable.decode n).map (f a)) ↔ Primrec₂ f :=
  ⟨fun h => Primrec₂.option_some_iff.mp
    ((h.comp₂ Primrec₂.left (Primrec.encode.comp₂ Primrec₂.right)).of_eq $ by simp),
   fun h => option_map (Primrec.decode.comp snd) (h.comp₂ (fst.comp fst) Primrec₂.right)⟩

section Equiv

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
  exact Primrec₂.decode_iff₂.mp (this.of_eq $ fun x e => by simp only [Option.map_eq_bind]; rfl)

lemma list_zipWith {f : α → β → γ} (hf : Primrec₂ f) : Primrec₂ (List.zipWith f) :=
  (list_zipWith_param (hf.comp₂ (fst.comp₂ Primrec₂.right) (snd.comp₂ Primrec₂.right))).comp₂
    (Primrec₂.const ())
    Primrec.id.to₂

end zipWith

open Encodable
variable {α : Type*} [Primcodable α]

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

instance vector (β : Type*) [Primcodable β] : UniformlyPrimcodable (Vector β) where
  uniformly_prim := by
    have e : ∀ n e, encode ((decode (α := List β) e).bind (fun a => if a.length = n then some a else none)) =
        encode (decode (α := Vector β n) e) := by intro n e; rw[Encodable.encode_decode_subtype]
    have : Primrec₂ (fun n e => encode ((decode (α := List β) e).bind (fun a => if a.length = n then some a else none))) :=
      Primrec.encode.comp
        (Primrec.option_bind
          (Primrec.decode.comp snd)
          (Primrec.ite (Primrec.eq.comp (Primrec.list_length.comp snd) (fst.comp fst)) (Primrec.option_some.comp snd) (const none)))
    exact this.of_eq e

instance finArrow (β : Type*) [Primcodable β] : UniformlyPrimcodable (Fin · → β) where
  uniformly_prim := by
    have : ∀ n e, encode (decode (α := Vector β n) e) = encode (decode (α := Fin n → β) e) := by
      intro n e; simp[Encodable.decode_ofEquiv]
      rcases h : decode (α := Vector β n) e with (_ | v) <;> simp
      { have : ∀ b : Fin n → β, encode b = encode ((Equiv.vectorEquivFin β n).symm b) := 
          fun b => encode_ofEquiv (Equiv.vectorEquivFin β n).symm b
        simpa using (this (Equiv.vectorEquivFin β n v)).symm }
    exact uniformly_prim.of_eq this

instance fintypeArrow (γ : α → Type*) (β : Type*)
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

instance prod (β : α → Type*) (γ : α → Type*)
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

instance const {β : Type*} [Primcodable β] : UniformlyPrimcodable (fun (_ : α) => β) where
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
variable {β : Type*} [Encodable β]

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

lemma decode_finArrow (β : Type*) [Primcodable β] (e : ℕ) :
    (decode (α := Fin k → β) e) = (decode (α := List β) e).bind (fun l => (l.toVector k).map (Equiv.vectorEquivFin β k)) := by
  simp[Primcodable.ofEquiv_toEncodable, Encodable.decode_ofEquiv]
  rw[decode_vector];
  rcases (decode e : Option (List β)) with (_ | bs) <;> simp

lemma decode_fintypeArrow (ι : Type*) [Fintype ι] [Primcodable ι] [DecidableEq ι] (β : Type*) [Primcodable β] (e : ℕ) :
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

lemma encode_fintypeArrow (ι : Type*) [Fintype ι] [Primcodable ι] [DecidableEq ι] (β : Type*) [Primcodable β] (f : ι → β) :
    encode f = encode (fintypeArrowEquivFinArrow f) := by simp[Primcodable.ofEquiv_toEncodable]; rw[Encodable.encode_ofEquiv]

lemma encode_fintypeArrow' (ι : Type*) [Fintype ι] [Primcodable ι] [DecidableEq ι] (β : Type*) [Primcodable β] (f : ι → β) :
    encode f = encode (fun i => encode (f i)) := by
  simp[encode_fintypeArrow, encode_finArrow, encode_list (List.ofFn $ fintypeArrowEquivFinArrow f)]
  funext i; simp

lemma encode_fintypeArrow_isEmpty
  (ι : Type*) [Fintype ι] [Primcodable ι] [DecidableEq ι] [IsEmpty ι] (β : Type*) [Primcodable β] (f : ι → β) :
    encode f = 0 := by
  have : Fintype.card ι = 0 := Fintype.card_eq_zero
  simp[encode_fintypeArrow, encode_finArrow, this]

lemma encode_fintypeArrow_card_one
  {ι : Type*} [Fintype ι] [Primcodable ι] [DecidableEq ι] (hι : Fintype.card ι = 1) (β : Type*) [Primcodable β] (f : ι → β) (i) :
    encode f = encode [f i] := by
  have : Subsingleton ι := Fintype.card_le_one_iff_subsingleton.mp (by simp[hι])
  simp[encode_fintypeArrow, encode_finArrow, hι, (this.allEq · i)]

lemma encode_fintypeArrow_card_two
  {ι : Type*} [Fintype ι] [Primcodable ι] [DecidableEq ι] (hι : Fintype.card ι = 2) (β : Type*) [Primcodable β] (f : ι → β) :
    encode f = encode [f (fintypeEquivFin.symm ((0 : Fin 2).cast hι.symm)), f (fintypeEquivFin.symm ((1 : Fin 2).cast hι.symm))] := by
  simp[encode_fintypeArrow, encode_finArrow, hι]; exact ⟨by congr, by congr⟩

lemma encode_list_lt {b : β} {bs : List β} (h : b ∈ bs) : encode b < encode bs := by
  induction' bs with b' bs ih
  · simp at h
  · have : b = b' ∨ b ∈ bs := by simpa using h
    rcases this with (rfl | lt) <;> simp
    · exact Nat.lt_succ.mpr (Nat.left_le_pair (encode b) (encode bs))
    · exact Nat.lt.step <| lt_of_lt_of_le (ih lt) (Nat.right_le_pair (encode b') (encode bs))

end Encodable

