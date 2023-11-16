import Logic.Vorspiel.Vorspiel
import Mathlib.Computability.Halting

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

@[simp] lemma fintypeArrowEquivFinArrow_app (f : ι → α) (i) :
    fintypeArrowEquivFinArrow f i = f (fintypeEquivFin.symm i) := by rfl

@[simp] lemma fintypeArrowEquivFinArrow_symm_app (v : Fin (Fintype.card ι) → α) :
    fintypeArrowEquivFinArrow.symm v i = v (fintypeEquivFin i) := by rfl

@[simp] lemma fintypeArrowEquivFinArrow'_app {k} (hk : Fintype.card ι = k) (f : ι → α) (i) :
  fintypeArrowEquivFinArrow' hk f i = f (fintypeEquivFin.symm $ i.cast hk.symm) := by rcases hk with rfl; rfl

@[simp] lemma fintypeArrowEquivFinArrow'_symm_app {k} (hk : Fintype.card ι = k) (v : Fin k → α) :
    (fintypeArrowEquivFinArrow' hk).symm v i = v ((fintypeEquivFin i).cast hk) := by rcases hk with rfl; rfl

@[simp] lemma cast_fintypeEquivFin_fin {k : ℕ} (i : Fin k) : (fintypeEquivFin i).cast (Fintype.card_fin _) = i := by
  ext
  simp [Encodable.fintypeEquivFin, Fin.cast_eq_cast',
    Fin.encodable, List.Nodup.getEquivOfForallMemList,
    Encodable.sortedUniv, Encodable.encode']
  convert List.indexOf_finRange i
  exact Fin.sort_univ _

@[simp] lemma val_fintypeEquivFin_fin {k : ℕ} (i : Fin k) : (fintypeEquivFin i).val = i.val :=
  congr_arg Fin.val (cast_fintypeEquivFin_fin i)

@[simp] lemma fintypeEquivFin_false : fintypeEquivFin false = 0 := rfl

@[simp] lemma fintypeEquivFin_true : fintypeEquivFin true = 1 := rfl

@[simp] lemma fintypeEquivFin_symm_zero : fintypeEquivFin.symm 0 = false := rfl

@[simp] lemma fintypeEquivFin_symm_one : fintypeEquivFin.symm 1 = true := rfl

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

lemma option_get! [Inhabited α] : Primrec (Option.get! : Option α → α) :=
  (option_casesOn Primrec.id (const default) Primrec₂.right).of_eq <| by rintro (_ | a) <;> simp

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

lemma encode_finArrow' [Primcodable β] (f : Fin k → β) :
    encode f = encode (fun i => encode (f i)) := by
  simp[encode_finArrow, encode_list (List.ofFn f)]
  funext i; simp

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
  simp[encode_fintypeArrow, encode_finArrow, hι]

lemma encode_list_lt {b : β} {bs : List β} (h : b ∈ bs) : encode b < encode bs := by
  induction' bs with b' bs ih
  · simp at h
  · have : b = b' ∨ b ∈ bs := by simpa using h
    rcases this with (rfl | lt) <;> simp
    · exact Nat.lt_succ.mpr (Nat.left_le_pair (encode b) (encode bs))
    · exact Nat.lt.step <| lt_of_lt_of_le (ih lt) (Nat.right_le_pair (encode b') (encode bs))

end Encodable

namespace Primrec

open Encodable WType
variable {σ : Type*} {α : Type*} {β : α → Type*} {γ : Type*}
  [Primcodable σ] [Primcodable α] [(a : α) → Fintype (β a)]
  [(a : α) → DecidableEq (β a)] [(a : α) → Primcodable (β a)] [PrimrecCard β] [Primcodable γ]

lemma finArrow_list_ofFn {α} [Primcodable α] : Primrec (List.ofFn : (Fin k → α) → List α) :=
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

lemma sigma_prod_left {α} {β γ : α → Type*} [Primcodable α]
  [(a : α) → Primcodable (β a)] [(a : α) → Primcodable (γ a)] [UniformlyPrimcodable β] [UniformlyPrimcodable γ] :
    Primrec (fun p => ⟨p.1, p.2.1⟩ : (Σ a, β a × γ a) → (Σ a, β a)) :=
  have : Primrec (fun p => Nat.pair (encode p).unpair.1 (encode p).unpair.2.unpair.1 : (Σ a, β a × γ a) → ℕ) :=
    Primrec₂.natPair.comp (fst.comp $ unpair.comp Primrec.encode) (fst.comp $ unpair.comp $ snd.comp $ unpair.comp Primrec.encode)
  encode_iff.mp (this.of_eq $ fun ⟨k, b, v⟩ => by simp[encode_finArrow])

lemma sigma_prod_right {α} {β γ : α → Type*} [Primcodable α]
  [(a : α) → Primcodable (β a)] [(a : α) → Primcodable (γ a)] [UniformlyPrimcodable β] [UniformlyPrimcodable γ] :
    Primrec (fun p => ⟨p.1, p.2.2⟩ : (Σ a, β a × γ a) → (Σ a, γ a)) :=
  have : Primrec (fun p => Nat.pair (encode p).unpair.1 (encode p).unpair.2.unpair.2 : (Σ a, β a × γ a) → ℕ) :=
    Primrec₂.natPair.comp (fst.comp $ unpair.comp Primrec.encode) (snd.comp $ unpair.comp $ snd.comp $ unpair.comp Primrec.encode)
  encode_iff.mp (this.of_eq $ fun ⟨k, b, v⟩ => by simp[encode_finArrow])

lemma sigma_pair [UniformlyPrimcodable β] (a : α) : Primrec (Sigma.mk a : β a → (a : α) × β a) :=
  encode_iff.mp (by simp; exact Primrec₂.natPair.comp (const _) Primrec.encode)

lemma encode_of_uniform {σ} [Primcodable σ] [UniformlyPrimcodable β] {b : σ → Σ a, β a} (hb : Primrec b) :
    Primrec (fun x => encode (b x).2) := by
  have : Primrec (fun x => (Nat.unpair (encode (b x))).2) := snd.comp (unpair.comp $ Primrec.encode.comp hb)
  exact this.of_eq <| by
    intro x
    rcases b x with ⟨a, b⟩
    simp[encode_sigma_val]

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

lemma finArrow_app {v : σ → Fin n → α} {f} (hv : Primrec v) (hf : Primrec f) : Primrec (fun x => (v x) (f x) : σ → α) :=
  have : Primrec (fun x => (List.ofFn (v x)).get? (f x)) := list_get?.comp (finArrow_list_ofFn.comp hv) (fin_val.comp hf)
  option_some_iff.mp <| this.of_eq <| fun x => by simp[List.ofFnNthVal]

lemma finite_change {f} (hf : Primrec f) (g : ℕ → α) (h : ∃ m, ∀ x ≥ m, g x = f x) : Primrec g := by
  rcases h with ⟨m, h⟩
  induction' m with m ih generalizing g
  · exact hf.of_eq <| by intro n; exact Eq.symm <| h n (Nat.zero_le n)
  · let g' : ℕ → α := fun x => if x < m then g x else f x
    have : Primrec g' :=
      ih g' (by simp; intro x hx lt; exact (False.elim $ Nat.not_le.mpr lt hx))
    have : Primrec (fun x => if x = m then g m else g' x) :=
      Primrec.ite (Primrec.eq.comp Primrec.id (const m)) (const (g m)) this
    exact this.of_eq <| by
      intro x; simp
      by_cases hx : x = m <;> simp[hx]
      intro hhx
      have : m < x := Ne.lt_of_le' hx hhx
      exact Eq.symm <| h x this

lemma of_subtype_iff {β} [Primcodable β] {p : α → Prop} [DecidablePred p] {hp : PrimrecPred p} {f : β → {a : α // p a}} :
    haveI := Primcodable.subtype hp
    Primrec (Subtype.val $ f ·) ↔ Primrec f :=
  letI := Primcodable.subtype hp
  ⟨fun hf => encode_iff.mp <| (Primrec.encode.comp hf).of_eq <| by intro b; simp[Encodable.Subtype.encode_eq],
   fun hf => subtype_val.comp hf⟩

lemma _root_.Primrec₂.of_subtype_iff {β γ} [Primcodable β] [Primcodable γ]
  {p : α → Prop} [DecidablePred p] {hp : PrimrecPred p} {f : β → γ → {a : α // p a}} :
    haveI := Primcodable.subtype hp
    Primrec₂ (Subtype.val $ f · ·) ↔ Primrec₂ f := Primrec.of_subtype_iff

lemma nat_toFin {n : ℕ} : Primrec (Nat.toFin n) :=
  have : Primrec (fun x => if x < n then x + 1 else 0) :=
    Primrec.ite (nat_lt.comp Primrec.id (const n)) succ (const 0)
  encode_iff.mp <| (Primrec.ite (nat_lt.comp Primrec.id (const n)) succ (const 0)).of_eq <| by
    intro x; simp[Nat.toFin]
    by_cases hx : x < n <;> simp[hx]
    · rfl
    · rfl

lemma decide_eq_iff (p : Prop) [Decidable p] (b : Bool) : decide p = b ↔ (p ↔ b = true) := by cases b <;> simp

lemma Primrec.lawfulbeq [BEq α] [LawfulBEq α] :
    Primrec₂ (@BEq.beq α _) := by
  haveI : DecidableEq α := Encodable.decidableEqOfEncodable α
  exact Primrec₂.of_eq Primrec.eq (by intro a b; simp[decide_eq_iff])

lemma list_mem [BEq α] [LawfulBEq α] : PrimrecRel (· ∈ · : α → List α → Prop) := by
  have : Primrec₂ (fun a l => l.foldr (fun a' ih => (a == a') || ih) false : α → List α → Bool) :=
    to₂' <| list_foldr snd (const false)
      <| (dom_bool₂ Bool.or).comp₂
        (Primrec.lawfulbeq.comp₂ (fst.comp₂ Primrec₂.left) (fst.comp₂ Primrec₂.right))
        (snd.comp₂ Primrec₂.right)
  exact this.of_eq <| by intro a as; induction as <;> simp[*]; symm; simp[decide_eq_iff]

lemma list_subset [DecidableEq α] : PrimrecRel (· ⊆ · : List α → List α → Prop) := by
  have : Primrec₂ (fun l₁ l₂ => l₁.foldr (fun a' ih => a' ∈ l₂ && ih) true : List α → List α → Bool) :=
    to₂' <| list_foldr fst (const true)
      <| (dom_bool₂ _).comp₂
        (list_mem.comp₂ (fst.comp₂ Primrec₂.right) (snd.comp₂ Primrec₂.left))
        (snd.comp₂ Primrec₂.right)
  exact this.of_eq <| by intro l₁ l₂; induction l₁ <;> simp[*]

lemma list_all {α : Type*} {β : Type*} [Primcodable α] [Primcodable β]
  {p : α → β → Bool} {l : α → List β} (hp : Primrec₂ p) (hl : Primrec l) : Primrec (fun a => (l a).all (p a)) :=
  list_foldr hl (const true) ((dom_bool₂ _).comp₂ (hp.comp₂ Primrec₂.left (fst.comp₂ Primrec₂.right)) (snd.comp₂ Primrec₂.right))

lemma list_replicate {α : Type*} [Primcodable α] : Primrec₂ (@List.replicate α) := by
   have : Primrec₂ (fun p ih => p.2 :: ih.2 : ℕ × α → ℕ × List α → List α) :=
     list_cons.comp₂ (snd.comp₂ .left) (snd.comp₂ .right)
   exact (Primrec.nat_rec' Primrec.fst (.const []) this).of_eq <| by
     rintro ⟨n, a⟩; simp; induction n <;> simp[*]

end Primrec

namespace Computable

variable {α : Type*} {β : Type*} {σ : Type*} [Primcodable α] [Primcodable β] [Primcodable σ]

lemma dom_bool {f : Bool → α} : Computable f := (Primrec.dom_bool f).to_comp

lemma dom_bool₂ {f : Bool → Bool → α} : Computable₂ f := (Primrec.dom_bool₂ f).to_comp

lemma _root_.Computable₂.left : Computable₂ fun (a : α) (_ : β) => a := .fst

lemma _root_.Computable₂.right : Computable₂ fun (_ : α) (b : β) => b := .snd

lemma to₂' {f : α → β → σ} (hf : Computable (fun p => f p.1 p.2 : α × β → σ)) : Computable₂ f := hf

lemma list_all {α : Type*} {β : Type*} [Primcodable α] [Primcodable β]
  {p : α → β → Bool} {l : α → List β} (hp : Computable₂ p) (hl : Computable l) : Computable (fun a => (l a).all (p a)) := by
  let f : α → ℕ → Bool := fun a n => n.recOn true (fun m ih => ((l a).reverse.get? m).casesOn false (fun b => p a b && ih))
  have : Computable₂ (fun q₁ q₂ => ((l q₁.1).reverse.get? q₂.1).casesOn false (fun b => p q₁.1 b && q₂.2)
    : α × ℕ → ℕ × Bool → Bool) :=
    to₂' <| option_casesOn
      (list_get?.comp (list_reverse.comp $ hl.comp $ fst.comp fst) (fst.comp snd))
      (const false) (by apply dom_bool₂.comp₂ (hp.comp₂ (fst.comp₂ $ fst.comp₂ .left) .right) (snd.comp₂ $ snd.comp₂ .left))
  have hf : Computable₂ f := (nat_rec snd (const true) this).to₂
  have := hf.comp Computable.id (list_length.comp hl)
  exact this.of_eq <| by
    intro a; simp
    generalize l a = l
    induction' l with b l ih <;> simp
    { have : List.get? (List.reverse l ++ [b]) (List.length l) = some b := by
        simpa using List.get?_concat_length l.reverse b
      simp[this]; rw[←ih]
      exact congr_arg₂ (· && ·) rfl (Nat.rec_eq _ _ _ _ (by
        intro m hm k
        have : (l.reverse ++ [b]).get? m = l.reverse.get? m := List.get?_append (by simp[hm])
        simp[this])) }

end Computable

namespace Partrec

variable {α : Type*} {β : Type*} {σ : Type*} [Primcodable α] [Primcodable β] [Primcodable σ]

noncomputable def _root_.PFun.merge (f g : α →. σ) : α →. σ :=
  Classical.epsilon (fun k => ∀ a x, x ∈ k a ↔ x ∈ f a ∨ x ∈ g a)

lemma merge_iff {f g : α →. σ} (hf : Partrec f) (hg : Partrec g)
  (H : ∀ (a), ∀ x ∈ f a, ∀ y ∈ g a, x = y) {a x} :
    x ∈ PFun.merge f g a ↔ x ∈ f a ∨ x ∈ g a := by
  rcases merge hf hg H with ⟨k, _, hk⟩
  exact Classical.epsilon_spec (p := fun k => ∀ a x, x ∈ k a ↔ x ∈ f a ∨ x ∈ g a) ⟨k, hk⟩ a x

lemma mergep {f g : α →. σ} (hf : Partrec f) (hg : Partrec g)
  (H : ∀ (a), ∀ x ∈ f a, ∀ y ∈ g a, x = y) :
    Partrec (PFun.merge f g) := by
  rcases merge hf hg H with ⟨k, pk, hk⟩
  exact pk.of_eq fun a => by ext a; simp[hk, merge_iff hf hg H]

end Partrec
