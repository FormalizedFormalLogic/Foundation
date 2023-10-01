import Logic.Vorspiel.Computability
import Logic.Vorspiel.StrongRec

attribute [-instance] WType.instEncodableWType Encodable.finPi Encodable.fintypeArrowOfEncodable

namespace WType

open Encodable Primrec Primcodable UniformlyPrimcodable
variable {α : Type*} {β : α → Type*}
  [Primcodable α] [(a : α) → Fintype (β a)] [(a : α) → DecidableEq (β a)] [(a : α) → Primcodable (β a)] [PrimrecCard β]

def inversion : WType β → α × List (WType β)
  | ⟨a, f⟩ => ⟨a, List.ofFn $ fintypeArrowEquivFinArrow f⟩

def elimv {σ γ : Type*} (fs : α → σ → σ) (fγ : σ → (Σ a : α, β a → γ) → γ) : σ → WType β → γ
  | x, ⟨a, f⟩ => fγ x ⟨a, fun b => elimv fs fγ (fs a x) (f b)⟩

def elimOpt (γ : Type*) (fγ : (Σ a : α, β a → γ) → Option γ) : WType β → Option γ
  | ⟨a, f⟩ => (toFinArrowOpt (fun b => elimOpt γ fγ (f b))).bind fun g => fγ ⟨a, g⟩

def SubWType {α : Type*} (β : α → Type*)
  [(a : α) → Fintype (β a)] [(a : α) → Primcodable (β a)] (n : ℕ) := { t : WType β // t.depth ≤ n }

namespace SubWType

@[ext] lemma ext (w₁ w₂ : SubWType β s) : w₁.val = w₂.val → w₁ = w₂ := by
  rcases w₁ with ⟨w₁, h₁⟩
  rcases w₂ with ⟨w₂, h₂⟩
  simp; rintro rfl; apply Subtype.ext (by simp)

def cast {s'} (hs : s = s') (w : SubWType β s) : SubWType β s' := ⟨w.val, by simp[←hs]; exact w.prop⟩

@[simp] def cast_refl (h : s = s) (w : SubWType β s) : cast h w = w := rfl

def mk (a : α) (f : β a → SubWType β s) : SubWType β (s + 1) := ⟨⟨a, fun i => (f i).val⟩, by simp[depth]; intro b; exact (f b).property ⟩

@[simp] lemma cast_mk {s'} (hs : s + 1 = s' + 1) (a : α) (f : β a → SubWType β s) :
  cast hs (mk a f) = mk a (fun i => cast (by apply Nat.succ_inj'.mp hs) (f i)) := rfl

@[simp] lemma cast_mk_one (hs : s + 1 = 1) (a : α) (f : β a → SubWType β s) :
  cast hs (mk a f) = mk a (fun i => cast (by apply Nat.succ_inj'.mp hs) (f i)) := rfl

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

instance _root_.Primcodable.SubWType (n : ℕ) : Primcodable (SubWType β n) :=
  Nat.rec SubWType.primcodable_zero SubWType.primcodable_succ n

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

lemma encode_cast (w : SubWType β s) {s'} (hs : s = s') : encode w = encode (cast hs w) := by
  rcases hs with rfl; simp

section elimDecode

variable {σ : Type*} {γ : Type*}
variable (β)

def elimDecode (f : α → List γ → γ) : ℕ → ℕ → Option γ :=
 fun s e => (decode e : Option (SubWType β s)).map (elim' γ (fun ⟨a, v⟩ => f a (List.ofFn $ fintypeArrowEquivFinArrow v)) s)

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
  to₂' <| Primrec.nat_casesOn (fst.comp $ snd.comp fst) (const none)
    <| to₂' <| option_bind (Primrec.decode.comp $ fst.comp $ unpair.comp $ snd.comp $ snd.comp $ fst.comp fst)
      <| to₂' <| option_map
        (option_bind
          (option_list_mapM'
            ((Primrec.ofNat _).comp $ snd.comp $ unpair.comp $ snd.comp $ snd.comp $ fst.comp $ fst.comp $ fst)
            (to₂' <| list_getI.comp (snd.comp $ fst.comp $ fst.comp fst)
              (Primrec₂.natPair.comp (snd.comp $ fst.comp fst) snd)))
          (to₂' <| Primrec.ite
            (Primrec.eq.comp (list_length.comp snd) (PrimrecCard.card_prim.comp $ snd.comp fst))
            (option_some.comp snd)
            (const none)))
        (to₂' <| hf.comp (fst.comp $ fst.comp $ fst.comp $ fst.comp fst) (Primrec.pair (snd.comp fst) snd))

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
    option_bind (Primrec₂.encodeDecode_u.comp (fst.comp unpair) (snd.comp unpair))
      (option_map (SubWType.depth_decode_primrec.comp (fst.comp $ unpair.comp fst) snd)
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
  elim γ (fun ⟨a, v⟩ => f a (List.ofFn $ fintypeArrowEquivFinArrow v))

lemma elimL_mk (f : α → List γ → γ) (a : α) (v : β a → WType β) :
    elimL f ⟨a, v⟩ = f a (List.ofFn $ fintypeArrowEquivFinArrow $ fun b => elimL f (v b)) := by simp[elimL, elim]

lemma elim_eq_elimL [Inhabited γ] (f : (a : α) × (β a → γ) → γ) :
    elim γ f w = elimL (fun a l => f ⟨a, fintypeArrowEquivFinArrow.symm (fun i => l.getI i)⟩) w := by
  simp[elimL]; congr; funext ⟨a, j⟩; simp; congr; funext b; simp

lemma decode_elimL_eq (f : α → List γ → γ) :
    (decode e : Option (WType β)).map (elimL f) = (SubWType.elimDecode β f e.unpair.1 e.unpair.2) := by
  simp[elimL, decode_eq, Function.comp, SubWType.elimDecode, SubWType.elim']
  rcases (decode e.unpair.2) with (_ | ⟨_, _⟩) <;> simp[SubWType.toW]

def elimvL (fs : α → σ → σ) (fγ : σ → α → List γ → γ) : σ → WType β → γ :=
  elimv fs (fun x ⟨a, v⟩ => fγ x a (List.ofFn $ fintypeArrowEquivFinArrow v))

lemma elimvL_mk (fs : α → σ → σ) (fγ : σ → α → List γ → γ) (a : α) (v : β a → WType β) :
    elimvL fs fγ x ⟨a, v⟩ = fγ x a (List.ofFn $ fintypeArrowEquivFinArrow $ fun b => elimvL fs fγ (fs a x) (v b)) := by simp[elimvL, elimv]

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

lemma mkL_inversion (w : WType β) : mkL (inversion w).1 (inversion w).2 = w := by
  rcases w with ⟨a, f⟩
  simp[inversion, mkL, Fin.castIso_eq_cast]
  funext; simp

end WType

namespace Primrec

open Encodable WType
variable {τ σ α γ : Type*} {β : α → Type*}
  [Primcodable τ] [Primcodable σ] [Primcodable α] [(a : α) → Fintype (β a)]
  [(a : α) → DecidableEq (β a)] [(a : α) → Primcodable (β a)] [PrimrecCard β] [Primcodable γ]

lemma w_depth : Primrec (depth : WType β → ℕ) := by
  have : Primrec (fun n => (encodeDecode (WType β) n).map $ fun e => e.unpair.1) :=
    option_map Primrec.encodeDecode (fst.comp₂ $ unpair.comp₂ Primrec₂.right)
  exact decode_iff.mp (this.of_eq $ fun n => by
    simp[encodeDecode_eq_encode_map_decode]
    rcases decode n <;> simp[WType.encode_eq, WType.SubWType.ofW])

lemma w_elimL {f : α → List γ → γ} (hf : Primrec₂ f) : Primrec (elimL f : WType β → γ) :=
  decode_iff.mp (by simp[decode_elimL_eq]; apply SubWType.primrec_elimDecode β hf)

lemma w_elimL_param {f : σ → α × List γ → γ} {w : σ → WType β} (hf : Primrec₂ f) (hw : Primrec w) :
    Primrec (fun x => elimL (fun p l => f x (p, l)) (w x) : σ → γ) := by
  have : Primrec₂ (fun x w => elimL (fun p l => f x (p, l)) w : σ → WType β → γ) :=
  Primrec₂.decode_iff₂.mp
    (by simp[decode_elimL_eq]
        exact (SubWType.primrec_elimDecode_param β hf).comp₂ Primrec₂.left
          (Primrec.pair (fst.comp $ Primrec.unpair.comp snd) (snd.comp $ Primrec.unpair.comp snd)).to₂)
  exact this.comp Primrec.id hw

lemma w_elim [Inhabited γ] {f : (a : α) × (β a → γ) → γ}
  (hf : Primrec₂ (fun a l => f ⟨a, fintypeArrowEquivFinArrow.symm (fun i => l.getI i)⟩ : α → List γ → γ)) :
    Primrec (WType.elim γ f) := (w_elimL (β := β) hf).of_eq (fun w => by simp[elim_eq_elimL])

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

lemma w_inversion [Inhabited (WType β)] : Primrec (WType.inversion : WType β → α × List (WType β)) := by
  have : Primrec₂ (fun a l => (a, l.map (fun p => (mkL p.1 p.2).get!)) : α → List (α × List (WType β)) → α × List (WType β)) :=
    Primrec₂.pair.comp₂ Primrec₂.left
      (to₂' <| list_map snd (option_get!.comp₂ $ w_mkL.comp₂ (fst.comp₂ $ Primrec₂.right) (snd.comp₂ $ Primrec₂.right)))
  have := w_elimL (β := β) this
  exact this.of_eq <| fun w => by
    induction w
    simp[inversion, elimL_mk, Function.comp]
    funext i; simp[*, mkL_inversion]

lemma w_elimvL_param [Inhabited (WType β)] {fs : τ → α × σ → σ} {fγ : τ → σ × α × List γ → γ} {g : τ → σ} {w : τ → WType β}
  (hfs : Primrec₂ fs) (hfγ : Primrec₂ fγ) (hg : Primrec g) (hw : Primrec w) :
    Primrec (fun z => WType.elimvL (fun a x => fs z (a, x)) (fun x a l => fγ z (x, a, l)) (g z) (w z)) := by
  have : Primrec₂ (fun z (p : σ × WType β) => WType.elimvL (fun a x => fs z (a, x)) (fun x a l => fγ z (x, a, l)) p.1 p.2) :=
    to₂' <| by {
      have hm : Primrec (fun (p : τ × σ × WType β) => p.2.2.depth) := w_depth.comp <| snd.comp snd
      have hl : Primrec (fun (p : τ × σ × WType β) =>
          p.2.2.inversion.2.map (fun w => (p.1, fs p.1 (p.2.2.inversion.1, p.2.1), w))) :=
        list_map (snd.comp $ w_inversion.comp $ snd.comp snd)
          <| Primrec₂.pair.comp (fst.comp fst)
          <| Primrec₂.pair.comp
            (hfs.comp (fst.comp fst)
              (Primrec₂.pair.comp
                (fst.comp $ w_inversion.comp $ snd.comp $ snd.comp fst)
                (fst.comp $ snd.comp fst)))
          <| snd
      have hg : Primrec₂ (fun (p : τ × σ × WType β) (l : List γ) => fγ p.1 (p.2.1, p.2.2.inversion.1, l)) :=
        hfγ.comp₂ (fst.comp₂ Primrec₂.left)
          <| Primrec₂.pair.comp₂ (fst.comp₂ $ snd.comp₂ Primrec₂.left)
          <| Primrec₂.pair.comp₂ (fst.comp₂ $ w_inversion.comp₂ $ snd.comp₂ $ snd.comp₂ Primrec₂.left) Primrec₂.right
      apply strong_rec _ hm hl (option_some.comp₂ hg)
        (by rintro ⟨z, x, ⟨a, f⟩⟩ ⟨z', x', w'⟩
            simp[inversion, Function.comp, List.mem_ofFn]
            rintro rfl rfl i rfl; exact depth_lt_depth_mk _ _ _)
        (by { rintro ⟨z, x, ⟨a, f⟩⟩; simp[inversion, Function.comp, elimvL_mk]
              congr }) }
  exact this.comp Primrec.id (Primrec₂.pair.comp hg hw)

lemma w_elimvL [Inhabited (WType β)] {fs : α → σ → σ} {fγ : σ → α × List γ → γ}
  (hfs : Primrec₂ fs) (hfγ : Primrec₂ fγ) : Primrec₂ (WType.elimvL (β := β) fs (fun x a l => fγ x (a, l))) := to₂' <| by {
  have hfs : Primrec₂ (fun _ p => fs p.1 p.2 : σ × WType β → α × σ → σ) :=
    hfs.comp₂ (fst.comp₂ Primrec₂.right) (snd.comp₂ Primrec₂.right)
  have hfγ : Primrec₂ (fun _ p => fγ p.1 p.2 : σ × WType β → σ × α × List γ → γ) :=
    hfγ.comp₂ (fst.comp₂ Primrec₂.right) (snd.comp₂ Primrec₂.right)
  exact w_elimvL_param hfs hfγ fst snd }
  

end Primrec