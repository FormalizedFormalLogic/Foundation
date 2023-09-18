import Logic.Vorspiel.Computability
import Logic.Vorspiel.StrongRec

attribute [-instance] WType.instEncodableWType Encodable.finPi Encodable.fintypeArrowOfEncodable

namespace WType

section elimv

variable {α σ γ : Type*} {β : α → Type*}

def elimv (fs : σ → σ) (fγ : σ → (Σ a : α, β a → γ) → γ) : σ → WType β → γ
  | x, ⟨a, f⟩ => fγ x ⟨a, fun b => elimv fs fγ (fs x) (f b)⟩

lemma elimv_eq_elim {fγ : σ → (Σ a : α, β a → γ) → γ} : elimv id fγ a = elim γ (fγ a) := by
  funext w; induction' w with a f ih; simp[elim, elimv, ih]

lemma elimv_eq_elimv (fs : τ → σ → σ) (fγ : τ → σ → (Σ a : α, β a → γ) → γ) (x z) :
    elimv (fs x) (fγ x) z = elimv (fun (p : τ × σ) => (p.1, fs p.1 p.2)) (fun (p : τ × σ) => fγ p.1 p.2) (x, z) := by
  funext w; induction w generalizing x z; simp[elimv, *]

end elimv

open Encodable Primrec Primcodable UniformlyPrimcodable
variable {α : Type*} {β : α → Type*}
  [Primcodable α] [(a : α) → Fintype (β a)] [(a : α) → DecidableEq (β a)] [(a : α) → Primcodable (β a)] [PrimrecCard β]

def elimOpt (γ : Type*) (fγ : (Σ a : α, β a → γ) → Option γ) : WType β → Option γ
  | ⟨a, f⟩ => (toFinArrowOpt (fun b => elimOpt γ fγ (f b))).bind fun g => fγ ⟨a, g⟩

def SubWType {α : Type*} (β : α → Type*)
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

def elimv' {σ : Type*} {γ : Type*} (fs : σ → σ) (fγ : σ → (Σ a : α, β a → γ) → γ) (s) :
    σ → SubWType β s → γ := fun x ⟨t, _⟩ => t.elimv fs fγ x

lemma elimv_const {w₁ : SubWType β s₁} {w₂ : SubWType β s₂} (h : w₁.val = w₂.val) (γ) (fγ : (Σ a : α, β a → γ) → γ) : 
    elim' γ fγ s₁ w₁ = elim' γ fγ s₂ w₂ := by
  rcases w₁ with ⟨w, hw₁⟩
  rcases w₂ with ⟨w, hw₂⟩
  simp at h; rcases h with rfl
  simp[elim']

lemma elimv'_eq_elim' {fγ : σ → (Σ a : α, β a → γ) → γ} (s) : elimv' id fγ s a = elim' γ (fγ a) s := by
  funext ⟨w, _⟩; simp[elim', elimv', elimv_eq_elim]

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

section elimDecode

variable {σ : Type*} {γ : Type*}
variable (β)

def elimDecode (f : α → List γ → γ) : ℕ → ℕ → Option γ :=
 fun s e => (decode e : Option (SubWType β s)).map (elim' γ (fun ⟨a, v⟩ => f a (List.ofFn $ fintypeArrowEquivFinArrow v)) s)

def elimvDecode (fs : σ → σ) (f : σ → α → List γ → γ) : σ → ℕ → ℕ → Option γ :=
 fun x s e => (decode e : Option (SubWType β s)).map
   (elimv' fs (fun x ⟨a, v⟩ => f x a (List.ofFn $ fintypeArrowEquivFinArrow v)) s x)

lemma elimvDecode_eq_induction (fs : σ → σ) (f : σ → α → List γ → γ) (x s e) :
    elimvDecode β fs f x s e =
    Nat.casesOn s none
      (fun s => (decode e.unpair.1 : Option α).bind
        $ fun a => (((Denumerable.ofNat (List ℕ) e.unpair.2).mapM' (elimvDecode β fs f (fs x) s)).bind
          $ fun l => if l.length = Fintype.card (β a) then some l else none).map
            $ fun v => f x a v) := by
  rcases s with (_ | s)
  · simp[elimvDecode]
  · simp[elimvDecode, SubWType.decode_succ, Option.map_bind', decode_list, Function.comp, List.mapM'_option_map]; congr
    funext a
    rcases hw : List.mapM' (decode : ℕ → Option (SubWType β s)) (Denumerable.ofNat (List ℕ) e.unpair.2) with (_ | w) <;> simp
    { simp[List.toVector]
      by_cases hlw : w.length = Fintype.card (β a) <;> simp[hlw, elimv, elimv']
      { simp[Vector.get_mk_eq_get, List.ofFn_get_eq_map]; congr
        rw[Encodable.fintypeArrowEquivFinArrow_fintypeEquivFin (fun i => WType.elimv fs _ (fs x) (w.get (i.cast hlw.symm)).val),
          List.ofFn_get_eq_map (fun z => WType.elimv fs _ (fs x) z.val) w]; rfl } }

@[reducible]
private def elimvDecodeG (f : α → List γ → γ) : ℕ × ℕ → List (Option γ) → Option γ := fun (s, e) ih =>
  Nat.casesOn s none
    (fun _ => (decode e.unpair.1 : Option α).bind
      $ fun a => (((Denumerable.ofNat (List ℕ) e.unpair.2).mapM' (fun c => ih.getI c)).bind
        $ fun l => if l.length = Fintype.card (β a) then some l else none).map
          $ fun v => f a v)

private lemma elimvDecodeG_eq_elimvDecode (fs : σ → σ) (f : σ → α → List γ → γ) (x s e) :
    elimvDecodeG β (f x) (s, e) ((List.range e).map (elimvDecode β fs f (fs x) s.pred)) =
    elimvDecode β fs f x s e := by
  simp[elimvDecode_eq_induction β fs f x s e, elimvDecodeG]
  rcases s with (_ | s) <;> simp; congr
  funext a
  have : mapM' (fun c => ((List.range e).map $ elimvDecode β fs f (fs x) s).getI c)
      (Denumerable.ofNat (List ℕ) e.unpair.2) =
    mapM' (elimvDecode β fs f (fs x) s) (Denumerable.ofNat (List ℕ) e.unpair.2) :=
  List.mapM'_eq_mapM'_of_eq _ (by
  { intro c hc
    have : c < e := by
      have : c < e.unpair.2 := Denumerable.lt_of_mem_list _ _ hc
      exact lt_of_lt_of_le this (Nat.unpair_right_le e)
    simp[List.getI_map_range _ this] })
  rw[this]

variable [Primcodable σ] [Primcodable γ]

private lemma elimvDecodeG_primrec {f : σ → α × List γ → γ} (hf : Primrec₂ f) :
    Primrec₂ (fun p ih => elimvDecodeG β (fun a ih => f p.1.1 (a, ih)) (p.1.2, p.2) ih
      : (σ × ℕ) × ℕ → List (Option γ) → Option γ) :=
  to₂' <| nat_casesOn (snd.comp $ fst.comp fst) (const _)
    <| to₂' <| option_bind
      (Primrec.decode.comp $ fst.comp $ unpair.comp $ snd.comp $ fst.comp fst)
      <| to₂' <| option_map
        (option_bind
          (option_list_mapM'
            ((Primrec.ofNat _).comp $ snd.comp $ unpair.comp $ snd.comp $ fst.comp $ fst.comp fst)
            (list_getI.comp₂ (snd.comp₂ $ fst.comp₂ $ fst.comp₂ Primrec₂.left) Primrec₂.right))
          (to₂' $ Primrec.ite
            (Primrec.eq.comp (list_length.comp snd) (PrimrecCard.card_prim.comp $ snd.comp fst))
            (option_some.comp snd) (const _)))
        (hf.comp₂ (fst.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ $ fst.comp₂ $ Primrec₂.left)
          (Primrec₂.pair.comp₂ (snd.comp₂ Primrec₂.left) Primrec₂.right))

lemma primrec_elimvDecode {fs : σ → σ} {f : σ → α × List γ → γ} (hfs : Primrec fs) (hf : Primrec₂ f) :
    Primrec₂ (fun x p => elimvDecode β fs (fun x a ih => f x (a, ih)) x p.1 p.2 : σ → ℕ × ℕ → Option γ) := by
  let F : σ × ℕ → ℕ → Option γ := (fun p e => elimvDecode β fs (fun x a ih => f x (a, ih)) p.1 p.2 e)
  have := nat_one_side_strong_rec F (option_some.comp₂ (elimvDecodeG_primrec β hf))
    (Primrec₂.pair.comp (hfs.comp fst) (pred.comp snd))
    (fun (x, s) e => by
      simpa using elimvDecodeG_eq_elimvDecode β fs (fun x a ih => f x (a, ih)) x s e)
  exact this.comp₂ (Primrec₂.pair.comp₂ Primrec₂.left (fst.comp₂ Primrec₂.right)) (snd.comp₂ Primrec₂.right)

lemma primrec_elimDecode {f : α → List γ → γ} (hf : Primrec₂ f) :
    Primrec₂ (fun s e => elimDecode β f s e : ℕ → ℕ → Option γ) := by
  have : Primrec₂ (fun _ p => f p.1 p.2 : Unit → α × List γ → γ) :=
    hf.comp₂ (fst.comp₂ Primrec₂.right) (snd.comp₂ Primrec₂.right)
  have H := primrec_elimvDecode β (fs := (id : Unit → Unit)) Primrec.id this
  have : Primrec₂ (fun _ e => (e, ()) : ℕ → ℕ → ℕ × Unit) := (Primrec₂.pair.comp₂ Primrec₂.right (Primrec₂.const ()))
  exact (H.comp₂ (Primrec₂.const ()) (Primrec₂.pair.comp₂ Primrec₂.left Primrec₂.right)).of_eq <|
    by intro s e; simp[elimvDecode, elimDecode, elimv'_eq_elim']

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
  elim γ (fun ⟨a, v⟩ => f a (List.ofFn $ fintypeArrowEquivFinArrow v))

def elimvL (fs : σ → σ) (f : σ → α → List γ → γ) : σ → WType β → γ :=
  elimv fs (fun x ⟨a, v⟩ => f x a (List.ofFn $ fintypeArrowEquivFinArrow v))

lemma elimL_mk (f : α → List γ → γ) (a : α) (v : β a → WType β) :
    elimL f ⟨a, v⟩ = f a (List.ofFn $ fintypeArrowEquivFinArrow $ fun b => elimL f (v b)) := by simp[elimL, elim]

lemma elimvL_mk (fs : σ → σ) (f : σ → α → List γ → γ) (a : α) (v : β a → WType β) :
    elimvL fs f x ⟨a, v⟩ = f x a (List.ofFn $ fintypeArrowEquivFinArrow $ fun b => elimvL fs f (fs x) (v b)) := by
  simp[elimvL, elimv]

lemma elim_eq_elimL [Inhabited γ] (f : (a : α) × (β a → γ) → γ) :
    elim γ f w = elimL (fun a l => f ⟨a, fintypeArrowEquivFinArrow.symm (fun i => l.getI i)⟩) w := by
  simp[elimL]; congr; funext ⟨a, j⟩; simp; congr; funext b; simp

lemma decode_elimL_eq (f : α → List γ → γ) :
    (decode e : Option (WType β)).map (elimL f) = (SubWType.elimDecode β f e.unpair.1 e.unpair.2) := by
  simp[elimL, decode_eq, Function.comp, SubWType.elimDecode, SubWType.elim']
  rcases (decode e.unpair.2) with (_ | ⟨_, _⟩) <;> simp[SubWType.toW]

lemma decode_elimvL_eq (fs : σ → σ) (f : σ → α → List γ → γ) :
    (decode e : Option (WType β)).map (elimvL fs f x) = (SubWType.elimvDecode β fs f x e.unpair.1 e.unpair.2) := by
  simp[elimvL, decode_eq, Function.comp, SubWType.elimvDecode, SubWType.elimv']
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
variable {τ σ α γ : Type*} {β : α → Type*}
  [Primcodable τ] [Primcodable σ] [Primcodable α] [(a : α) → Fintype (β a)]
  [(a : α) → DecidableEq (β a)] [(a : α) → Primcodable (β a)] [PrimrecCard β] [Primcodable γ]

lemma w_depth : Primrec (fun w => w.depth : WType β → ℕ) := by
  have : Primrec (fun n => (encodeDecode (WType β) n).map $ fun e => e.unpair.1) :=
    option_map Primrec.encodeDecode (fst.comp₂ $ Primrec.unpair.comp₂ Primrec₂.right)
  exact decode_iff.mp (this.of_eq $ fun n => by
    simp[encodeDecode_eq_encode_map_decode]
    rcases decode n <;> simp[WType.encode_eq, WType.SubWType.ofW])

lemma w_elimL {f : α → List γ → γ} (hf : Primrec₂ f) : Primrec (elimL f : WType β → γ) :=
  decode_iff.mp (by simp[decode_elimL_eq]; apply SubWType.primrec_elimDecode β hf)

lemma w_elimvL {fs : σ → σ} {f : σ → α × List γ → γ}
  (hfs : Primrec fs) (hf : Primrec₂ f) : Primrec₂ (elimvL fs (fun x a v => f x (a, v)) : σ → WType β → γ) :=
  Primrec₂.decode_iff₂.mp (by
    simp[decode_elimvL_eq]
    exact (SubWType.primrec_elimvDecode β hfs hf).comp₂ Primrec₂.left
      (Primrec₂.pair.comp₂
        (fst.comp₂ $ unpair.comp₂ Primrec₂.right)
        (snd.comp₂ $ unpair.comp₂ Primrec₂.right)))

lemma w_elimvL_param {fs : τ → σ → σ} {f : τ → σ × (α × List γ) → γ} {s : τ → σ} {g : τ → WType β}
  (hfs : Primrec₂ fs) (hf : Primrec₂ f) (hs : Primrec s) (hg : Primrec g) :
    Primrec (fun x => elimvL (fs x) (fun z a l => f x (z, a, l)) (s x) (g x)) := by
  have := (w_elimvL (β := β)
      (Primrec₂.pair.comp fst (hfs.comp fst snd))
      (hf.comp₂ (fst.comp₂ Primrec₂.left) (Primrec₂.pair.comp₂ (snd.comp₂ Primrec₂.left) Primrec₂.right))).comp
    (Primrec₂.pair.comp Primrec.id hs) hg
  apply this.of_eq <| by
    intro x; simp[elimvL]; apply congr_fun; exact Eq.symm <|
      elimv_eq_elimv fs (fun x z (p : Σ a, β a → γ) => f x (z, p.1, List.ofFn $ fintypeArrowEquivFinArrow p.2)) x (s x)

-- TODO: delete
lemma w_elimvL_param' {fs : τ → σ → σ} {f : τ → σ → α → List γ → γ} {s : τ → σ} {g : τ → WType β}
  (hfs : Primrec₂ fs) (hf : Primrec₂ (fun (p : τ × σ) (q : α × List γ) => f p.1 p.2 q.1 q.2)) (hs : Primrec s) (hg : Primrec g) :
    Primrec (fun x => elimvL (fs x) (f x) (s x) (g x)) := by
  have := ((w_elimvL (β := β) (Primrec₂.pair.comp fst (hfs.comp fst snd)) hf)).comp
    (Primrec₂.pair.comp Primrec.id hs) hg
  exact this.of_eq <| by
    intro x; simp[elimvL]; exact Eq.symm <|
      congr_fun (elimv_eq_elimv fs (fun x z (p : Σ a, β a → γ) => f x z p.1 (List.ofFn $ fintypeArrowEquivFinArrow p.2)) x (s x)) _

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

end Primrec