import Arithmetization.ISigmaOne.Metamath.Formula.Typed
import Arithmetization.ISigmaOne.Metamath.Proof.Derivation
import Logic.Logic.HilbertStyle.Supplemental

/-!

# Typed Formalized Tait-Calculus

-/

noncomputable section

namespace LO.Arith

open FirstOrder FirstOrder.Arith

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

variable {L : Arith.Language V} {pL : LDef} [Arith.Language.Defined L pL]

section typed_formula

abbrev Language.TSemiformula.substs₁ (p : L.TSemiformula (0 + 1)) (t : L.TTerm) : L.TFormula := p.substs t.sing

abbrev Language.TSemiformula.free (p : L.TSemiformula (0 + 1)) : L.TFormula := p.shift.substs₁ (L.fvar 0)

@[simp] lemma Language.TSemiformula.val_substs₁ (p : L.TSemiformula (0 + 1)) (t : L.TTerm) :
    (p.substs₁ t).val = L.substs 0 ?[t.val] p.val := by simp [substs₁, substs]

@[simp] lemma Language.TSemiformula.val_free (p : L.TSemiformula (0 + 1)) :
    p.free.val = L.substs 0 ?[^&0] (L.shift p.val) := by simp [free, substs₁, substs, shift, fvar]

@[simp] lemma substs₁_neg (p : L.TSemiformula (0 + 1)) (t : L.TTerm) :
    (~p).substs₁ t = ~(p.substs₁ t) := by simp [Language.TSemiformula.substs₁]

@[simp] lemma substs₁_all (p : L.TSemiformula (0 + 1 + 1)) (t : L.TTerm) :
    p.all.substs₁ t = (p.substs t.sing.q).all := by simp [Language.TSemiformula.substs₁]

@[simp] lemma substs₁_ex (p : L.TSemiformula (0 + 1 + 1)) (t : L.TTerm) :
    p.ex.substs₁ t = (p.substs t.sing.q).ex := by simp [Language.TSemiformula.substs₁]

end typed_formula

section typed_theory

abbrev Language.Theory.tmem (p : L.TFormula) (T : L.Theory) : Prop := p.val ∈ T

scoped infix:50 " ∈' " => Language.Theory.tmem

end typed_theory

section typed_sequent

variable (L)

structure Language.Sequent where
  val : V
  val_formulaSet : L.FormulaSet val

attribute [simp] Language.Sequent.val_formulaSet

variable {L}

instance : EmptyCollection L.Sequent := ⟨⟨∅, by simp⟩⟩

instance : Singleton L.TFormula L.Sequent := ⟨fun p ↦ ⟨{p.val}, by simp⟩⟩

instance : Insert L.TFormula L.Sequent := ⟨fun p Γ ↦ ⟨insert p.val Γ.val, by simp⟩⟩

instance : Union L.Sequent := ⟨fun Γ Δ ↦ ⟨Γ.val ∪ Δ.val, by simp⟩⟩

instance : Membership L.TFormula L.Sequent := ⟨(·.val ∈ ·.val)⟩

instance : HasSubset L.Sequent := ⟨(·.val ⊆ ·.val)⟩

scoped infixr:50 " ⫽ " => Insert.insert

namespace Language.Sequent

variable {Γ Δ : L.Sequent} {p q : L.TFormula}

lemma mem_iff : p ∈ Γ ↔ p.val ∈ Γ.val := iff_of_eq rfl

lemma subset_iff : Γ ⊆ Δ ↔ Γ.val ⊆ Δ.val := iff_of_eq rfl

@[simp] lemma val_empty : (∅ : L.Sequent).val = ∅ := rfl

@[simp] lemma val_singleton (p : L.TFormula) : ({p} : L.Sequent).val = {p.val} := rfl

@[simp] lemma val_insert (p : L.TFormula) (Γ : L.Sequent) : (insert p Γ).val = insert p.val Γ.val := rfl

@[simp] lemma val_union (Γ Δ : L.Sequent) : (Γ ∪ Δ).val = Γ.val ∪ Δ.val := rfl

@[simp] lemma not_mem_empty (p : L.TFormula) : p ∉ (∅ : L.Sequent) := by simp [mem_iff]

@[simp] lemma mem_singleton_iff : p ∈ ({q} : L.Sequent) ↔ p = q := by simp [mem_iff, Language.TSemiformula.val_inj]

@[simp] lemma mem_insert_iff : p ∈ insert q Γ ↔ p = q ∨ p ∈ Γ := by simp [mem_iff, Language.TSemiformula.val_inj]

@[simp] lemma mem_union_iff : p ∈ Γ ∪ Δ ↔ p ∈ Γ ∨ p ∈ Δ := by simp [mem_iff, Language.TSemiformula.val_inj]

@[ext] lemma ext (h : ∀ x, x ∈ Γ ↔ x ∈ Δ) : Γ = Δ := by
  rcases Γ with ⟨Γ, hΓ⟩; rcases Δ with ⟨Δ, hΔ⟩; simp
  apply mem_ext; intro x
  constructor
  · intro hx; simpa using mem_iff.mp <| (h ⟨x, hΓ x hx⟩ |>.1 (by simp [mem_iff, hx]))
  · intro hx; simpa using mem_iff.mp <| (h ⟨x, hΔ x hx⟩ |>.2 (by simp [mem_iff, hx]))

lemma ext' (h : Γ.val = Δ.val) : Γ = Δ := by rcases Γ; rcases Δ; simpa using h

def shift (s : L.Sequent) : L.Sequent := ⟨L.setShift s.val, by simp⟩

@[simp] lemma shift_empty : (∅ : L.Sequent).shift = ∅ := ext' <| by simp [shift]

@[simp] lemma shift_insert : (insert p Γ).shift = insert p.shift Γ.shift := ext' <| by simp [shift]

end Language.Sequent

end typed_sequent

section typed_derivation

variable (L)

structure Language.TTheory where
  thy : L.Theory
  pthy : pL.TDef
  [defined : thy.Defined pthy]

instance (T : Language.TTheory L) : T.thy.Defined T.pthy := T.defined

variable {L}

structure Language.Theory.TDerivation (T : Language.TTheory L) (Γ : L.Sequent) where
  derivation : V
  derivationOf : T.thy.DerivationOf derivation Γ.val

scoped infix:45 " ⊢¹ " => Language.Theory.TDerivation

def Language.Theory.TProof (T : Language.TTheory L) (p : L.TFormula) := T ⊢¹ insert p ∅

instance : System L.TFormula L.TTheory := ⟨Language.Theory.TProof⟩

variable {T : L.TTheory}

def Language.Theory.Derivable.toTDerivation (Γ : L.Sequent) (h : T.thy.Derivable Γ.val) : T ⊢¹ Γ := by
  choose a ha using h; choose d hd using ha.2
  exact ⟨a, ha.1, d, hd⟩

lemma Language.Theory.TDerivation.toDerivable {Γ : L.Sequent} (d : T ⊢¹ Γ) : T.thy.Derivable Γ.val :=
  ⟨d.derivation, d.derivationOf⟩

lemma Language.Theory.TProvable.iff_provable {σ : L.TFormula} :
    T ⊢! σ ↔ T.thy.Provable σ.val := by
  constructor
  · intro b
    simpa [←singleton_eq_insert] using Language.Theory.TDerivation.toDerivable b.get
  · intro h
    exact ⟨Language.Theory.Derivable.toTDerivation _ <| by simpa [←singleton_eq_insert] using h⟩

def Language.Theory.TDerivation.toTProof {p} (d : T ⊢¹ insert p ∅) : T ⊢ p := d

def Language.Theory.TProof.toTDerivation {p} (d : T ⊢ p) : T ⊢¹ insert p ∅ := d

namespace Language.Theory.TDerivation

variable {Γ Δ : L.Sequent} {p q p₀ p₁ p₂ p₃ p₄ : L.TFormula}

def byAxm (p) (h : p ∈' T.thy) (hΓ : p ∈ Γ) : T ⊢¹ Γ :=
  Language.Theory.Derivable.toTDerivation _
    <| Language.Theory.Derivable.by_axm (by simp) _ hΓ h

def em (p) (h : p ∈ Γ := by simp) (hn : ~p ∈ Γ := by simp) : T ⊢¹ Γ :=
  Language.Theory.Derivable.toTDerivation _
    <| Language.Theory.Derivable.em (by simp) p.val (Language.Sequent.mem_iff.mp h) (by simpa using Language.Sequent.mem_iff.mp hn)

def verum (h : ⊤ ∈ Γ := by simp) : T ⊢¹ Γ :=
  Language.Theory.Derivable.toTDerivation _
    <| Language.Theory.Derivable.verum (by simp) (by simpa using Language.Sequent.mem_iff.mp h)

def and (dp : T ⊢¹ insert p Γ) (dq : T ⊢¹ insert q Γ) : T ⊢¹ insert (p ⋏ q) Γ :=
  Language.Theory.Derivable.toTDerivation _
    <| by simpa using Language.Theory.Derivable.and (by simpa using dp.toDerivable) (by simpa using dq.toDerivable)

def or (dpq : T ⊢¹ insert p (insert q Γ)) : T ⊢¹ insert (p ⋎ q) Γ :=
  Language.Theory.Derivable.toTDerivation _ <| by simpa using Language.Theory.Derivable.or (by simpa using dpq.toDerivable)

def all {p : L.TSemiformula (0 + 1)} (dp : T ⊢¹ insert p.free Γ.shift) : T ⊢¹ insert p.all Γ :=
  Language.Theory.Derivable.toTDerivation _ <| by
    simpa using Language.Theory.Derivable.all (by simpa using p.prop) (by simpa using dp.toDerivable)

def ex {p : L.TSemiformula (0 + 1)} (t : L.TTerm) (dp : T ⊢¹ insert (p.substs₁ t) Γ) : T ⊢¹ insert p.ex Γ :=
  Language.Theory.Derivable.toTDerivation _ <| by
    simpa using Language.Theory.Derivable.ex (by simpa using p.prop) t.prop (by simpa using dp.toDerivable)

def wk (d : T ⊢¹ Δ) (h : Δ ⊆ Γ) : T ⊢¹ Γ :=
  Language.Theory.Derivable.toTDerivation _ <| by
    simpa using Language.Theory.Derivable.wk (by simp) (Language.Sequent.subset_iff.mp h) (by simpa using d.toDerivable)

def shift (d : T ⊢¹ Γ) : T ⊢¹ Γ.shift :=
  Language.Theory.Derivable.toTDerivation _ <| by
    simpa using Language.Theory.Derivable.shift (by simpa using d.toDerivable)

def cut (d₁ : T ⊢¹ insert p Γ) (d₂ : T ⊢¹ insert (~p) Γ) : T ⊢¹ Γ :=
  Language.Theory.Derivable.toTDerivation _ <| by
    simpa using Language.Theory.Derivable.cut p.val (by simpa using d₁.toDerivable) (by simpa using d₂.toDerivable)

def cut' (d₁ : T ⊢¹ insert p Γ) (d₂ : T ⊢¹ insert (~p) Δ) : T ⊢¹ Γ ∪ Δ :=
  cut (p := p) (d₁.wk (by intro x; simp; tauto)) (d₂.wk (by intro x; simp; tauto))

def conj (ps : L.TSemiformulaVec 0) (ds : ∀ i, (hi : i < len ps.val) → T ⊢¹ insert (ps.nth i hi) Γ) : T ⊢¹ insert ps.conj Γ := by
  have : ∀ i < len ps.val, T.thy.Derivable (insert (ps.val.[i]) Γ.val) := by intro i hi; simpa using (ds i hi).toDerivable
  have : T.thy.Derivable (insert (^⋀ ps.val) Γ.val) := Language.Theory.Derivable.conj ps.val (by simp) this
  exact Language.Theory.Derivable.toTDerivation _ (by simpa using this)

def disj (ps : L.TSemiformulaVec 0) {i} (hi : i < len ps.val)
    (d : T ⊢¹ insert (ps.nth i hi) Γ) : T ⊢¹ insert ps.disj Γ := by
  have : T.thy.Derivable (insert (^⋁ ps.val) Γ.val) :=
    Language.Theory.Derivable.disj ps.val Γ.val ps.prop hi (by simpa using d.toDerivable)
  apply Language.Theory.Derivable.toTDerivation _ (by simpa using this)

def modusPonens (dpq : T ⊢¹ insert (p ⟶ q) Γ) (dp : T ⊢¹ insert p Γ) : T ⊢¹ insert q Γ := by
  let d : T ⊢¹ insert (p ⟶ q) (insert q Γ) := dpq.wk (insert_subset_insert_of_subset _ <| by simp)
  let b : T ⊢¹ insert (~(p ⟶ q)) (insert q Γ) := by
    simp only [TSemiformula.imp_def, TSemiformula.neg_or, TSemiformula.neg_neg]
    exact and (dp.wk (insert_subset_insert_of_subset _ <| by simp))
      (em q (by simp) (by simp))
  exact cut d b

def ofEq (d : T ⊢¹ Γ) (h : Γ = Δ) : T ⊢¹ Δ := h ▸ d

def rotate₁ (d : T ⊢¹ p₀ ⫽ p₁ ⫽ Γ) : T ⊢¹ p₁ ⫽ p₀ ⫽ Γ :=
  ofEq d (by ext x; simp; tauto)

def rotate₂ (d : T ⊢¹ p₀ ⫽ p₁ ⫽ p₂ ⫽ Γ) : T ⊢¹ p₂ ⫽ p₁ ⫽ p₀ ⫽ Γ :=
  ofEq d (by ext x; simp; tauto)

def rotate₃ (d : T ⊢¹ p₀ ⫽ p₁ ⫽ p₂ ⫽ p₃ ⫽ Γ) : T ⊢¹ p₃ ⫽ p₁ ⫽ p₂ ⫽ p₀ ⫽ Γ :=
  ofEq d (by ext x; simp; tauto)

def orInv (d : T ⊢¹ p ⋎ q ⫽ Γ) : T ⊢¹ p ⫽ q ⫽ Γ := by
  have b : T ⊢¹ p ⋎ q ⫽ p ⫽ q ⫽ Γ := wk d (by intro x; simp; tauto)
  have : T ⊢¹ ~(p ⋎ q) ⫽ p ⫽ q ⫽ Γ := by
    simp only [TSemiformula.neg_or]
    apply and (em p) (em q)
  exact cut b this

def specialize {p : L.TSemiformula (0 + 1)} (b : T ⊢¹ p.all ⫽ Γ) (t : L.TTerm) : T ⊢¹ p.substs₁ t ⫽ Γ := by
  apply TDerivation.cut (p := p.all)
  · exact (TDerivation.wk b <| by intro x; simp; tauto)
  · rw [TSemiformula.neg_all]
    apply TDerivation.ex t
    apply TDerivation.em (p.substs₁ t)

end Language.Theory.TDerivation

namespace Language.Theory.TProof

variable {T : L.TTheory} {p q : L.TFormula}

/-- Condition D2 -/
def modusPonens (d : T ⊢ p ⟶ q) (b : T ⊢ p) : T ⊢ q := TDerivation.modusPonens d b

def byAxm {p : L.TFormula} (h : p ∈' T.thy) : T ⊢ p := TDerivation.byAxm p h (by simp)

instance : System.ModusPonens T := ⟨modusPonens⟩

instance : System.NegationEquiv T where
  neg_equiv p := by
    simp [Axioms.NegEquiv, LO.LogicalConnective.iff, TSemiformula.imp_def]
    apply TDerivation.and
    · apply TDerivation.or
      apply TDerivation.rotate₁
      apply TDerivation.or
      exact TDerivation.em p
    · apply TDerivation.or
      apply TDerivation.and
      · exact TDerivation.em p
      · exact TDerivation.verum

instance : System.Minimal T where
  verum := TDerivation.toTProof <| TDerivation.verum
  imply₁ (p q) := by
    simp only [Axioms.Imply₁, TSemiformula.imp_def]
    apply TDerivation.or
    apply TDerivation.rotate₁
    apply TDerivation.or
    exact TDerivation.em p
  imply₂ (p q r) := by
    simp only [Axioms.Imply₂, TSemiformula.imp_def, TSemiformula.neg_or, TSemiformula.neg_neg]
    apply TDerivation.or
    apply TDerivation.rotate₁
    apply TDerivation.or
    apply TDerivation.rotate₁
    apply TDerivation.or
    apply TDerivation.rotate₂
    apply TDerivation.and
    · exact TDerivation.em p
    · apply TDerivation.rotate₃
      apply TDerivation.and
      · exact TDerivation.em p
      · apply TDerivation.and
        · exact TDerivation.em q
        · exact TDerivation.em r
  and₁ (p q) := by
    simp only [Axioms.AndElim₁, TSemiformula.imp_def, TSemiformula.neg_and]
    apply TDerivation.or
    apply TDerivation.or
    exact TDerivation.em p
  and₂ (p q) := by
    simp only [Axioms.AndElim₂, TSemiformula.imp_def, TSemiformula.neg_and]
    apply TDerivation.or
    apply TDerivation.or
    exact TDerivation.em q
  and₃ (p q) := by
    simp only [Axioms.AndInst, TSemiformula.imp_def]
    apply TDerivation.or
    apply TDerivation.rotate₁
    apply TDerivation.or
    apply TDerivation.rotate₁
    apply TDerivation.and
    · exact TDerivation.em p
    · exact TDerivation.em q
  or₁ (p q) := by
    simp only [Axioms.OrInst₁, TSemiformula.imp_def]
    apply TDerivation.or
    apply TDerivation.rotate₁
    apply TDerivation.or
    exact TDerivation.em p
  or₂ (p q) := by
    simp [Axioms.OrInst₂, TSemiformula.imp_def]
    apply TDerivation.or
    apply TDerivation.rotate₁
    apply TDerivation.or
    exact TDerivation.em q
  or₃ (p q r) := by
    simp [Axioms.OrElim, TSemiformula.imp_def]
    apply TDerivation.or
    apply TDerivation.rotate₁
    apply TDerivation.or
    apply TDerivation.rotate₁
    apply TDerivation.or
    apply TDerivation.and
    · apply TDerivation.rotate₃
      apply TDerivation.and
      · exact TDerivation.em p
      · exact TDerivation.em r
    · apply TDerivation.rotate₂
      apply TDerivation.and
      · exact TDerivation.em q
      · exact TDerivation.em r

instance : System.Classical T where
  dne p := by
    simp [Axioms.DNE, TSemiformula.imp_def]
    apply TDerivation.or
    exact TDerivation.em p

def exIntro (p : L.TSemiformula (0 + 1)) (t : L.TTerm) (b : T ⊢ p.substs₁ t) : T ⊢ p.ex := TDerivation.ex t b

lemma ex_intro! (p : L.TSemiformula (0 + 1)) (t : L.TTerm) (b : T ⊢! p.substs₁ t) : T ⊢! p.ex := ⟨exIntro _ t b.get⟩

def specialize {p : L.TSemiformula (0 + 1)} (b : T ⊢ p.all) (t : L.TTerm) : T ⊢ p.substs₁ t := TDerivation.specialize b t

lemma specialize! {p : L.TSemiformula (0 + 1)} (b : T ⊢! p.all) (t : L.TTerm) : T ⊢! p.substs₁ t := ⟨TDerivation.specialize b.get t⟩

def conj (ps : L.TSemiformulaVec 0) (ds : ∀ i, (hi : i < len ps.val) → T ⊢ ps.nth i hi) : T ⊢ ps.conj := TDerivation.conj ps ds

lemma conj! (ps : L.TSemiformulaVec 0) (ds : ∀ i, (hi : i < len ps.val) → T ⊢! ps.nth i hi) : T ⊢! ps.conj := ⟨conj ps fun i hi ↦ (ds i hi).get⟩

def conj' (ps : L.TSemiformulaVec 0) (ds : ∀ i, (hi : i < len ps.val) → T ⊢ ps.nth (len ps.val - (i + 1)) (sub_succ_lt_self hi)) : T ⊢ ps.conj :=
  TDerivation.conj ps <| fun i hi ↦ by
    simpa [sub_succ_lt_selfs hi] using ds (len ps.val - (i + 1)) (by simp [tsub_lt_iff_left (succ_le_iff_lt.mpr hi)])

def conjOr' (ps : L.TSemiformulaVec 0) (q) (ds : ∀ i, (hi : i < len ps.val) → T ⊢ ps.nth (len ps.val - (i + 1)) (sub_succ_lt_self hi) ⋎ q) : T ⊢ ps.conj ⋎ q :=
  TDerivation.or <| TDerivation.conj ps <| fun i hi ↦ by
    simpa [sub_succ_lt_selfs hi] using TDerivation.orInv (ds (len ps.val - (i + 1)) (by simp [tsub_lt_iff_left (succ_le_iff_lt.mpr hi)]))

def disj (ps : L.TSemiformulaVec 0) {i} (hi : i < len ps.val) (d : T ⊢ ps.nth i hi) : T ⊢ ps.disj :=
  TDerivation.disj ps hi d

def shift {p : L.TFormula} (d : T ⊢ p) : T ⊢ p.shift := by simpa using TDerivation.shift d

lemma shift! {p : L.TFormula} (d : T ⊢! p) : T ⊢! p.shift := ⟨by simpa using TDerivation.shift d.get⟩

def all {p : L.TSemiformula (0 + 1)} (dp : T ⊢ p.free) : T ⊢ p.all := TDerivation.all (by simpa using dp)

lemma all! {p : L.TSemiformula (0 + 1)} (dp : T ⊢! p.free) : T ⊢! p.all := ⟨all dp.get⟩

def generalizeAux {C : L.TFormula} {p : L.TSemiformula (0 + 1)} (dp : T ⊢ C.shift ⟶ p.free) : T ⊢ C ⟶ p.all := by
  rw [TSemiformula.imp_def] at dp ⊢
  apply TDerivation.or
  apply TDerivation.rotate₁
  apply TDerivation.all
  exact TDerivation.wk (TDerivation.orInv dp) (by intro x; simp; tauto)

lemma conj_shift (Γ : List L.TFormula) : (⋀Γ).shift = ⋀(Γ.map .shift) := by
    induction Γ using List.induction_with_singleton
    case hnil => simp
    case hsingle => simp [List.conj₂]
    case hcons p ps hps ih =>
      simp [hps, ih]

def generalize {Γ} {p : L.TSemiformula (0 + 1)} (d : Γ.map .shift ⊢[T] p.free) : Γ ⊢[T] p.all := by
  apply System.FiniteContext.ofDef
  apply generalizeAux
  simpa [conj_shift] using System.FiniteContext.toDef d

lemma generalize! {Γ} {p : L.TSemiformula (0 + 1)} (d : Γ.map .shift ⊢[T]! p.free) : Γ ⊢[T]! p.all := ⟨generalize d.get⟩

def specializeWithCtxAux {C : L.TFormula} {p : L.TSemiformula (0 + 1)} (d : T ⊢ C ⟶ p.all) (t : L.TTerm) : T ⊢ C ⟶ p.substs₁ t := by
  rw [TSemiformula.imp_def] at d ⊢
  apply TDerivation.or
  apply TDerivation.rotate₁
  apply TDerivation.specialize
  exact TDerivation.wk (TDerivation.orInv d) (by intro x; simp; tauto)

def specializeWithCtx {Γ} {p : L.TSemiformula (0 + 1)} (d : Γ ⊢[T] p.all) (t) : Γ ⊢[T] p.substs₁ t := specializeWithCtxAux d t

lemma specialize_with_ctx! {Γ} {p : L.TSemiformula (0 + 1)} (d : Γ ⊢[T]! p.all) (t) : Γ ⊢[T]! p.substs₁ t := ⟨specializeWithCtx d.get t⟩

def ex {p : L.TSemiformula (0 + 1)} (t) (dp : T ⊢ p.substs₁ t) : T ⊢ p.ex := TDerivation.ex t (by simpa using dp)

lemma ex! {p : L.TSemiformula (0 + 1)} (t) (dp : T ⊢! p.substs₁ t) : T ⊢! p.ex := ⟨ex t dp.get⟩

end Language.Theory.TProof

end typed_derivation
