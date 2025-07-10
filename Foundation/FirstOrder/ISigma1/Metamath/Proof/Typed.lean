import Foundation.FirstOrder.ISigma1.Metamath.Formula.Typed
import Foundation.FirstOrder.ISigma1.Metamath.Proof.Derivation
import Foundation.Logic.HilbertStyle.Supplemental

/-!
# Typed internal Tait-calculus
-/

namespace LO

open FirstOrder Arithmetic PeanoMinus IOpen ISigma0

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁]

variable {L : Language} [L.Encodable] [L.LORDefinable]

namespace ISigma1.Metamath

section typed_formula

noncomputable abbrev Semiformula.substs1 (p : Semiformula V L (0 + 1)) (t : Term V L) : Formula V L := p.substs t.sing

noncomputable abbrev Semiformula.free (p : Semiformula V L (0 + 1)) : Formula V L := p.shift.substs1 (Semiterm.fvar L 0)

@[simp] lemma Semiformula.val_substs1 (p : Semiformula V L (0 + 1)) (t : Term V L) :
    (p.substs1 t).val = Metamath.substs L ?[t.val] p.val := by simp [substs1, substs]

@[simp] lemma Semiformula.val_free (p : Semiformula V L (0 + 1)) :
    p.free.val = Metamath.substs L ?[^&0] (Metamath.shift L p.val) := by simp [free, substs1, substs, shift]

@[simp] lemma substs1_neg (p : Semiformula V L (0 + 1)) (t : Term V L) :
    (∼p).substs1 t = ∼(p.substs1 t) := by simp [Semiformula.substs1]

@[simp] lemma substs1_all (p : Semiformula V L (0 + 1 + 1)) (t : Term V L) :
    p.all.substs1 t = (p.substs t.sing.q).all := by simp [Semiformula.substs1]

@[simp] lemma substs1_ex (p : Semiformula V L (0 + 1 + 1)) (t : Term V L) :
    p.ex.substs1 t = (p.substs t.sing.q).ex := by simp [Semiformula.substs1]

end typed_formula

section typed_theory

abbrev tmem (p : Formula V L) (T : Theory L) [T.Δ₁Definable] : Prop := p.val ∈ T.Δ₁Class

scoped infix:50 " ∈' " => tmem

end typed_theory

section typed_sequent

variable (V L)

structure Sequent where
  val : V
  val_formulaSet : IsFormulaSet L val

attribute [simp] Sequent.val_formulaSet

variable {V L}

instance : EmptyCollection (Sequent V L) := ⟨⟨∅, by simp⟩⟩

noncomputable instance : Singleton (Formula V L) (Sequent V L) := ⟨fun p ↦ ⟨{p.val}, by simp⟩⟩

noncomputable instance : Insert (Formula V L) (Sequent V L) := ⟨fun p Γ ↦ ⟨insert p.val Γ.val, by simp⟩⟩

noncomputable instance : Union (Sequent V L) := ⟨fun Γ Δ ↦ ⟨Γ.val ∪ Δ.val, by simp⟩⟩

instance : Membership (Formula V L) (Sequent V L) := ⟨fun Γ p ↦ (p.val ∈ Γ.val)⟩

instance : HasSubset (Sequent V L) := ⟨(·.val ⊆ ·.val)⟩

scoped infixr:50 " ⫽ " => Insert.insert

namespace Sequent

variable {Γ Δ : (Sequent V L)} {p q : Formula V L}

lemma mem_iff : p ∈ Γ ↔ p.val ∈ Γ.val := iff_of_eq rfl

lemma subset_iff : Γ ⊆ Δ ↔ Γ.val ⊆ Δ.val := iff_of_eq rfl

@[simp] lemma val_empty : (∅ : (Sequent V L)).val = ∅ := rfl

@[simp] lemma val_singleton (p : Formula V L) : ({p} : (Sequent V L)).val = {p.val} := rfl

@[simp] lemma val_insert (p : Formula V L) (Γ : (Sequent V L)) : (insert p Γ).val = insert p.val Γ.val := rfl

@[simp] lemma val_union (Γ Δ : (Sequent V L)) : (Γ ∪ Δ).val = Γ.val ∪ Δ.val := rfl

@[simp] lemma not_mem_empty (p : Formula V L) : p ∉ (∅ : (Sequent V L)) := by simp [mem_iff]

@[simp] lemma mem_singleton_iff : p ∈ ({q} : (Sequent V L)) ↔ p = q := by simp [mem_iff, Semiformula.val_inj]

@[simp] lemma mem_insert_iff : p ∈ insert q Γ ↔ p = q ∨ p ∈ Γ := by simp [mem_iff, Semiformula.val_inj]

@[simp] lemma mem_union_iff : p ∈ Γ ∪ Δ ↔ p ∈ Γ ∨ p ∈ Δ := by simp [mem_iff]

@[ext] lemma ext (h : ∀ x, x ∈ Γ ↔ x ∈ Δ) : Γ = Δ := by
  rcases Γ with ⟨Γ, hΓ⟩; rcases Δ with ⟨Δ, hΔ⟩
  suffices ∀ x, x ∈ Γ ↔ x ∈ Δ by simpa using mem_ext this
  intro x
  constructor
  · intro hx; simpa using mem_iff.mp <| h ⟨x, hΓ x hx⟩ |>.1 (by simp [mem_iff, hx])
  · intro hx; simpa using mem_iff.mp <| h ⟨x, hΔ x hx⟩ |>.2 (by simp [mem_iff, hx])

lemma ext' (h : Γ.val = Δ.val) : Γ = Δ := by rcases Γ; rcases Δ; simpa using h

noncomputable def shift (s : (Sequent V L)) : (Sequent V L) := ⟨setShift L s.val, by simp⟩

@[simp] lemma shift_empty : (∅ : (Sequent V L)).shift = ∅ := ext' <| by simp [shift]

@[simp] lemma shift_insert : (insert p Γ).shift = insert p.shift Γ.shift := ext' <| by simp [shift]

end Sequent

end typed_sequent

section typed_derivation

/-- Auxiliary theories for the typed internal proof. -/
structure InternalTheory (V : Type*) (L : Language) [L.Encodable] [L.LORDefinable] where
  theory : Theory L
  Δ₁Definable : theory.Δ₁Definable

instance : CoeOut (InternalTheory V L) (Theory L) := ⟨InternalTheory.theory⟩

instance (T : InternalTheory V L) : T.theory.Δ₁Definable := T.Δ₁Definable

variable (V)

def _root_.LO.FirstOrder.Theory.internalize (T : Theory L) [T.Δ₁Definable] : InternalTheory V L := ⟨T, inferInstance⟩

variable {V}

structure TDerivation (T : InternalTheory V L) (Γ : Sequent V L) where
  derivation : V
  derivatioNOf : T.theory.DerivationOf derivation Γ.val

scoped infix:45 " ⊢ᵈᵉʳ " => TDerivation

def TProof (T : InternalTheory V L) (p : Formula V L) := T ⊢ᵈᵉʳ insert p ∅

instance : Entailment (Formula V L) (InternalTheory V L) := ⟨TProof⟩

instance : HasSubset (InternalTheory V L) := ⟨fun T U ↦ T.theory.Δ₁Class (V := V) ⊆ U.theory.Δ₁Class⟩

variable {T U : InternalTheory V L}

noncomputable def _root_.LO.FirstOrder.Theory.Derivable.toTDerivation (Γ : Sequent V L) (h : T.theory.Derivable Γ.val) : T ⊢ᵈᵉʳ Γ := by
  choose a ha using h; choose d hd using ha.2
  exact ⟨a, ha.1, d, hd⟩

lemma TDerivation.toDerivable {Γ : (Sequent V L)} (d : T ⊢ᵈᵉʳ Γ) : T.theory.Derivable Γ.val :=
  ⟨d.derivation, d.derivatioNOf⟩

lemma TProvable.iff_provable {σ : Formula V L} :
    T ⊢! σ ↔ T.theory.Provable σ.val := by
  constructor
  · intro b
    simpa [←singleton_eq_insert] using TDerivation.toDerivable b.get
  · intro h
    exact ⟨Theory.Derivable.toTDerivation _ <| by simpa [←singleton_eq_insert] using h⟩

def TDerivation.toTProof {p} (d : T ⊢ᵈᵉʳ insert p ∅) : T ⊢ p := d

def TDerivation.of_eq (d : T ⊢ᵈᵉʳ Γ) (e : Γ = Δ) : T ⊢ᵈᵉʳ Δ := by rcases e; exact d

def TProof.toTDerivation {p} (d : T ⊢ p) : T ⊢ᵈᵉʳ insert p ∅ := d

namespace TDerivation

variable {Γ Δ : (Sequent V L)} {p q p₀ p₁ p₂ p₃ p₄ : Formula V L}

noncomputable def byAxm (p) (h : p ∈' T.theory) (hΓ : p ∈ Γ) : T ⊢ᵈᵉʳ Γ :=
  Theory.Derivable.toTDerivation _
    <| Theory.Derivable.by_axm (by simp) _ hΓ h

noncomputable def em (p) (h : p ∈ Γ := by simp) (hn : ∼p ∈ Γ := by simp) : T ⊢ᵈᵉʳ Γ :=
  Theory.Derivable.toTDerivation _
    <| Theory.Derivable.em (by simp) p.val (Sequent.mem_iff.mp h) (by simpa using Sequent.mem_iff.mp hn)

noncomputable def verum (h : ⊤ ∈ Γ := by simp) : T ⊢ᵈᵉʳ Γ :=
  Theory.Derivable.toTDerivation _
    <| Theory.Derivable.verum (by simp) (by simpa using Sequent.mem_iff.mp h)

noncomputable def and (dp : T ⊢ᵈᵉʳ insert p Γ) (dq : T ⊢ᵈᵉʳ insert q Γ) : T ⊢ᵈᵉʳ insert (p ⋏ q) Γ :=
  Theory.Derivable.toTDerivation _
    <| by simpa using Theory.Derivable.and (by simpa using dp.toDerivable) (by simpa using dq.toDerivable)

noncomputable def or (dpq : T ⊢ᵈᵉʳ insert p (insert q Γ)) : T ⊢ᵈᵉʳ insert (p ⋎ q) Γ :=
  Theory.Derivable.toTDerivation _ <| by simpa using Theory.Derivable.or (by simpa using dpq.toDerivable)

noncomputable def all {p : Semiformula V L (0 + 1)} (dp : T ⊢ᵈᵉʳ insert p.free Γ.shift) : T ⊢ᵈᵉʳ insert p.all Γ :=
  Theory.Derivable.toTDerivation _ <| by
    simpa using Theory.Derivable.all (by simpa using p.prop) (by simpa using dp.toDerivable)

noncomputable def ex {p : Semiformula V L (0 + 1)} (t : Term V L) (dp : T ⊢ᵈᵉʳ insert (p.substs1 t) Γ) : T ⊢ᵈᵉʳ insert p.ex Γ :=
  Theory.Derivable.toTDerivation _ <| by
    simpa using Theory.Derivable.ex (by simpa using p.prop) t.prop (by simpa using dp.toDerivable)

noncomputable def wk (d : T ⊢ᵈᵉʳ Δ) (h : Δ ⊆ Γ) : T ⊢ᵈᵉʳ Γ :=
  Theory.Derivable.toTDerivation _ <| by
    simpa using Theory.Derivable.wk (by simp) (Sequent.subset_iff.mp h) (by simpa using d.toDerivable)

noncomputable def shift (d : T ⊢ᵈᵉʳ Γ) : T ⊢ᵈᵉʳ Γ.shift :=
  Theory.Derivable.toTDerivation _ <| by
    simpa using Theory.Derivable.shift (by simpa using d.toDerivable)

noncomputable def cut (d₁ : T ⊢ᵈᵉʳ insert p Γ) (d₂ : T ⊢ᵈᵉʳ insert (∼p) Γ) : T ⊢ᵈᵉʳ Γ :=
  Theory.Derivable.toTDerivation _ <| by
    simpa using Theory.Derivable.cut p.val (by simpa using d₁.toDerivable) (by simpa using d₂.toDerivable)

def ofSubset (h : T ⊆ U) (d : T ⊢ᵈᵉʳ Γ) : U ⊢ᵈᵉʳ Γ where
  derivation := d.derivation
  derivatioNOf := ⟨d.derivatioNOf.1, d.derivatioNOf.2.of_ss h⟩

noncomputable def cut' (d₁ : T ⊢ᵈᵉʳ insert p Γ) (d₂ : T ⊢ᵈᵉʳ insert (∼p) Δ) : T ⊢ᵈᵉʳ Γ ∪ Δ :=
  cut (p := p) (d₁.wk (by intro x; simp; tauto)) (d₂.wk (by intro x; simp; tauto))

noncomputable def conj (ps : SemiformulaVec L 0) (ds : ∀ i, (hi : i < len ps.val) → T ⊢ᵈᵉʳ insert (ps.nth i hi) Γ) : T ⊢ᵈᵉʳ insert ps.conj Γ := by
  have : ∀ i < len ps.val, T.theory.Derivable (insert (ps.val.[i]) Γ.val) := by intro i hi; simpa using (ds i hi).toDerivable
  have : T.theory.Derivable (insert (^⋀ ps.val) Γ.val) := Theory.Derivable.conj ps.val (by simp) this
  exact Theory.Derivable.toTDerivation _ (by simpa using this)

noncomputable def disj (ps : SemiformulaVec L 0) {i} (hi : i < len ps.val)
    (d : T ⊢ᵈᵉʳ insert (ps.nth i hi) Γ) : T ⊢ᵈᵉʳ insert ps.disj Γ := by
  have : T.theory.Derivable (insert (^⋁ ps.val) Γ.val) :=
    Theory.Derivable.disj ps.val Γ.val ps.prop hi (by simpa using d.toDerivable)
  apply Theory.Derivable.toTDerivation _ (by simpa using this)

noncomputable def modusPonens (dpq : T ⊢ᵈᵉʳ insert (p ➝ q) Γ) (dp : T ⊢ᵈᵉʳ insert p Γ) : T ⊢ᵈᵉʳ insert q Γ := by
  let d : T ⊢ᵈᵉʳ insert (p ➝ q) (insert q Γ) := dpq.wk (insert_subset_insert_of_subset _ <| by simp)
  let b : T ⊢ᵈᵉʳ insert (∼(p ➝ q)) (insert q Γ) := by
    simp only [Semiformula.imp_def, Semiformula.neg_or, Semiformula.neg_neg]
    exact and (dp.wk (insert_subset_insert_of_subset _ <| by simp))
      (em q (by simp) (by simp))
  exact cut d b

def ofEq (d : T ⊢ᵈᵉʳ Γ) (h : Γ = Δ) : T ⊢ᵈᵉʳ Δ := h ▸ d

def rotate₁ (d : T ⊢ᵈᵉʳ p₀ ⫽ p₁ ⫽ Γ) : T ⊢ᵈᵉʳ p₁ ⫽ p₀ ⫽ Γ :=
  ofEq d (by ext x; simp; tauto)

def rotate₂ (d : T ⊢ᵈᵉʳ p₀ ⫽ p₁ ⫽ p₂ ⫽ Γ) : T ⊢ᵈᵉʳ p₂ ⫽ p₁ ⫽ p₀ ⫽ Γ :=
  ofEq d (by ext x; simp; tauto)

def rotate₃ (d : T ⊢ᵈᵉʳ p₀ ⫽ p₁ ⫽ p₂ ⫽ p₃ ⫽ Γ) : T ⊢ᵈᵉʳ p₃ ⫽ p₁ ⫽ p₂ ⫽ p₀ ⫽ Γ :=
  ofEq d (by ext x; simp; tauto)

noncomputable def orInv (d : T ⊢ᵈᵉʳ p ⋎ q ⫽ Γ) : T ⊢ᵈᵉʳ p ⫽ q ⫽ Γ := by
  have b : T ⊢ᵈᵉʳ p ⋎ q ⫽ p ⫽ q ⫽ Γ := wk d (by intro x; simp; tauto)
  have : T ⊢ᵈᵉʳ ∼(p ⋎ q) ⫽ p ⫽ q ⫽ Γ := by
    simp only [Semiformula.neg_or]
    apply and (em p) (em q)
  exact cut b this

noncomputable def specialize {p : Semiformula V L (0 + 1)} (b : T ⊢ᵈᵉʳ p.all ⫽ Γ) (t : Term V L) : T ⊢ᵈᵉʳ p.substs1 t ⫽ Γ := by
  apply TDerivation.cut (p := p.all)
  · exact (TDerivation.wk b <| by intro x; simp; tauto)
  · rw [Semiformula.neg_all]
    apply TDerivation.ex t
    apply TDerivation.em (p.substs1 t)

end TDerivation

namespace TProof

variable {T U : InternalTheory V L} {p q : Formula V L}

/-- Condition D2 -/
noncomputable def modusPonens (d : T ⊢ p ➝ q) (b : T ⊢ p) : T ⊢ q := TDerivation.modusPonens d b

noncomputable def byAxm {p : Formula V L} (h : p ∈' T.theory) : T ⊢ p := TDerivation.byAxm p h (by simp)

noncomputable def ofSubset (h : T ⊆ U) {p : Formula V L} : T ⊢ p → U ⊢ p := TDerivation.ofSubset h

lemma of_subset (h : T ⊆ U) {p : Formula V L} : T ⊢! p → U ⊢! p := by
  rintro ⟨b⟩; exact ⟨ofSubset h b⟩

noncomputable instance : Entailment.ModusPonens T := ⟨modusPonens⟩

noncomputable instance : Entailment.NegationEquiv T where
  negEquiv p := by
    suffices T ⊢ (p ⋎ ∼p ⋎ ⊥) ⋏ (p ⋏ ⊤ ⋎ ∼p) by
      simpa [Axioms.NegEquiv, LO.LogicalConnective.iff, Semiformula.imp_def]
    apply TDerivation.and
    · apply TDerivation.or
      apply TDerivation.rotate₁
      apply TDerivation.or
      exact TDerivation.em p
    · apply TDerivation.or
      apply TDerivation.and
      · exact TDerivation.em p
      · exact TDerivation.verum

noncomputable instance : Entailment.Minimal T where
  verum := TDerivation.toTProof <| TDerivation.verum
  imply₁ (p q) := by
    simp only [Axioms.Imply₁, Semiformula.imp_def]
    apply TDerivation.or
    apply TDerivation.rotate₁
    apply TDerivation.or
    exact TDerivation.em p
  imply₂ (p q r) := by
    simp only [Axioms.Imply₂, Semiformula.imp_def, Semiformula.neg_or, Semiformula.neg_neg]
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
    simp only [Axioms.AndElim₁, Semiformula.imp_def, Semiformula.neg_and]
    apply TDerivation.or
    apply TDerivation.or
    exact TDerivation.em p
  and₂ (p q) := by
    simp only [Axioms.AndElim₂, Semiformula.imp_def, Semiformula.neg_and]
    apply TDerivation.or
    apply TDerivation.or
    exact TDerivation.em q
  and₃ (p q) := by
    simp only [Axioms.AndInst, Semiformula.imp_def]
    apply TDerivation.or
    apply TDerivation.rotate₁
    apply TDerivation.or
    apply TDerivation.rotate₁
    apply TDerivation.and
    · exact TDerivation.em p
    · exact TDerivation.em q
  or₁ (p q) := by
    simp only [Axioms.OrInst₁, Semiformula.imp_def]
    apply TDerivation.or
    apply TDerivation.rotate₁
    apply TDerivation.or
    exact TDerivation.em p
  or₂ (p q) := by
    suffices T ⊢ ∼q ⋎ p ⋎ q by
      simpa [Axioms.OrInst₂, Semiformula.imp_def]
    apply TDerivation.or
    apply TDerivation.rotate₁
    apply TDerivation.or
    exact TDerivation.em q
  or₃ (p q r) := by
    suffices T ⊢ p ⋏ ∼r ⋎ q ⋏ ∼r ⋎ ∼p ⋏ ∼q ⋎ r by
      simpa [Axioms.OrElim, Semiformula.imp_def]
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

noncomputable instance : Entailment.Cl T where
  dne p := by simpa [Axioms.DNE, Semiformula.imp_def] using TDerivation.or (TDerivation.em p)

noncomputable def exIntro (p : Semiformula V L (0 + 1)) (t : Term V L) (b : T ⊢ p.substs1 t) : T ⊢ p.ex := TDerivation.ex t b

lemma ex_intro! (p : Semiformula V L (0 + 1)) (t : Term V L) (b : T ⊢! p.substs1 t) : T ⊢! p.ex := ⟨exIntro _ t b.get⟩

noncomputable def specialize {p : Semiformula V L (0 + 1)} (b : T ⊢ p.all) (t : Term V L) : T ⊢ p.substs1 t := TDerivation.specialize b t

lemma specialize! {p : Semiformula V L (0 + 1)} (b : T ⊢! p.all) (t : Term V L) : T ⊢! p.substs1 t := ⟨TDerivation.specialize b.get t⟩

noncomputable def conj (ps : SemiformulaVec L 0) (ds : ∀ i, (hi : i < len ps.val) → T ⊢ ps.nth i hi) : T ⊢ ps.conj := TDerivation.conj ps ds

lemma conj! (ps : SemiformulaVec L 0) (ds : ∀ i, (hi : i < len ps.val) → T ⊢! ps.nth i hi) : T ⊢! ps.conj := ⟨conj ps fun i hi ↦ (ds i hi).get⟩

noncomputable def conj'
    (ps : SemiformulaVec L 0)
    (ds : ∀ i, (hi : i < len ps.val) → T ⊢ ps.nth (len ps.val - (i + 1)) (sub_succ_lt_self hi)) :
    T ⊢ ps.conj :=
  TDerivation.conj ps <| fun i hi ↦ by
    have : T ⊢ ps.nth (len ps.val - (len ps.val - (i + 1) + 1)) _ :=
      ds (len ps.val - (i + 1)) (sub_succ_lt_self hi)
    exact this.of_eq <| by congr; exact sub_succ_lt_selfs hi

noncomputable def conjOr'
    (ps : SemiformulaVec L 0) (q)
    (ds : ∀ i, (hi : i < len ps.val) → T ⊢ ps.nth (len ps.val - (i + 1)) (sub_succ_lt_self hi) ⋎ q) :
    T ⊢ ps.conj ⋎ q :=
  TDerivation.or <| TDerivation.conj ps <| fun i hi ↦ by
    have : T ⊢ᵈᵉʳ ps.nth (len ps.val - (len ps.val - (i + 1) + 1)) _ ⫽ q ⫽ ∅ :=
      TDerivation.orInv <| ds (len ps.val - (i + 1)) (sub_succ_lt_self hi)
    exact this.of_eq <| by congr; exact sub_succ_lt_selfs hi

noncomputable def disj (ps : SemiformulaVec L 0) {i} (hi : i < len ps.val) (d : T ⊢ ps.nth i hi) : T ⊢ ps.disj :=
  TDerivation.disj ps hi d

noncomputable def shift {p : Formula V L} (d : T ⊢ p) : T ⊢ p.shift := by simpa using TDerivation.shift d

lemma shift! {p : Formula V L} (d : T ⊢! p) : T ⊢! p.shift := ⟨by simpa using TDerivation.shift d.get⟩

noncomputable def all {p : Semiformula V L (0 + 1)} (dp : T ⊢ p.free) : T ⊢ p.all := TDerivation.all (by simpa using dp)

lemma all! {p : Semiformula V L (0 + 1)} (dp : T ⊢! p.free) : T ⊢! p.all := ⟨all dp.get⟩

noncomputable def generalizeAux {C : Formula V L} {p : Semiformula V L (0 + 1)} (dp : T ⊢ C.shift ➝ p.free) : T ⊢ C ➝ p.all := by
  rw [Semiformula.imp_def] at dp ⊢
  apply TDerivation.or
  apply TDerivation.rotate₁
  apply TDerivation.all
  exact TDerivation.wk (TDerivation.orInv dp) (by intro x; simp; tauto)

lemma conj_shift (Γ : List (Formula V L)) : (⋀Γ).shift = ⋀(Γ.map .shift) := by
    induction Γ using List.induction_with_singleton
    case hnil => simp
    case hsingle => simp [List.conj₂]
    case hcons p ps hps ih =>
      simp [hps, ih]

noncomputable def generalize {Γ} {p : Semiformula V L (0 + 1)} (d : Γ.map .shift ⊢[T] p.free) : Γ ⊢[T] p.all := by
  apply Entailment.FiniteContext.ofDef
  apply generalizeAux
  simpa [conj_shift] using Entailment.FiniteContext.toDef d

lemma generalize! {Γ} {p : Semiformula V L (0 + 1)} (d : Γ.map .shift ⊢[T]! p.free) : Γ ⊢[T]! p.all := ⟨generalize d.get⟩

noncomputable def specializeWithCtxAux {C : Formula V L} {p : Semiformula V L (0 + 1)} (d : T ⊢ C ➝ p.all) (t : Term V L) : T ⊢ C ➝ p.substs1 t := by
  rw [Semiformula.imp_def] at d ⊢
  apply TDerivation.or
  apply TDerivation.rotate₁
  apply TDerivation.specialize
  exact TDerivation.wk (TDerivation.orInv d) (by intro x; simp; tauto)

noncomputable def specializeWithCtx {Γ} {p : Semiformula V L (0 + 1)} (d : Γ ⊢[T] p.all) (t) : Γ ⊢[T] p.substs1 t := specializeWithCtxAux d t

lemma specialize_with_ctx! {Γ} {p : Semiformula V L (0 + 1)} (d : Γ ⊢[T]! p.all) (t) : Γ ⊢[T]! p.substs1 t := ⟨specializeWithCtx d.get t⟩

noncomputable def ex {p : Semiformula V L (0 + 1)} (t) (dp : T ⊢ p.substs1 t) : T ⊢ p.ex := TDerivation.ex t (by simpa using dp)

lemma ex! {p : Semiformula V L (0 + 1)} (t) (dp : T ⊢! p.substs1 t) : T ⊢! p.ex := ⟨ex t dp.get⟩

end TProof

end typed_derivation
