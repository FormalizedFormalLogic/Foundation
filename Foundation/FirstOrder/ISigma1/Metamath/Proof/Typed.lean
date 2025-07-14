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

section typed_theory

abbrev tmem (φ : Formula V L) (T : Theory L) [T.Δ₁Definable] : Prop := φ.val ∈ T.Δ₁Class

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

noncomputable instance : Singleton (Formula V L) (Sequent V L) := ⟨fun φ ↦ ⟨{φ.val}, by simp⟩⟩

noncomputable instance : Insert (Formula V L) (Sequent V L) := ⟨fun φ Γ ↦ ⟨insert φ.val Γ.val, by simp⟩⟩

noncomputable instance : Union (Sequent V L) := ⟨fun Γ Δ ↦ ⟨Γ.val ∪ Δ.val, by simp⟩⟩

instance : Membership (Formula V L) (Sequent V L) := ⟨fun Γ φ ↦ (φ.val ∈ Γ.val)⟩

instance : HasSubset (Sequent V L) := ⟨(·.val ⊆ ·.val)⟩

scoped infixr:50 " ⫽ " => Insert.insert

namespace Sequent

variable {Γ Δ : Sequent V L} {φ ψ : Formula V L}

lemma mem_iff : φ ∈ Γ ↔ φ.val ∈ Γ.val := iff_of_eq rfl

lemma subset_iff : Γ ⊆ Δ ↔ Γ.val ⊆ Δ.val := iff_of_eq rfl

@[simp] lemma val_empty : (∅ : (Sequent V L)).val = ∅ := rfl

@[simp] lemma val_singleton (φ : Formula V L) : ({φ} : (Sequent V L)).val = {φ.val} := rfl

@[simp] lemma val_insert (φ : Formula V L) (Γ : (Sequent V L)) : (insert φ Γ).val = insert φ.val Γ.val := rfl

@[simp] lemma val_union (Γ Δ : (Sequent V L)) : (Γ ∪ Δ).val = Γ.val ∪ Δ.val := rfl

@[simp] lemma not_mem_empty (φ : Formula V L) : φ ∉ (∅ : (Sequent V L)) := by simp [mem_iff]

@[simp] lemma mem_singleton_iff : φ ∈ ({ψ} : (Sequent V L)) ↔ φ = ψ := by simp [mem_iff, Semiformula.val_inj]

@[simp] lemma mem_insert_iff : φ ∈ insert ψ Γ ↔ φ = ψ ∨ φ ∈ Γ := by simp [mem_iff, Semiformula.val_inj]

@[simp] lemma mem_union_iff : φ ∈ Γ ∪ Δ ↔ φ ∈ Γ ∨ φ ∈ Δ := by simp [mem_iff]

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

@[simp] lemma shift_insert : (insert φ Γ).shift = insert φ.shift Γ.shift := ext' <| by simp [shift]

lemma insert_eq_of_mem (h : φ ∈ Γ) : insert φ Γ = Γ := by
  ext; simp only [mem_insert_iff, or_iff_right_iff_imp]; rintro rfl; simpa

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

omit [ORingStruc V] [V ⊧ₘ* 𝐈𝚺₁] in
@[simp] lemma internalize_theory (T : Theory L) [T.Δ₁Definable] : (T.internalize V).theory = T := rfl

structure TDerivation (T : InternalTheory V L) (Γ : Sequent V L) where
  derivation : V
  derivationOf : T.theory.DerivationOf derivation Γ.val

attribute [simp] TDerivation.derivationOf

scoped infix:45 " ⊢ᵈᵉʳ " => TDerivation

def TProof (T : InternalTheory V L) (φ : Formula V L) := T ⊢ᵈᵉʳ insert φ ∅

instance : Entailment (Formula V L) (InternalTheory V L) := ⟨TProof⟩

instance : HasSubset (InternalTheory V L) := ⟨fun T U ↦ T.theory.Δ₁Class (V := V) ⊆ U.theory.Δ₁Class⟩

variable {T U : InternalTheory V L}

noncomputable def _root_.LO.FirstOrder.Theory.Derivable.toTDerivation (Γ : Sequent V L) (h : T.theory.Derivable Γ.val) : T ⊢ᵈᵉʳ Γ := by
  choose a ha using h; choose d hd using ha.2
  exact ⟨a, ha.1, d, hd⟩

lemma TDerivation.toDerivable {Γ : (Sequent V L)} (d : T ⊢ᵈᵉʳ Γ) : T.theory.Derivable Γ.val :=
  ⟨d.derivation, d.derivationOf⟩

lemma TProvable.iff_provable {σ : Formula V L} :
    T ⊢! σ ↔ T.theory.Provable σ.val := by
  constructor
  · intro b
    simpa [←singleton_eq_insert] using TDerivation.toDerivable b.get
  · intro h
    exact ⟨Theory.Derivable.toTDerivation _ <| by simpa [←singleton_eq_insert] using h⟩

alias ⟨toProvable, _root_.LO.FirstOrder.Theory.Provable.toTProvable⟩ := TProvable.iff_provable

def proof_to_tDerivation {σ : Formula V L} : T ⊢ σ → T ⊢ᵈᵉʳ insert σ ∅ := fun x ↦ x

lemma internalize_TProvable_iff_provable {T : Theory L} [T.Δ₁Definable] {σ : Formula V L} :
    T.internalize V ⊢! σ ↔ T.Provable σ.val := TProvable.iff_provable

def TDerivation.toTProof {φ} (d : T ⊢ᵈᵉʳ insert φ ∅) : T ⊢ φ := d

def TDerivation.of_eq (d : T ⊢ᵈᵉʳ Γ) (e : Γ = Δ) : T ⊢ᵈᵉʳ Δ := by rcases e; exact d

def TProof.toTDerivation {φ} (d : T ⊢ φ) : T ⊢ᵈᵉʳ insert φ ∅ := d

namespace TDerivation

variable {Γ Δ : (Sequent V L)} {φ ψ p₀ p₁ p₂ p₃ p₄ : Formula V L}

noncomputable def byAxm (φ) (h : φ ∈' T.theory) (hΓ : φ ∈ Γ) : T ⊢ᵈᵉʳ Γ :=
  Theory.Derivable.toTDerivation _
    <| Theory.Derivable.by_axm (by simp) _ hΓ h

noncomputable def em (φ) (h : φ ∈ Γ := by simp) (hn : ∼φ ∈ Γ := by simp) : T ⊢ᵈᵉʳ Γ :=
  Theory.Derivable.toTDerivation _
    <| Theory.Derivable.em (by simp) φ.val (Sequent.mem_iff.mp h) (by simpa using Sequent.mem_iff.mp hn)

noncomputable def verum (h : ⊤ ∈ Γ := by simp) : T ⊢ᵈᵉʳ Γ :=
  Theory.Derivable.toTDerivation _
    <| Theory.Derivable.verum (by simp) (by simpa using Sequent.mem_iff.mp h)

noncomputable def and (dp : T ⊢ᵈᵉʳ insert φ Γ) (dq : T ⊢ᵈᵉʳ insert ψ Γ) : T ⊢ᵈᵉʳ insert (φ ⋏ ψ) Γ :=
  Theory.Derivable.toTDerivation _
    <| by simpa using Theory.Derivable.and (by simpa using dp.toDerivable) (by simpa using dq.toDerivable)

noncomputable def or (dpq : T ⊢ᵈᵉʳ insert φ (insert ψ Γ)) : T ⊢ᵈᵉʳ insert (φ ⋎ ψ) Γ :=
  Theory.Derivable.toTDerivation _ <| by simpa using Theory.Derivable.or (by simpa using dpq.toDerivable)

noncomputable def all {φ : Semiformula V L 1} (dp : T ⊢ᵈᵉʳ insert φ.free Γ.shift) : T ⊢ᵈᵉʳ insert (∀' φ) Γ :=
  Theory.Derivable.toTDerivation _ <| by
    simpa using Theory.Derivable.all (by simp) (by simpa using dp.toDerivable)

noncomputable def ex {φ : Semiformula V L 1} (t : Term V L) (dp : T ⊢ᵈᵉʳ insert (φ.substs ![t]) Γ) : T ⊢ᵈᵉʳ insert (∃' φ) Γ :=
  Theory.Derivable.toTDerivation _ <| by
    simpa using Theory.Derivable.ex (by simp) t.isSemiterm (by simpa using dp.toDerivable)

noncomputable def wk (d : T ⊢ᵈᵉʳ Δ) (h : Δ ⊆ Γ) : T ⊢ᵈᵉʳ Γ :=
  Theory.Derivable.toTDerivation _ <| by
    simpa using Theory.Derivable.wk (by simp) (Sequent.subset_iff.mp h) (by simpa using d.toDerivable)

noncomputable def shift (d : T ⊢ᵈᵉʳ Γ) : T ⊢ᵈᵉʳ Γ.shift :=
  Theory.Derivable.toTDerivation _ <| by
    simpa using Theory.Derivable.shift (by simpa using d.toDerivable)

noncomputable def cut (d₁ : T ⊢ᵈᵉʳ insert φ Γ) (d₂ : T ⊢ᵈᵉʳ insert (∼φ) Γ) : T ⊢ᵈᵉʳ Γ :=
  Theory.Derivable.toTDerivation _ <| by
    simpa using Theory.Derivable.cut φ.val (by simpa using d₁.toDerivable) (by simpa using d₂.toDerivable)

def ofSubset (h : T ⊆ U) (d : T ⊢ᵈᵉʳ Γ) : U ⊢ᵈᵉʳ Γ where
  derivation := d.derivation
  derivationOf := ⟨d.derivationOf.1, d.derivationOf.2.of_ss h⟩

noncomputable def cut' (d₁ : T ⊢ᵈᵉʳ insert φ Γ) (d₂ : T ⊢ᵈᵉʳ insert (∼φ) Δ) : T ⊢ᵈᵉʳ Γ ∪ Δ :=
  cut (φ := φ) (d₁.wk (by intro x; simp; tauto)) (d₂.wk (by intro x; simp; tauto))

noncomputable def modusPonens (dpq : T ⊢ᵈᵉʳ insert (φ ➝ ψ) Γ) (dp : T ⊢ᵈᵉʳ insert φ Γ) : T ⊢ᵈᵉʳ insert ψ Γ := by
  let d : T ⊢ᵈᵉʳ insert (φ ➝ ψ) (insert ψ Γ) := dpq.wk (insert_subset_insert_of_subset _ <| by simp)
  let b : T ⊢ᵈᵉʳ insert (∼(φ ➝ ψ)) (insert ψ Γ) := by
    simp only [Semiformula.imp_def, DeMorgan.or, DeMorgan.neg]
    exact and (dp.wk (insert_subset_insert_of_subset _ <| by simp))
      (em ψ (by simp) (by simp))
  exact cut d b

def ofEq (d : T ⊢ᵈᵉʳ Γ) (h : Γ = Δ) : T ⊢ᵈᵉʳ Δ := h ▸ d

def rotate₁ (d : T ⊢ᵈᵉʳ p₀ ⫽ p₁ ⫽ Γ) : T ⊢ᵈᵉʳ p₁ ⫽ p₀ ⫽ Γ :=
  ofEq d (by ext x; simp; tauto)

def rotate₂ (d : T ⊢ᵈᵉʳ p₀ ⫽ p₁ ⫽ p₂ ⫽ Γ) : T ⊢ᵈᵉʳ p₂ ⫽ p₁ ⫽ p₀ ⫽ Γ :=
  ofEq d (by ext x; simp; tauto)

def rotate₃ (d : T ⊢ᵈᵉʳ p₀ ⫽ p₁ ⫽ p₂ ⫽ p₃ ⫽ Γ) : T ⊢ᵈᵉʳ p₃ ⫽ p₁ ⫽ p₂ ⫽ p₀ ⫽ Γ :=
  ofEq d (by ext x; simp; tauto)

noncomputable def orInv (d : T ⊢ᵈᵉʳ φ ⋎ ψ ⫽ Γ) : T ⊢ᵈᵉʳ φ ⫽ ψ ⫽ Γ := by
  have b : T ⊢ᵈᵉʳ φ ⋎ ψ ⫽ φ ⫽ ψ ⫽ Γ := wk d (by intro x; simp; tauto)
  have : T ⊢ᵈᵉʳ ∼(φ ⋎ ψ) ⫽ φ ⫽ ψ ⫽ Γ := by
    simp only [DeMorgan.or]
    apply and (em φ) (em ψ)
  exact cut b this

noncomputable def specialize {φ : Semiformula V L 1} (b : T ⊢ᵈᵉʳ (∀' φ) ⫽ Γ) (t : Term V L) : T ⊢ᵈᵉʳ φ.substs ![t] ⫽ Γ := by
  apply TDerivation.cut (φ := (∀' φ))
  · exact (TDerivation.wk b <| by intro x; simp; tauto)
  · rw [Semiformula.neg_all]
    apply TDerivation.ex t
    apply TDerivation.em (φ.substs ![t])

end TDerivation

namespace TProof

variable {T U : InternalTheory V L} {φ ψ : Formula V L}

/-- Condition D2 -/
noncomputable def modusPonens (d : T ⊢ φ ➝ ψ) (b : T ⊢ φ) : T ⊢ ψ := TDerivation.modusPonens d b

noncomputable def byAxm {φ : Formula V L} (h : φ ∈' T.theory) : T ⊢ φ := TDerivation.byAxm φ h (by simp)

noncomputable def ofSubset (h : T ⊆ U) {φ : Formula V L} : T ⊢ φ → U ⊢ φ := TDerivation.ofSubset h

lemma of_subset (h : T ⊆ U) {φ : Formula V L} : T ⊢! φ → U ⊢! φ := by
  rintro ⟨b⟩; exact ⟨ofSubset h b⟩

noncomputable instance : Entailment.ModusPonens T := ⟨modusPonens⟩

noncomputable instance : Entailment.NegationEquiv T where
  negEquiv φ := by
    suffices T ⊢ (φ ⋎ ∼φ ⋎ ⊥) ⋏ (φ ⋏ ⊤ ⋎ ∼φ) by
      simpa [Axioms.NegEquiv, LO.LogicalConnective.iff, Semiformula.imp_def]
    apply TDerivation.and
    · apply TDerivation.or
      apply TDerivation.rotate₁
      apply TDerivation.or
      exact TDerivation.em φ
    · apply TDerivation.or
      apply TDerivation.and
      · exact TDerivation.em φ
      · exact TDerivation.verum

noncomputable instance : Entailment.Minimal T where
  verum := TDerivation.toTProof <| TDerivation.verum
  imply₁ (φ ψ) := by
    simp only [Axioms.Imply₁, Semiformula.imp_def]
    apply TDerivation.or
    apply TDerivation.rotate₁
    apply TDerivation.or
    exact TDerivation.em φ
  imply₂ (φ ψ r) := by
    simp only [Axioms.Imply₂, Semiformula.imp_def, DeMorgan.or, DeMorgan.neg]
    apply TDerivation.or
    apply TDerivation.rotate₁
    apply TDerivation.or
    apply TDerivation.rotate₁
    apply TDerivation.or
    apply TDerivation.rotate₂
    apply TDerivation.and
    · exact TDerivation.em φ
    · apply TDerivation.rotate₃
      apply TDerivation.and
      · exact TDerivation.em φ
      · apply TDerivation.and
        · exact TDerivation.em ψ
        · exact TDerivation.em r
  and₁ (φ ψ) := by
    simp only [Axioms.AndElim₁, Semiformula.imp_def, DeMorgan.and]
    apply TDerivation.or
    apply TDerivation.or
    exact TDerivation.em φ
  and₂ (φ ψ) := by
    simp only [Axioms.AndElim₂, Semiformula.imp_def, DeMorgan.and]
    apply TDerivation.or
    apply TDerivation.or
    exact TDerivation.em ψ
  and₃ (φ ψ) := by
    simp only [Axioms.AndInst, Semiformula.imp_def]
    apply TDerivation.or
    apply TDerivation.rotate₁
    apply TDerivation.or
    apply TDerivation.rotate₁
    apply TDerivation.and
    · exact TDerivation.em φ
    · exact TDerivation.em ψ
  or₁ (φ ψ) := by
    simp only [Axioms.OrInst₁, Semiformula.imp_def]
    apply TDerivation.or
    apply TDerivation.rotate₁
    apply TDerivation.or
    exact TDerivation.em φ
  or₂ (φ ψ) := by
    suffices T ⊢ ∼ψ ⋎ φ ⋎ ψ by
      simpa [Axioms.OrInst₂, Semiformula.imp_def]
    apply TDerivation.or
    apply TDerivation.rotate₁
    apply TDerivation.or
    exact TDerivation.em ψ
  or₃ (φ ψ r) := by
    suffices T ⊢ φ ⋏ ∼r ⋎ ψ ⋏ ∼r ⋎ ∼φ ⋏ ∼ψ ⋎ r by
      simpa [Axioms.OrElim, Semiformula.imp_def]
    apply TDerivation.or
    apply TDerivation.rotate₁
    apply TDerivation.or
    apply TDerivation.rotate₁
    apply TDerivation.or
    apply TDerivation.and
    · apply TDerivation.rotate₃
      apply TDerivation.and
      · exact TDerivation.em φ
      · exact TDerivation.em r
    · apply TDerivation.rotate₂
      apply TDerivation.and
      · exact TDerivation.em ψ
      · exact TDerivation.em r

noncomputable instance : Entailment.Cl T where
  dne φ := by simpa [Axioms.DNE, Semiformula.imp_def] using TDerivation.or (TDerivation.em φ)

noncomputable def exIntro (φ : Semiformula V L 1) (t : Term V L) (b : T ⊢ φ.substs ![t]) : T ⊢ (∃' φ) := TDerivation.ex t b

lemma ex_intro! (φ : Semiformula V L 1) (t : Term V L) (b : T ⊢! φ.substs ![t]) : T ⊢! (∃' φ) := ⟨exIntro _ t b.get⟩

noncomputable def specialize {φ : Semiformula V L 1} (b : T ⊢ ∀' φ) (t : Term V L) : T ⊢ φ.substs ![t] := TDerivation.specialize b t

noncomputable def specialize₂ {φ : Semiformula V L 2} (b : T ⊢ ∀' ∀' φ) (t u : Term V L) :
    T ⊢ φ.substs ![t, u] := by
  have : T ⊢ ∀' Semiformula.substs (SemitermVec.q ![u]) φ := by simpa using specialize b u
  simpa [SemitermVec.q, Semiformula.substs_substs] using specialize this t

noncomputable def specialize₃ {φ : Semiformula V L 3} (b : T ⊢ ∀' ∀' ∀' φ) (t₁ t₂ t₃ : Term V L) :
    T ⊢ φ.substs ![t₁, t₂, t₃] := by
  have := by simpa using specialize b t₃
  have := by simpa using specialize this t₂
  have := by simpa using specialize this t₁
  simp [Semiformula.substs_substs] at this
  simpa [SemitermVec.q] using this

noncomputable def specialize₄ {φ : Semiformula V L 4} (b : T ⊢ ∀' ∀' ∀' ∀' φ) (t₁ t₂ t₃ t₄ : Term V L) :
    T ⊢ φ.substs ![t₁, t₂, t₃, t₄] := by
  have := by simpa using specialize b t₄
  have := by simpa using specialize this t₃
  have := by simpa using specialize this t₂
  have := by simpa using specialize this t₁
  simp [Semiformula.substs_substs, Semiterm.substs_substs] at this
  simpa [SemitermVec.q, Semiterm.bShift_substs_succ] using this

lemma specialize! {φ : Semiformula V L 1} (b : T ⊢! (∀' φ)) (t : Term V L) : T ⊢! φ.substs ![t] := ⟨TDerivation.specialize b.get t⟩

lemma specialize₂! {φ : Semiformula V L 2} (b : T ⊢! ∀' ∀' φ) (t u : Term V L) :
    T ⊢! φ.substs ![t, u] := ⟨specialize₂ b.get t u⟩

lemma specialize₄! {φ : Semiformula V L 4} (b : T ⊢! ∀' ∀' ∀' ∀' φ) (t₁ t₂ t₃ t₄ : Term V L) :
    T ⊢! φ.substs ![t₁, t₂, t₃, t₄] := ⟨specialize₄ b.get _ _ _ _⟩

noncomputable def shift {φ : Formula V L} (d : T ⊢ φ) : T ⊢ φ.shift := by simpa using TDerivation.shift d

lemma shift! {φ : Formula V L} (d : T ⊢! φ) : T ⊢! φ.shift := ⟨by simpa using TDerivation.shift d.get⟩

noncomputable def all {φ : Semiformula V L 1} (dp : T ⊢ φ.free) : T ⊢ ∀' φ := TDerivation.all (by simpa using dp)

noncomputable def all₂ {φ : Semiformula V L 2}
    (d : T ⊢ φ.shift.shift.substs ![Semiterm.fvar 0, Semiterm.fvar 1]) : T ⊢ ∀' ∀' φ := by
  apply all
  suffices
      T ⊢ ∀' Semiformula.substs ![Semiterm.bvar 0, Semiterm.fvar 0] φ.shift by
    simpa [Semiformula.free, SemitermVec.q, Semiformula.shift_substs, Semiformula.substs_substs]
  apply all
  simpa [Semiformula.free, SemitermVec.q, Semiformula.shift_substs, Semiformula.substs_substs]

lemma all₂! {φ : Semiformula V L 2}
    (d : T ⊢! φ.shift.shift.substs ![Semiterm.fvar 0, Semiterm.fvar 1]) : T ⊢! ∀' ∀' φ :=
  ⟨all₂ d.get⟩

lemma all! {φ : Semiformula V L 1} (dp : T ⊢! φ.free) : T ⊢! ∀' φ := ⟨all dp.get⟩

noncomputable def specialize_shift {φ : Semiformula V L 1} (b : T ⊢ ∀' φ) (t : Term V L) :
    T ⊢ φ.shift.substs ![t] := by
  have : T ⊢ ∀' φ.shift := by simpa using shift b
  exact specialize this t

noncomputable def specialize₂_shift {φ : Semiformula V L 2} (b : T ⊢ ∀' ∀' φ) (t u : Term V L) :
    T ⊢ φ.shift.shift.substs ![t, u] := by
  have : T ⊢ ∀' ∀' φ.shift.shift := by simpa using shift (shift b)
  exact specialize₂ this t u

lemma specialize₂_shift! {φ : Semiformula V L 2} (b : T ⊢! ∀' ∀' φ) (t u : Term V L) :
    T ⊢! φ.shift.shift.substs ![t, u] := ⟨specialize₂_shift b.get _ _⟩

noncomputable def generalizeAux {C : Formula V L} {φ : Semiformula V L 1} (dp : T ⊢ C.shift ➝ φ.free) : T ⊢ C ➝ ∀' φ := by
  rw [Semiformula.imp_def] at dp ⊢
  apply TDerivation.or
  apply TDerivation.rotate₁
  apply TDerivation.all
  exact TDerivation.wk (TDerivation.orInv dp) (by intro x; simp; tauto)

lemma conj_shift (Γ : List (Formula V L)) : (⋀Γ).shift = ⋀(Γ.map .shift) := by
    induction Γ using List.induction_with_singleton
    case hnil => simp
    case hsingle => simp [List.conj₂]
    case hcons φ ps hps ih =>
      simp [hps, ih]

noncomputable def generalize {Γ} {φ : Semiformula V L 1} (d : Γ.map .shift ⊢[T] φ.free) : Γ ⊢[T] ∀' φ := by
  apply Entailment.FiniteContext.ofDef
  apply generalizeAux
  simpa [conj_shift] using Entailment.FiniteContext.toDef d

lemma generalize! {Γ} {φ : Semiformula V L 1} (d : Γ.map .shift ⊢[T]! φ.free) : Γ ⊢[T]! ∀' φ := ⟨generalize d.get⟩

noncomputable def specializeWithCtxAux {C : Formula V L} {φ : Semiformula V L 1} (d : T ⊢ C ➝ ∀' φ) (t : Term V L) : T ⊢ C ➝ φ.substs ![t] := by
  rw [Semiformula.imp_def] at d ⊢
  apply TDerivation.or
  apply TDerivation.rotate₁
  apply TDerivation.specialize
  exact TDerivation.wk (TDerivation.orInv d) (by intro x; simp; tauto)

noncomputable def specializeWithCtx {Γ} {φ : Semiformula V L 1} (d : Γ ⊢[T] (∀' φ)) (t) : Γ ⊢[T] φ.substs ![t] := specializeWithCtxAux d t

lemma specialize_with_ctx! {Γ} {φ : Semiformula V L 1} (d : Γ ⊢[T]! (∀' φ)) (t) : Γ ⊢[T]! φ.substs ![t] := ⟨specializeWithCtx d.get t⟩

open Entailment.FiniteContext Classical

noncomputable def allImpAll {Γ} {φ ψ : Semiformula V L 1} (d : Γ.map .shift ⊢[T] φ.free ➝ ψ.free) :
    Γ ⊢[T] ∀' φ ➝ ∀' ψ := by
  apply deduct
  apply generalize
  suffices ((∀' φ.shift) :: Γ.map Semiformula.shift) ⊢[T] ψ.free by simpa
  have hφ : ((∀' φ.shift) :: Γ.map Semiformula.shift) ⊢[T] φ.free := by
    apply specializeWithCtx
    apply byAxm₀
  have h : ((∀' φ.shift) :: Γ.map Semiformula.shift) ⊢[T] φ.free ➝ ψ.free :=
    Entailment.FiniteContext.weakening (by simp) d
  exact h ⨀ hφ

noncomputable def all_imp_all! {Γ} {φ ψ : Semiformula V L 1} (d : Γ.map .shift ⊢[T]! φ.free ➝ ψ.free) :
    Γ ⊢[T]! ∀' φ ➝ ∀' ψ := ⟨allImpAll d.get⟩

noncomputable def exImpEx {Γ} {φ ψ : Semiformula V L 1} (d : Γ.map .shift ⊢[T] φ.free ➝ ψ.free) : Γ ⊢[T] ∃' φ ➝ ∃' ψ := by
  apply Entailment.C_of_CNN
  suffices Γ ⊢[T] ∀' ∼ψ ➝ ∀' ∼φ by simpa
  apply allImpAll
  apply Entailment.C_of_CNN
  simpa [Semiformula.free] using d

noncomputable def ex_imp_ex! {Γ} {φ ψ : Semiformula V L 1} (d : Γ.map .shift ⊢[T]! φ.free ➝ ψ.free) :
    Γ ⊢[T]! ∃' φ ➝ ∃' ψ := ⟨exImpEx d.get⟩

noncomputable def ex {φ : Semiformula V L 1} (t) (dp : T ⊢ φ.substs ![t]) : T ⊢ ∃' φ := TDerivation.ex t (by simpa using dp)

lemma ex! {φ : Semiformula V L 1} (t) (dp : T ⊢! φ.substs ![t]) : T ⊢! ∃' φ := ⟨ex t dp.get⟩

variable (A : InternalTheory V ℒₒᵣ)

open InternalArithmetic

open Entailment Theory.Derivation

lemma substItrDisj_right {i z : V}
    (w : TermVec V ℒₒᵣ m) (φ : Semiformula V ℒₒᵣ (m + 1)) (hi : i < z) :
    A ⊢! φ.substs (↑i :> w) ➝ φ.substItrDisj w z := Theory.Provable.toTProvable <| Theory.Derivable.toProvable <| by
  apply Theory.Derivable.or
  apply Theory.Derivable.exchange
  apply Theory.Derivable.disj (L := ℒₒᵣ) (i := z - (i + 1)) _
  · intro i hi
    have hi : i < z := by simpa using hi
    rw [substItr_nth _ _ _ hi]
    exact φ.isSemiformula.substs (w.isSemitermVec.cons (by simp))
  · simpa using pos_of_gt hi
  · have : z - (i + 1) < z := by simpa using pos_of_gt hi
    rw [substItr_nth _ _ _ this]
    have : z - (z - (i + 1) + 1) = i := sub_succ_lt_selfs hi
    simp only [this, Nat.succ_eq_add_one, Semiformula.val_substs, SemitermVec.val_succ,
      Matrix.head_cons, val_numeral, Matrix.tail_cons]
    apply Theory.Derivable.em (L := ℒₒᵣ) (p := substs ℒₒᵣ (numeral i ∷ SemitermVec.val w) φ.val)
    · simpa using φ.isSemiformula_succ.substs (w.isSemitermVec.cons (numeral_semiterm 0 i))
    · simp
    · simp

lemma substItrDisj_right_intro {ψ} {i z : V} {w : TermVec V ℒₒᵣ m} {φ : Semiformula V ℒₒᵣ (m + 1)}
    (hi : i < z) (h : A ⊢! ψ ➝ φ.substs (↑i :> w)) :
     A ⊢! ψ ➝ φ.substItrDisj w z :=
  Entailment.C!_trans h (substItrDisj_right A w φ hi)

lemma substItrConj_right_intro {ψ} {w : TermVec V ℒₒᵣ m} {φ : Semiformula V ℒₒᵣ (m + 1)} {z : V}
    (h : ∀ i < z, A ⊢! ψ ➝ φ.substs (↑i :> w)) :
    A ⊢! ψ ➝ φ.substItrConj w z := Theory.Provable.toTProvable <| Theory.Derivable.toProvable <| by
  apply Theory.Derivable.or
  apply Theory.Derivable.exchange
  apply Theory.Derivable.conj
  · simp
  · intro i hi
    have hi : i < z := by simpa using hi
    rw [substItr_nth _ _ _ hi]
    apply Theory.Derivable.exchange
    suffices A ⊢ᵈᵉʳ (∼ψ ⫽ φ.substs (↑(z - (i + 1)) :> w) ⫽ ∅) by
      simpa using this.toDerivable
    have : A ⊢! ∼ψ ⋎ Semiformula.substs (typedNumeral (z - (i + 1)) :> w) φ := h (z - (i + 1)) (by simp [pos_of_gt hi])
    exact TDerivation.orInv (proof_to_tDerivation this.get)

open Classical in
lemma substItrDisj_left_intro {ψ} {w : TermVec V ℒₒᵣ m} {φ : Semiformula V ℒₒᵣ (m + 1)} {z : V}
    (h : ∀ i < z, A ⊢! φ.substs (↑i :> w) ➝ ψ) :
    A ⊢! φ.substItrDisj w z ➝ ψ := by
  apply C!_of_CNN!
  simp only [Semiformula.substItrDisj_neg]
  apply substItrConj_right_intro
  intro i hi
  apply C!_of_CNN!
  simpa using h i hi

end TProof

end typed_derivation
