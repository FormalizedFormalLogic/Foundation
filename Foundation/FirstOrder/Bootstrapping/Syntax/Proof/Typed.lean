module

public import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Basic

@[expose] public section
/-!
# Typed internal Tait-calculus
-/

namespace LO

open FirstOrder Arithmetic

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

variable {L : Language} [L.Encodable] [L.LORDefinable]

namespace FirstOrder.Arithmetic.Bootstrapping

section typed_theory

abbrev tmem (φ : Formula V L) (T : Theory L) [T.Δ₁] : Prop := φ.val ∈ T.Δ₁Class

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

lemma insert_empty_eq_singleton : insert φ (∅ : Sequent V L) = {φ} := by ext; simp

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
  Δ₁ : theory.Δ₁

instance : CoeOut (InternalTheory V L) (Theory L) := ⟨InternalTheory.theory⟩

instance (T : InternalTheory V L) : T.theory.Δ₁ := T.Δ₁

variable (V)

def _root_.LO.FirstOrder.Theory.internalize (T : Theory L) [T.Δ₁] : InternalTheory V L := ⟨T, inferInstance⟩

variable {V}

omit [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁] in
@[simp] lemma internalize_theory (T : Theory L) [T.Δ₁] : (T.internalize V).theory = T := rfl

structure TDerivation (T : InternalTheory V L) (Γ : Sequent V L) where
  val : V
  derivationOf : T.theory.DerivationOf val Γ.val

attribute [simp] TDerivation.derivationOf

scoped infix:45 " ⊢!ᵈᵉʳ " => TDerivation

def TProof (T : InternalTheory V L) (φ : Formula V L) := T ⊢!ᵈᵉʳ insert φ ∅

instance : Entailment (InternalTheory V L) (Formula V L) := ⟨TProof⟩

instance : HasSubset (InternalTheory V L) := ⟨fun T U ↦ T.theory.Δ₁Class (V := V) ⊆ U.theory.Δ₁Class⟩

variable {T U : InternalTheory V L}

noncomputable def _root_.LO.FirstOrder.Theory.Derivable.toTDerivation (Γ : Sequent V L) (h : T.theory.Derivable Γ.val) : T ⊢!ᵈᵉʳ Γ := by
  choose a ha using h; choose d hd using ha.2
  exact ⟨a, ha.1, d, hd⟩

lemma TDerivation.toDerivable {Γ : (Sequent V L)} (d : T ⊢!ᵈᵉʳ Γ) : T.theory.Derivable Γ.val :=
  ⟨d.val, d.derivationOf⟩

lemma TProvable.iff_provable {σ : Formula V L} :
    T ⊢ σ ↔ T.theory.Provable σ.val := by
  constructor
  · intro b
    simpa [←singleton_eq_insert] using TDerivation.toDerivable b.get
  · intro h
    exact ⟨Theory.Derivable.toTDerivation _ <| by simpa [←singleton_eq_insert] using h⟩

alias ⟨toProvable, _root_.LO.FirstOrder.Theory.Provable.toTProvable⟩ := TProvable.iff_provable

def proof_to_tDerivation {σ : Formula V L} : T ⊢! σ → T ⊢!ᵈᵉʳ insert σ ∅ := fun x ↦ x

lemma tprovable_iff_provable {T : Theory L} [T.Δ₁] {σ : Formula V L} :
    T.internalize V ⊢ σ ↔ T.Provable σ.val := TProvable.iff_provable

lemma tprovable_tquote_iff_provable_quote {T : Theory L} [T.Δ₁] {φ : Proposition L} :
    T.internalize V ⊢ ⌜φ⌝ ↔ T.Provable (⌜φ⌝ : V) := TProvable.iff_provable

lemma tprovable_tquote_iff_provable_quote_sentence {T : Theory L} [T.Δ₁] {σ : Sentence L} :
    T.internalize V ⊢ ⌜σ⌝ ↔ T.Provable (⌜σ⌝ : V) := TProvable.iff_provable

def TDerivation.toTProof {φ} (d : T ⊢!ᵈᵉʳ insert φ ∅) : T ⊢! φ := d

def TDerivation.of_eq (d : T ⊢!ᵈᵉʳ Γ) (e : Γ = Δ) : T ⊢!ᵈᵉʳ Δ := by rcases e; exact d

def TProof.toTDerivation {φ} (d : T ⊢! φ) : T ⊢!ᵈᵉʳ insert φ ∅ := d

namespace TDerivation

variable {Γ Δ : (Sequent V L)} {φ ψ p₀ p₁ p₂ p₃ p₄ : Formula V L}

protected noncomputable def cast {Γ Δ : Bootstrapping.Sequent V L} (e : Γ = Δ) :
    T ⊢!ᵈᵉʳ Γ → T ⊢!ᵈᵉʳ Δ := fun d ↦ by rcases e; exact d

@[simp] lemma cast_val {Γ Δ : Bootstrapping.Sequent V L} (e : Γ = Δ) (d : T ⊢!ᵈᵉʳ Γ) :
    (TDerivation.cast e d).val = d.val := by rcases e; simp [TDerivation.cast]

noncomputable def byAxm (φ) (h : φ ∈' T.theory) (hΓ : φ ∈ Γ) : T ⊢!ᵈᵉʳ Γ :=
  ⟨Bootstrapping.axm Γ.val φ.val, by simp, Theory.Derivation.axm (by simp) (by simpa) h⟩

@[simp] lemma byAxm_val (φ) (h : φ ∈' T.theory) (hΓ : φ ∈ Γ) :
    (byAxm φ h hΓ).val = Bootstrapping.axm Γ.val φ.val := rfl

noncomputable def em (φ) (h : φ ∈ Γ := by simp) (hn : ∼φ ∈ Γ := by simp) : T ⊢!ᵈᵉʳ Γ :=
  ⟨axL Γ.val φ.val, by simp, Theory.Derivation.axL (by simp) h hn⟩

@[simp] lemma em_val (φ) (h : φ ∈ Γ) (hn : ∼φ ∈ Γ) :
    (em φ h hn : T ⊢!ᵈᵉʳ Γ).val = Bootstrapping.axL Γ.val φ.val := rfl

noncomputable def verum (h : ⊤ ∈ Γ := by simp) : T ⊢!ᵈᵉʳ Γ :=
  ⟨verumIntro Γ.val, by simp, Theory.Derivation.verumIntro (by simp) h⟩

@[simp] lemma verum_val (h : ⊤ ∈ Γ) :
    (verum h : T ⊢!ᵈᵉʳ Γ).val = Bootstrapping.verumIntro Γ.val := rfl

noncomputable def and' (H : φ ⋏ ψ ∈ Γ) (dp : T ⊢!ᵈᵉʳ insert φ Γ) (dq : T ⊢!ᵈᵉʳ insert ψ Γ) : T ⊢!ᵈᵉʳ Γ :=
  ⟨andIntro Γ.val φ.val ψ.val dp.val dq.val, by simp,
    Theory.Derivation.andIntro (by simpa) (by simpa using dp.derivationOf) (by simpa using dq.derivationOf)⟩

@[simp] lemma and'_val  (H : φ ⋏ ψ ∈ Γ) (dp : T ⊢!ᵈᵉʳ insert φ Γ) (dq : T ⊢!ᵈᵉʳ insert ψ Γ) :
    (and' H dp dq : T ⊢!ᵈᵉʳ Γ).val = andIntro Γ.val φ.val ψ.val dp.val dq.val := rfl

noncomputable def or' (H : φ ⋎ ψ ∈ Γ) (dpq : T ⊢!ᵈᵉʳ insert φ (insert ψ Γ)) : T ⊢!ᵈᵉʳ Γ :=
  ⟨orIntro Γ.val φ.val ψ.val dpq.val, by simp, Theory.Derivation.orIntro (by simpa) (by simpa using dpq.derivationOf)⟩

@[simp] lemma or'_val (H : φ ⋎ ψ ∈ Γ) (dpq : T ⊢!ᵈᵉʳ insert φ (insert ψ Γ)) :
    (or' H dpq : T ⊢!ᵈᵉʳ Γ).val = orIntro Γ.val φ.val ψ.val dpq.val := rfl

noncomputable def all' {φ : Semiformula V L 1} (H : ∀⁰ φ ∈ Γ) (dp : T ⊢!ᵈᵉʳ insert φ.free Γ.shift) : T ⊢!ᵈᵉʳ Γ :=
  ⟨allIntro Γ.val φ.val dp.val, by simp, Theory.Derivation.allIntro (by simpa) (by simpa using dp.derivationOf)⟩

@[simp] lemma all'_val {φ : Semiformula V L 1} (H : ∀⁰ φ ∈ Γ) (dp : T ⊢!ᵈᵉʳ insert φ.free Γ.shift) :
    (all' H dp : T ⊢!ᵈᵉʳ Γ).val = allIntro Γ.val φ.val dp.val := rfl

noncomputable def exs' {φ : Semiformula V L 1} (H : ∃⁰ φ ∈ Γ) (t : Term V L) (dp : T ⊢!ᵈᵉʳ insert (φ.subst ![t]) Γ) : T ⊢!ᵈᵉʳ Γ :=
  ⟨exsIntro Γ.val φ.val t.val dp.val, by simp, Theory.Derivation.exsIntro (by simpa) (by simp) (by simpa using dp.derivationOf)⟩

@[simp] lemma exs'_val {φ : Semiformula V L 1} (H : ∃⁰ φ ∈ Γ) (t : Term V L) (dp : T ⊢!ᵈᵉʳ insert (φ.subst ![t]) Γ) :
    (exs' H t dp : T ⊢!ᵈᵉʳ Γ).val = exsIntro Γ.val φ.val t.val dp.val := rfl

noncomputable def wk (d : T ⊢!ᵈᵉʳ Δ) (h : Δ ⊆ Γ) : T ⊢!ᵈᵉʳ Γ :=
  ⟨wkRule Γ.val d.val, by simp, Theory.Derivation.wkRule (s' := Δ.val) (by simp) (by simpa) (by simp)⟩

@[simp] lemma wk_val (d : T ⊢!ᵈᵉʳ Δ) (h : Δ ⊆ Γ) : (wk d h).val = wkRule Γ.val d.val := rfl

noncomputable def shift (d : T ⊢!ᵈᵉʳ Γ) : T ⊢!ᵈᵉʳ Γ.shift :=
  ⟨shiftRule Γ.shift.val d.val, by simp, Theory.Derivation.shiftRule (by simp)⟩

@[simp] lemma shift_val (d : T ⊢!ᵈᵉʳ Γ) : (shift d).val = shiftRule Γ.shift.val d.val := rfl

noncomputable def cut (d₁ : T ⊢!ᵈᵉʳ insert φ Γ) (d₂ : T ⊢!ᵈᵉʳ insert (∼φ) Γ) : T ⊢!ᵈᵉʳ Γ :=
  ⟨cutRule Γ.val φ.val d₁.val d₂.val, by simp, Theory.Derivation.cutRule (by simpa using d₁.derivationOf) (by simpa using d₂.derivationOf)⟩

@[simp] lemma cut_val  (d₁ : T ⊢!ᵈᵉʳ insert φ Γ) (d₂ : T ⊢!ᵈᵉʳ insert (∼φ) Γ) :
    (cut d₁ d₂).val = cutRule Γ.val φ.val d₁.val d₂.val := rfl

noncomputable def and (dp : T ⊢!ᵈᵉʳ insert φ Γ) (dq : T ⊢!ᵈᵉʳ insert ψ Γ) : T ⊢!ᵈᵉʳ insert (φ ⋏ ψ) Γ :=
  Theory.Derivable.toTDerivation _
    <| by simpa using Theory.Derivable.and (by simpa using dp.toDerivable) (by simpa using dq.toDerivable)

noncomputable def or (dpq : T ⊢!ᵈᵉʳ insert φ (insert ψ Γ)) : T ⊢!ᵈᵉʳ insert (φ ⋎ ψ) Γ :=
  Theory.Derivable.toTDerivation _ <| by simpa using Theory.Derivable.or (by simpa using dpq.toDerivable)

noncomputable def all {φ : Semiformula V L 1} (dp : T ⊢!ᵈᵉʳ insert φ.free Γ.shift) : T ⊢!ᵈᵉʳ insert (∀⁰ φ) Γ :=
  Theory.Derivable.toTDerivation _ <| by
    simpa using Theory.Derivable.all (by simp) (by simpa using dp.toDerivable)

noncomputable def exs {φ : Semiformula V L 1} (t : Term V L) (dp : T ⊢!ᵈᵉʳ insert (φ.subst ![t]) Γ) : T ⊢!ᵈᵉʳ insert (∃⁰ φ) Γ :=
  Theory.Derivable.toTDerivation _ <| by
    simpa using Theory.Derivable.exs (by simp) t.isSemiterm (by simpa using dp.toDerivable)

def ofSubset (h : T ⊆ U) (d : T ⊢!ᵈᵉʳ Γ) : U ⊢!ᵈᵉʳ Γ where
  val := d.val
  derivationOf := ⟨d.derivationOf.1, d.derivationOf.2.of_ss h⟩

noncomputable def cut' (d₁ : T ⊢!ᵈᵉʳ insert φ Γ) (d₂ : T ⊢!ᵈᵉʳ insert (∼φ) Δ) : T ⊢!ᵈᵉʳ Γ ∪ Δ :=
  cut (φ := φ) (d₁.wk (by intro x; simp; tauto)) (d₂.wk (by intro x; simp; tauto))

noncomputable def modusPonens (dpq : T ⊢!ᵈᵉʳ insert (φ 🡒 ψ) Γ) (dp : T ⊢!ᵈᵉʳ insert φ Γ) : T ⊢!ᵈᵉʳ insert ψ Γ := by
  let d : T ⊢!ᵈᵉʳ insert (φ 🡒 ψ) (insert ψ Γ) := dpq.wk (insert_subset_insert_of_subset _ <| by simp)
  let b : T ⊢!ᵈᵉʳ insert (∼(φ 🡒 ψ)) (insert ψ Γ) := by
    simp only [Semiformula.imp_def, DeMorgan.or, DeMorgan.neg]
    exact and (dp.wk (insert_subset_insert_of_subset _ <| by simp))
      (em ψ (by simp) (by simp))
  exact cut d b

def ofEq (d : T ⊢!ᵈᵉʳ Γ) (h : Γ = Δ) : T ⊢!ᵈᵉʳ Δ := h ▸ d

noncomputable def rotate₁ (d : T ⊢!ᵈᵉʳ p₀ ⫽ p₁ ⫽ Γ) : T ⊢!ᵈᵉʳ p₁ ⫽ p₀ ⫽ Γ :=
  ofEq d (by ext x; simp; tauto)

noncomputable def rotate₂ (d : T ⊢!ᵈᵉʳ p₀ ⫽ p₁ ⫽ p₂ ⫽ Γ) : T ⊢!ᵈᵉʳ p₂ ⫽ p₁ ⫽ p₀ ⫽ Γ :=
  ofEq d (by ext x; simp; tauto)

noncomputable def rotate₃ (d : T ⊢!ᵈᵉʳ p₀ ⫽ p₁ ⫽ p₂ ⫽ p₃ ⫽ Γ) : T ⊢!ᵈᵉʳ p₃ ⫽ p₁ ⫽ p₂ ⫽ p₀ ⫽ Γ :=
  ofEq d (by ext x; simp; tauto)

noncomputable def orInv (d : T ⊢!ᵈᵉʳ φ ⋎ ψ ⫽ Γ) : T ⊢!ᵈᵉʳ φ ⫽ ψ ⫽ Γ := by
  have b : T ⊢!ᵈᵉʳ φ ⋎ ψ ⫽ φ ⫽ ψ ⫽ Γ := wk d (by intro x; simp; tauto)
  have : T ⊢!ᵈᵉʳ ∼(φ ⋎ ψ) ⫽ φ ⫽ ψ ⫽ Γ := by
    simp only [DeMorgan.or]
    apply and (em φ) (em ψ)
  exact cut b this

noncomputable def specialize {φ : Semiformula V L 1} (b : T ⊢!ᵈᵉʳ (∀⁰ φ) ⫽ Γ) (t : Term V L) : T ⊢!ᵈᵉʳ φ.subst ![t] ⫽ Γ := by
  apply TDerivation.cut (φ := (∀⁰ φ))
  · exact (TDerivation.wk b <| by intro x; simp; tauto)
  · rw [Semiformula.neg_all]
    apply TDerivation.exs t
    apply TDerivation.em (φ.subst ![t])

end TDerivation

namespace TProof

variable {T U : InternalTheory V L} {φ ψ : Formula V L}

/-- Condition D2 -/
noncomputable def modusPonens (d : T ⊢! φ 🡒 ψ) (b : T ⊢! φ) : T ⊢! ψ := TDerivation.modusPonens d b

noncomputable def byAxm {φ : Formula V L} (h : φ ∈' T.theory) : T ⊢! φ := TDerivation.byAxm φ h (by simp)

noncomputable def ofSubset (h : T ⊆ U) {φ : Formula V L} : T ⊢! φ → U ⊢! φ := TDerivation.ofSubset h

lemma of_subset (h : T ⊆ U) {φ : Formula V L} : T ⊢ φ → U ⊢ φ := by
  rintro ⟨b⟩; exact ⟨ofSubset h b⟩

noncomputable instance : Entailment.ModusPonens T := ⟨modusPonens⟩

noncomputable instance : Entailment.NegationEquiv T where
  negEquiv {φ} := by
    suffices T ⊢! (φ ⋎ ∼φ ⋎ ⊥) ⋏ (φ ⋏ ⊤ ⋎ ∼φ) by
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
  implyK {φ ψ} := by
    simp only [Axioms.ImplyK, Semiformula.imp_def]
    apply TDerivation.or
    apply TDerivation.rotate₁
    apply TDerivation.or
    exact TDerivation.em φ
  implyS {φ ψ r} := by
    simp only [Axioms.ImplyS, Semiformula.imp_def, DeMorgan.or, DeMorgan.neg]
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
  and₁ {φ ψ} := by
    simp only [Axioms.AndElim₁, Semiformula.imp_def, DeMorgan.and]
    apply TDerivation.or
    apply TDerivation.or
    exact TDerivation.em φ
  and₂ {φ ψ} := by
    simp only [Axioms.AndElim₂, Semiformula.imp_def, DeMorgan.and]
    apply TDerivation.or
    apply TDerivation.or
    exact TDerivation.em ψ
  and₃ {φ ψ} := by
    simp only [Axioms.AndInst, Semiformula.imp_def]
    apply TDerivation.or
    apply TDerivation.rotate₁
    apply TDerivation.or
    apply TDerivation.rotate₁
    apply TDerivation.and
    · exact TDerivation.em φ
    · exact TDerivation.em ψ
  or₁ {φ ψ} := by
    simp only [Axioms.OrInst₁, Semiformula.imp_def]
    apply TDerivation.or
    apply TDerivation.rotate₁
    apply TDerivation.or
    exact TDerivation.em φ
  or₂ {φ ψ} := by
    suffices T ⊢! ∼ψ ⋎ φ ⋎ ψ by
      simpa [Axioms.OrInst₂, Semiformula.imp_def]
    apply TDerivation.or
    apply TDerivation.rotate₁
    apply TDerivation.or
    exact TDerivation.em ψ
  or₃ {φ ψ r} := by
    suffices T ⊢! φ ⋏ ∼r ⋎ ψ ⋏ ∼r ⋎ ∼φ ⋏ ∼ψ ⋎ r by
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
  dne {φ} := by simpa [Axioms.DNE, Semiformula.imp_def] using TDerivation.or (TDerivation.em φ)

noncomputable def exsIntro (φ : Semiformula V L 1) (t : Term V L) (b : T ⊢! φ.subst ![t]) : T ⊢! (∃⁰ φ) := TDerivation.exs t b

lemma ex_intro! (φ : Semiformula V L 1) (t : Term V L) (b : T ⊢ φ.subst ![t]) : T ⊢ (∃⁰ φ) := ⟨exsIntro _ t b.get⟩

noncomputable def specialize {φ : Semiformula V L 1} (b : T ⊢! ∀⁰ φ) (t : Term V L) : T ⊢! φ.subst ![t] := TDerivation.specialize b t

noncomputable def specialize₂ {φ : Semiformula V L 2} (b : T ⊢! ∀⁰ ∀⁰ φ) (t u : Term V L) :
    T ⊢! φ.subst ![t, u] := by
  have : T ⊢! ∀⁰ Semiformula.subst (SemitermVec.q ![u]) φ := by simpa using specialize b u
  simpa [Semiformula.substs_substs] using specialize this t

noncomputable def specialize₃ {φ : Semiformula V L 3} (b : T ⊢! ∀⁰ ∀⁰ ∀⁰ φ) (t₁ t₂ t₃ : Term V L) :
    T ⊢! φ.subst ![t₁, t₂, t₃] := by
  have : T ⊢! ∀⁰ Semiformula.subst (SemitermVec.q ![t₂, t₃]) φ := by simpa using specialize₂ b t₂ t₃;
  simpa [Semiformula.substs_substs] using specialize this t₁;

noncomputable def specialize₄ {φ : Semiformula V L 4} (b : T ⊢! ∀⁰ ∀⁰ ∀⁰ ∀⁰ φ) (t₁ t₂ t₃ t₄ : Term V L) :
    T ⊢! φ.subst ![t₁, t₂, t₃, t₄] := by
  have : T ⊢! ∀⁰ Semiformula.subst (SemitermVec.q ![t₂, t₃, t₄]) φ := by simpa using specialize₃ b t₂ t₃ t₄;
  simpa [Semiformula.substs_substs] using specialize this t₁;

lemma specialize! {φ : Semiformula V L 1} (b : T ⊢ (∀⁰ φ)) (t : Term V L) : T ⊢ φ.subst ![t] := ⟨TDerivation.specialize b.get t⟩

lemma specialize₂! {φ : Semiformula V L 2} (b : T ⊢ ∀⁰ ∀⁰ φ) (t u : Term V L) :
    T ⊢ φ.subst ![t, u] := ⟨specialize₂ b.get t u⟩

lemma specialize₃! {φ : Semiformula V L 3} (b : T ⊢ ∀⁰ ∀⁰ ∀⁰ φ) (t₁ t₂ t₃ : Term V L) :
    T ⊢ φ.subst ![t₁, t₂, t₃] := ⟨specialize₃ b.get t₁ t₂ t₃⟩

lemma specialize₄! {φ : Semiformula V L 4} (b : T ⊢ ∀⁰ ∀⁰ ∀⁰ ∀⁰ φ) (t₁ t₂ t₃ t₄ : Term V L) :
    T ⊢ φ.subst ![t₁, t₂, t₃, t₄] := ⟨specialize₄ b.get _ _ _ _⟩

noncomputable def shift {φ : Formula V L} (d : T ⊢! φ) : T ⊢! φ.shift := by simpa using TDerivation.shift d

lemma shift! {φ : Formula V L} (d : T ⊢ φ) : T ⊢ φ.shift := ⟨by simpa using TDerivation.shift d.get⟩

noncomputable def all {φ : Semiformula V L 1} (dp : T ⊢! φ.free) : T ⊢! ∀⁰ φ := TDerivation.all (by simpa using dp)

noncomputable def all₂ {φ : Semiformula V L 2}
    (d : T ⊢! φ.shift.shift.subst ![Semiterm.fvar 0, Semiterm.fvar 1]) : T ⊢! ∀⁰ ∀⁰ φ := by
  apply all
  suffices
      T ⊢! ∀⁰ Semiformula.subst ![Semiterm.bvar 0, Semiterm.fvar 0] φ.shift by
    simpa [Semiformula.free, SemitermVec.q, Semiformula.shift_substs, Semiformula.substs_substs]
  apply all
  simpa [Semiformula.free, SemitermVec.q, Semiformula.shift_substs, Semiformula.substs_substs]

lemma all₂! {φ : Semiformula V L 2}
    (d : T ⊢ φ.shift.shift.subst ![Semiterm.fvar 0, Semiterm.fvar 1]) : T ⊢ ∀⁰ ∀⁰ φ :=
  ⟨all₂ d.get⟩

lemma all! {φ : Semiformula V L 1} (dp : T ⊢ φ.free) : T ⊢ ∀⁰ φ := ⟨all dp.get⟩

noncomputable def specialize_shift {φ : Semiformula V L 1} (b : T ⊢! ∀⁰ φ) (t : Term V L) :
    T ⊢! φ.shift.subst ![t] := by
  have : T ⊢! ∀⁰ φ.shift := by simpa using shift b
  exact specialize this t

noncomputable def specialize₂_shift {φ : Semiformula V L 2} (b : T ⊢! ∀⁰ ∀⁰ φ) (t u : Term V L) :
    T ⊢! φ.shift.shift.subst ![t, u] := by
  have : T ⊢! ∀⁰ ∀⁰ φ.shift.shift := by simpa using shift (shift b)
  exact specialize₂ this t u

lemma specialize₂_shift! {φ : Semiformula V L 2} (b : T ⊢ ∀⁰ ∀⁰ φ) (t u : Term V L) :
    T ⊢ φ.shift.shift.subst ![t, u] := ⟨specialize₂_shift b.get _ _⟩

noncomputable def generalizeAux {C : Formula V L} {φ : Semiformula V L 1} (dp : T ⊢! C.shift 🡒 φ.free) : T ⊢! C 🡒 ∀⁰ φ := by
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

noncomputable def generalize {Γ} {φ : Semiformula V L 1} (d : Γ.map .shift ⊢[T]! φ.free) : Γ ⊢[T]! ∀⁰ φ := by
  apply Entailment.FiniteContext.ofDef
  apply generalizeAux
  simpa [conj_shift] using Entailment.FiniteContext.toDef d

lemma generalize! {Γ} {φ : Semiformula V L 1} (d : Γ.map .shift ⊢[T] φ.free) : Γ ⊢[T] ∀⁰ φ := ⟨generalize d.get⟩

noncomputable def specializeWithCtxAux {C : Formula V L} {φ : Semiformula V L 1} (d : T ⊢! C 🡒 ∀⁰ φ) (t : Term V L) : T ⊢! C 🡒 φ.subst ![t] := by
  rw [Semiformula.imp_def] at d ⊢
  apply TDerivation.or
  apply TDerivation.rotate₁
  apply TDerivation.specialize
  exact TDerivation.wk (TDerivation.orInv d) (by intro x; simp; tauto)

noncomputable def specializeWithCtx {Γ} {φ : Semiformula V L 1} (d : Γ ⊢[T]! (∀⁰ φ)) (t) : Γ ⊢[T]! φ.subst ![t] := specializeWithCtxAux d t

lemma specialize_with_ctx! {Γ} {φ : Semiformula V L 1} (d : Γ ⊢[T] (∀⁰ φ)) (t) : Γ ⊢[T] φ.subst ![t] := ⟨specializeWithCtx d.get t⟩

open Entailment.FiniteContext Classical

noncomputable def allImpAll {Γ} {φ ψ : Semiformula V L 1} (d : Γ.map .shift ⊢[T]! φ.free 🡒 ψ.free) :
    Γ ⊢[T]! ∀⁰ φ 🡒 ∀⁰ ψ := by
  apply deduct
  apply generalize
  suffices ((∀⁰ φ.shift) :: Γ.map Semiformula.shift) ⊢[T]! ψ.free by simpa
  have hφ : ((∀⁰ φ.shift) :: Γ.map Semiformula.shift) ⊢[T]! φ.free := by
    apply specializeWithCtx
    apply byAxm₀
  have h : ((∀⁰ φ.shift) :: Γ.map Semiformula.shift) ⊢[T]! φ.free 🡒 ψ.free :=
    Entailment.FiniteContext.weakening (by simp) d
  exact h ⨀ hφ

noncomputable def all_imp_all! {Γ} {φ ψ : Semiformula V L 1} (d : Γ.map .shift ⊢[T] φ.free 🡒 ψ.free) :
    Γ ⊢[T] ∀⁰ φ 🡒 ∀⁰ ψ := ⟨allImpAll d.get⟩

noncomputable def exsImpExs {Γ} {φ ψ : Semiformula V L 1} (d : Γ.map .shift ⊢[T]! φ.free 🡒 ψ.free) : Γ ⊢[T]! ∃⁰ φ 🡒 ∃⁰ ψ := by
  apply Entailment.C_of_CNN
  suffices Γ ⊢[T]! ∀⁰ ∼ψ 🡒 ∀⁰ ∼φ by simpa
  apply allImpAll
  apply Entailment.C_of_CNN
  simpa [Semiformula.free] using d

noncomputable def exs_imp_exs! {Γ} {φ ψ : Semiformula V L 1} (d : Γ.map .shift ⊢[T] φ.free 🡒 ψ.free) :
    Γ ⊢[T] ∃⁰ φ 🡒 ∃⁰ ψ := ⟨exsImpExs d.get⟩

noncomputable def exs {φ : Semiformula V L 1} (t) (dp : T ⊢! φ.subst ![t]) : T ⊢! ∃⁰ φ := TDerivation.exs t (by simpa using dp)

lemma exs! {φ : Semiformula V L 1} (t) (dp : T ⊢ φ.subst ![t]) : T ⊢ ∃⁰ φ := ⟨exs t dp.get⟩

variable (A : InternalTheory V ℒₒᵣ)

open Bootstrapping.Arithmetic

open Entailment Theory.Derivation

lemma substItrDisj_right {i z : V}
    (w : TermVec V ℒₒᵣ m) (φ : Semiformula V ℒₒᵣ (m + 1)) (hi : i < z) :
    A ⊢ φ.subst (𝕹 i :> w) 🡒 φ.substItrDisj w z := Theory.Provable.toTProvable <| Theory.Derivable.toProvable <| by
  apply Theory.Derivable.or
  apply Theory.Derivable.exchange
  apply Theory.Derivable.disj (L := ℒₒᵣ) (i := z - (i + 1)) _
  · intro i hi
    have hi : i < z := by simpa using hi
    rw [substItr_nth _ _ _ hi]
    exact φ.isSemiformula.subst (w.isSemitermVec.adjoin (by simp))
  · simpa using pos_of_gt hi
  · have : z - (i + 1) < z := by simpa using pos_of_gt hi
    rw [substItr_nth _ _ _ this]
    have : z - (z - (i + 1) + 1) = i := sub_succ_lt_selfs hi
    simp only [this, Nat.succ_eq_add_one, Semiformula.val_substs, SemitermVec.val_succ,
      Matrix.head_cons, Matrix.tail_cons]
    apply Theory.Derivable.em (L := ℒₒᵣ) (p := subst ℒₒᵣ (numeral i ∷ SemitermVec.val w) φ.val)
    · simpa using φ.isSemiformula_succ.subst (w.isSemitermVec.adjoin (numeral_semiterm 0 i))
    · simp
    · simp

lemma substItrDisj_right_intro {ψ} {i z : V} {w : TermVec V ℒₒᵣ m} {φ : Semiformula V ℒₒᵣ (m + 1)}
    (hi : i < z) (h : A ⊢ ψ 🡒 φ.subst (𝕹 i :> w)) :
     A ⊢ ψ 🡒 φ.substItrDisj w z :=
  Entailment.C!_trans h (substItrDisj_right A w φ hi)

lemma substItrConj_right_intro {ψ} {w : TermVec V ℒₒᵣ m} {φ : Semiformula V ℒₒᵣ (m + 1)} {z : V}
    (h : ∀ i < z, A ⊢ ψ 🡒 φ.subst (𝕹 i :> w)) :
    A ⊢ ψ 🡒 φ.substItrConj w z := Theory.Provable.toTProvable <| Theory.Derivable.toProvable <| by
  apply Theory.Derivable.or
  apply Theory.Derivable.exchange
  apply Theory.Derivable.conj
  · simp
  · intro i hi
    have hi : i < z := by simpa using hi
    rw [substItr_nth _ _ _ hi]
    apply Theory.Derivable.exchange
    suffices A ⊢!ᵈᵉʳ (∼ψ ⫽ φ.subst (𝕹 (z - (i + 1)) :> w) ⫽ ∅) by
      simpa using this.toDerivable
    have : A ⊢ ∼ψ ⋎ Semiformula.subst (typedNumeral (z - (i + 1)) :> w) φ := h (z - (i + 1)) (by simp [pos_of_gt hi])
    exact TDerivation.orInv (proof_to_tDerivation this.get)

open Classical in
lemma substItrDisj_left_intro {ψ} {w : TermVec V ℒₒᵣ m} {φ : Semiformula V ℒₒᵣ (m + 1)} {z : V}
    (h : ∀ i < z, A ⊢ φ.subst (𝕹 i :> w) 🡒 ψ) :
    A ⊢ φ.substItrDisj w z 🡒 ψ := by
  apply Entailment.C!_of_CNN!
  simp only [Semiformula.substItrDisj_neg]
  apply substItrConj_right_intro
  intro i hi
  apply Entailment.C!_of_CNN!
  simpa using h i hi

end TProof

end typed_derivation
