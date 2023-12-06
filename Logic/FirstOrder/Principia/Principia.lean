import Logic.FirstOrder.Basic
import Logic.Vorspiel.String

namespace LO

namespace FirstOrder

variable {L : Language.{u}} [∀ k, DecidableEq (L.Func k)] [∀ k, DecidableEq (L.Rel k)]

variable {T : Theory L} {μ : Type v}

open Rew Subformula DerivationCR DerivationCRWA

/-
def SequentList.fvarList (l : List $ Subformula L μ n) : List μ :=
  l.bind Subformula.fvarList

def fleshVar (C : List $ SyntacticFormula L) : ℕ := (SequentList.fvarList C).sup
-/

def ProofArrow (T : Theory L) (Δ : List (SyntacticFormula L)) (p : SyntacticFormula L) := T ⊢' insert p (Δ.map (~·)).toFinset

noncomputable def Proof.toProofArrow {σ : Sentence L} (b : T ⊢ σ) : ProofArrow T [] (Rew.emb.hom σ) := b.cast (by simp)

namespace ProofArrow

variable {Δ Γ : List (SyntacticFormula L)}

def toDerivationCWA (b : ProofArrow T Δ p) : T ⊢' insert p (Δ.map (~·)).toFinset := b

def toProof {σ : Sentence L} (b : ProofArrow T [] (Rew.emb.hom σ)) : T ⊢ σ := b.cast (by simp)

def cast {p p'} (b : ProofArrow T Δ p) (h : p = p') : ProofArrow T Δ p' :=
  h ▸ b

def cast' {Δ Δ' p p'} (b : ProofArrow T Δ p) (hΔ : Δ = Δ') (hp : p = p') : ProofArrow T Δ' p' :=
  hΔ ▸ hp ▸ b

protected def rewrite (f : ℕ → SyntacticTerm L) {p} (b : ProofArrow T Δ p) :
    ProofArrow T (Δ.map $ (Rew.rewrite f).hom) ((Rew.rewrite f).hom p) :=
  (b.toDerivationCWA.rewrite f).cast (by simp[Function.comp, List.toFinset_map, Finset.image_image])

protected def shift {p} (b : ProofArrow T Δ p) : ProofArrow T (Δ.map shift.hom) (shift.hom p) := b.rewrite _

def byAxiom {σ} (h : σ ∈ T) : ProofArrow T Δ (Rew.emb.hom σ) :=
  DerivationCRWA.byAxiom (σ := σ) h (by simp)

def trans {p q} (b₁ : ProofArrow T Δ p) (b₂ : ProofArrow T (p :: Δ) q) : ProofArrow T Δ q :=
  let b₁' : T ⊢' insert p (Δ.map (~·)).toFinset := b₁
  let b₂' : T ⊢' insert (~p) (insert q (Δ.map (~·)).toFinset) := b₂.toDerivationCWA.cast (by simp[Finset.Insert.comm])
  (b₁'.cCut b₂').cast (by simp)

def assumption {p} (h : p ∈ Δ) : ProofArrow T Δ p := DerivationCRWA.em (p := p) (by simp) (by simp[h])

def weakening' {p q} (h : ~p :: Δ ⊆ ~q :: Γ) (b : ProofArrow T Δ p) : ProofArrow T Γ q :=
  b.toDerivationCWA.weakeningRight (by simpa using List.toFinset_mono (List.map_subset (~·) h))

def weakening {p} (h : Δ ⊆ Γ) (b : ProofArrow T Δ p) : ProofArrow T Γ p :=
  b.weakening' (List.cons_subset_cons _ h)

def exchange {p q} (b : ProofArrow T (p :: Δ) q) : ProofArrow T (~q :: Δ) (~p) :=
  b.toDerivationCWA.cast (by simp[Finset.Insert.comm])

def contradiction {p} (q) (b₁ : ProofArrow T Δ p) (b₂ : ProofArrow T Δ (~p)) : ProofArrow T Δ q :=
  (b₁.toDerivationCWA.cCut' b₂.toDerivationCWA).weakeningRight (Finset.subset_insert _ _)

def trivial : ProofArrow T Δ ⊤ := DerivationCRWA.verum (by simp)

def explode {p} (b : ProofArrow T Δ ⊥) : ProofArrow T Δ p := b.contradiction p (by simpa using trivial)

def intro {p q} (b : ProofArrow T (p :: Δ) q) : ProofArrow T Δ (p ⟶ q) :=
  let b : T ⊢' (insert (~p) $ insert q (Δ.map (~·)).toFinset) := b.toDerivationCWA.cast (by simp[Finset.Insert.comm])
  b.or'

def absurd {p} (b : ProofArrow T (p :: Δ) ⊥) : ProofArrow T Δ (~p) :=
  let b₁ : T ⊢' insert ⊥ (insert (~p) (Δ.map (~·)).toFinset) := b.toDerivationCWA.cast (by simp)
  let b₂ : T ⊢' insert ⊤ (insert (~p) (Δ.map (~·)).toFinset) := DerivationCRWA.verum (by simp)
  b₁.cCut' b₂

def modusPonens {p q} (b₁ : ProofArrow T Δ (p ⟶ q)) (b₂ : ProofArrow T Δ p) : ProofArrow T Δ q :=
    let b₁₁ : T ⊢' insert (~p ⋎ q) (Δ.map (~·)).toFinset := b₁
    let b₂₁ : T ⊢' insert p (insert q (Δ.map (~·)).toFinset) :=
      b₂.toDerivationCWA.weakeningRight (by simp[Finset.Insert.comm p])
    let b₃ : T ⊢' insert (~q) (insert q (Δ.map (~·)).toFinset) := DerivationCRWA.em (p := q) (by simp) (by simp)
    let b₄ : T ⊢' insert (~(~p ⋎ q)) (insert q (Δ.map (~·)).toFinset) := by simpa using (b₂₁.and' b₃)
    (b₁₁.cCut b₄).cast (by simp)

def split {p q} (b₁ : ProofArrow T Δ p) (b₂ : ProofArrow T Δ q) : ProofArrow T Δ (p ⋏ q) :=
  b₁.toDerivationCWA.and' b₂.toDerivationCWA

def splits : {k : ℕ} → {p : Fin k → SyntacticFormula L} → ((i : Fin k) → ProofArrow T Δ (p i)) →
    ProofArrow T Δ (Matrix.conj p)
  | 0,     _, _ => trivial
  | _ + 1, p, b => split (b 0) (splits (p := Matrix.vecTail p) (fun i => b i.succ))

def andLeft {p q} (b : ProofArrow T Δ (p ⋏ q)) : ProofArrow T Δ p :=
  let b' : T ⊢' insert (~(p ⋏ q)) (insert p (Δ.map (~·)).toFinset) := or' (DerivationCRWA.em (p := p) (by simp) (by simp[←neg_eq]))
  (b.toDerivationCWA.cCut b').cast (by simp)

def andRight {p q} (b : ProofArrow T Δ (p ⋏ q)) : ProofArrow T Δ q :=
  let b' : T ⊢' insert (~(p ⋏ q)) (insert q (Δ.map (~·)).toFinset) := or' (DerivationCRWA.em (p := q) (by simp) (by simp[←neg_eq]))
  (b.toDerivationCWA.cCut b').cast (by simp)

def destruct {p q r} (b₀ : ProofArrow T Δ (p ⋏ q)) (b : ProofArrow T (p :: q :: Δ) r) : ProofArrow T Δ r :=
  have : ProofArrow T Δ p := b₀.trans (andLeft (q := q) $ assumption $ by simp)
  have b' : ProofArrow T (q :: Δ) r := (this.weakening (by simp)).trans b
  have : ProofArrow T Δ q := b₀.trans (andRight (p := p) $ assumption $ by simp)
  this.trans b'

def byConj : {n : ℕ} → (p : Fin n → SyntacticFormula L) →
    (b : ProofArrow T Δ (Matrix.conj p)) → (i : Fin n) → ProofArrow T Δ (p i)
  | 0,     p, _ => fun i => by have : False := finZeroElim (α := fun _ => False) i; contradiction
  | n + 1, p, b => Fin.cases (andLeft b) (byConj (Matrix.vecTail p) (b.andRight))

def orLeft {p q} (b : ProofArrow T Δ p) : ProofArrow T Δ (p ⋎ q) :=
  (b.toDerivationCWA.weakeningRight (by simp[Finset.Insert.comm p])).or'

def orRight {p q} (b : ProofArrow T Δ q) : ProofArrow T Δ (p ⋎ q) :=
  (b.toDerivationCWA.weakeningRight (by simp[Finset.Insert.comm q])).or'

def cases {p q r} (b₀ : ProofArrow T Δ (p ⋎ q)) (b₁ : ProofArrow T (p :: Δ) r) (b₂ : ProofArrow T (q :: Δ) r) : ProofArrow T Δ r :=
  let b₁' : T ⊢' insert (~p) (insert r (Δ.map (~·)).toFinset) := b₁.toDerivationCWA.cast (by simp[Finset.Insert.comm])
  let b₂' : T ⊢' insert (~q) (insert r (Δ.map (~·)).toFinset) := b₂.toDerivationCWA.cast (by simp[Finset.Insert.comm])
  let b₃ : T ⊢' insert (~(p ⋎ q)) (insert r (Δ.map (~·)).toFinset) := by simpa using b₁'.and' b₂'
  (b₀.toDerivationCWA.cCut b₃).cast (by simp)

def generalize {p} (b : ProofArrow T (Δ.map shift.hom) (free.hom p)) : ProofArrow T Δ (∀' p) :=
  let b' : T ⊢' insert (free.hom p) (shifts (Δ.map (~·)).toFinset) :=
    b.toDerivationCWA.cast (by simp[shifts_eq_image, List.toFinset_map, Finset.image_image, Function.comp])
  b'.all'

def specialize (t) {p} (b : ProofArrow T Δ (∀' p)) : ProofArrow T Δ ([→ t].hom p) :=
  have b' : T ⊢' insert (∃' ~p) (insert ([→ t].hom p) (Δ.map (~·)).toFinset) :=
    DerivationCRWA.ex' (t := t) (DerivationCRWA.em (p := [→ t].hom p) (by simp) (by simp))
  (b.toDerivationCWA.cCut b').cast (by simp)

def specializes : {n : ℕ} → (v : Fin n → SyntacticTerm L) → {p : SyntacticSubformula L n} →
    ProofArrow T Δ (univClosure p) → ProofArrow T Δ ((substs v).hom p)
  | 0,     v, p, b => b.cast (by simp)
  | n + 1, v, p, b =>
    let b : ProofArrow T Δ (∀' (substs (#(Fin.last 0) :> bShift ∘ v ∘ Fin.succ)).hom p) :=
      by simpa using specializes (v ∘ Fin.succ) b
    (specialize (v 0) b).cast (by simp[←Rew.hom_comp_app]; congr; ext x <;> simp[Rew.comp_app]; cases x using Fin.cases <;> simp)

def useInstance (t) {p} (b : ProofArrow T Δ ([→ t].hom p)) : ProofArrow T Δ (∃' p) := b.ex'

def exCases {p q} (b₀ : ProofArrow T Δ (∃' p))
  (b₁ : ProofArrow T (free.hom p :: Δ.map shift.hom) (shift.hom q)) : ProofArrow T Δ q :=
  let b₁₁ : T ⊢' (insert (free.hom $ ~p) $ shifts $ insert q (Δ.map (~·)).toFinset) :=
    b₁.toDerivationCWA.cast
      (by simp[shifts_eq_image, List.toFinset_map, Finset.Insert.comm (shift.hom q), Finset.image_image, Function.comp])
  let b₁₂ : T ⊢' (insert (∀' ~p) $ insert q (Δ.map (~·)).toFinset) := b₁₁.all'
  (b₀.toDerivationCWA.cCut b₁₂).cast (by simp)

section Eq
variable [L.Eq] [EqTheory T]
open Subterm Subformula Theory Eq

def eqRefl (t : SyntacticTerm L) : ProofArrow T Δ (“!!t = !!t”) :=
  have b : ProofArrow T Δ (“∀ #0 = #0”) := (byAxiom (EqTheory.eq Theory.Eq.refl)).cast (by simp)
  (specialize t b).cast (by simp)

def eqSymm {t₁ t₂ : SyntacticTerm L} (b : ProofArrow T Δ “!!t₁ = !!t₂”) : ProofArrow T Δ “!!t₂ = !!t₁” :=
  have : ProofArrow T Δ “∀ ∀ (#1 = #0 → #0 = #1)” :=
    (byAxiom (EqTheory.eq Theory.Eq.symm)).cast (by simp)
  have : ProofArrow T Δ “!!t₁ = !!t₂ → !!t₂ = !!t₁” := (this.specializes ![t₂, t₁]).cast (by simp)
  this.modusPonens  b

def eqTrans {t₁ t₂ t₃ : SyntacticTerm L} (b₁ : ProofArrow T Δ “!!t₁ = !!t₂”) (b₂ : ProofArrow T Δ “!!t₂ = !!t₃”) :
    ProofArrow T Δ “!!t₁ = !!t₃” :=
  have : ProofArrow T Δ “∀ ∀ ∀ (#2 = #1 → #1 = #0 → #2 = #0)” :=
    (byAxiom (EqTheory.eq Theory.Eq.trans)).cast (by simp)
  have : ProofArrow T Δ “!!t₁ = !!t₂ → !!t₂ = !!t₃ → !!t₁ = !!t₃” := (this.specializes ![t₃, t₂, t₁]).cast (by simp)
  (this.modusPonens b₁).modusPonens b₂

def termExt : (t : SyntacticSubterm L n) → (v₁ v₂ : Fin n → SyntacticTerm L) →
    ((i : Fin n) → ProofArrow T Δ “!!(v₁ i) = !!(v₂ i)”) → ProofArrow T Δ “!!(substs v₁ t) = !!(substs v₂ t)”
  | #x,       _,  _,  b => b x
  | &x,       _,  _,  _ => eqRefl &x
  | func f v, v₁, v₂, b =>
    have : ProofArrow T Δ
      “∀* ((⋀ i, !!(varSumInL i) = !!(varSumInR i)) →
      !!(func f varSumInL) = !!(func f varSumInR))” :=
    (byAxiom (EqTheory.eq (Theory.Eq.funcExt f))).cast (by simp[vecEq, Matrix.hom_conj']; rfl)
    have : ProofArrow T Δ
      “(⋀ i, !!(substs v₁ $ v i) = !!(substs v₂ $ v i)) → !!(func f fun i => substs v₁ (v i)) = !!(func f fun i => substs v₂ (v i))” :=
      by simpa [Matrix.hom_conj', Rew.func] using
        this.specializes (Matrix.vecAppend rfl (fun i => substs v₁ (v i)) (fun i => substs v₂ (v i)))
    this.modusPonens (splits fun i => termExt (v i) v₁ v₂ b)

private def negImply {p q : SyntacticFormula L} (b : ProofArrow T Δ (p ⟶ q)) : ProofArrow T Δ (~q ⟶ ~p) :=
  (b.trans $ intro $ absurd $ trans (p := q) (modusPonens (p := p) (assumption $ by simp) (assumption $ by simp)) $
    contradiction (p := q) ⊥ (assumption $ by simp) (assumption $ by simp))

private def relExtAux {n} {k} (r : L.Rel k) (v : Fin k → SyntacticSubterm L n) (v₁ v₂ : Fin n → SyntacticTerm L)
  (b : (i : Fin n) → ProofArrow T Δ “!!(v₁ i) = !!(v₂ i)”) : ProofArrow T Δ ((substs v₁).hom (rel r v) ⟶ (substs v₂).hom (rel r v)) :=
  have : ProofArrow T Δ
    “∀* ((⋀ i, !!(varSumInL i) = !!(varSumInR i)) → (!(rel r varSumInL) → !(rel r varSumInR)))” :=
  (byAxiom (EqTheory.eq (Theory.Eq.relExt r))).cast (by simp[vecEq, Matrix.hom_conj']; simp[Rew.rel])
  have : ProofArrow T Δ “(⋀ i, !!(substs v₁ (v i)) = !!(substs v₂ (v i))) →
    !(rel r fun i => substs v₁ (v i)) → !(rel r fun i => substs v₂ (v i))” := by
  { have := this.specializes (Matrix.vecAppend rfl (fun i => substs v₁ (v i)) (fun i => substs v₂ (v i)));
    simp[Matrix.hom_conj', Rew.func] at this; simpa[Rew.rel] using this }
  (this.modusPonens (splits fun i => termExt (v i) v₁ v₂ b)).cast (by simp[Rew.rel])

private lemma free_substs_eq_substs_shift {n'} (w : Fin n' → SyntacticSubterm L (n + 1)) (p : SyntacticSubformula L n') :
    free.hom ((substs w).hom p) = (substs (fun i => Rew.free (w i))).hom (shift.hom p) :=
  by simp[←Rew.hom_comp_app]; apply Rew.hom_ext'; ext x <;> simp[Rew.comp_app]

-- 不要だが計算を軽くするために`noncomputable`をつけている
noncomputable def formulaExtAux : {Δ : List (SyntacticFormula L)} → {n : ℕ} → (p : SyntacticSubformula L n) → (v₁ v₂ : Fin n → SyntacticTerm L) →
    ((i : Fin n) → ProofArrow T Δ “!!(v₁ i) = !!(v₂ i)”) → ProofArrow T Δ ((substs v₁).hom p ⟶ (substs v₂).hom p)
  | Δ, _, ⊤,        v₁, v₂, _ => (intro $ assumption $ by simp)
  | Δ, _, ⊥,        v₁, v₂, _ => (intro $ assumption $ by simp)
  | Δ, _, rel r v,  v₁, v₂, b => relExtAux r v v₁ v₂ b
  | Δ, _, nrel r v, v₁, v₂, b => (relExtAux r v v₂ v₁ (fun i => eqSymm (b i))).negImply.cast (by simp[Rew.rel, Rew.nrel])
  | Δ, _, p ⋏ q,    v₁, v₂, b => by
    simp
    have bp : ProofArrow T Δ ((substs v₁).hom p ⟶ (substs v₂).hom p) := formulaExtAux p v₁ v₂ b
    have bq : ProofArrow T Δ ((substs v₁).hom q ⟶ (substs v₂).hom q) := formulaExtAux q v₁ v₂ b
    exact (intro $ split
      (modusPonens (bp.weakening $ by simp) (andLeft (q := (substs v₁).hom q) $ assumption $ by simp))
      (modusPonens (bq.weakening $ by simp) (andRight (p := (substs v₁).hom p) $ assumption $ by simp)))
  | Δ, _, p ⋎ q,    v₁, v₂, b => by
    simp
    have bp : ProofArrow T Δ ((substs v₁).hom p ⟶ (substs v₂).hom p) := formulaExtAux p v₁ v₂ b
    have bq : ProofArrow T Δ ((substs v₁).hom q ⟶ (substs v₂).hom q) := formulaExtAux q v₁ v₂ b
    exact (intro $ cases (p := (substs v₁).hom p) (q := (substs v₁).hom q) (assumption $ by simp)
      (orLeft $ modusPonens (bp.weakening $ List.subset_cons_of_subset _ $ by simp) $ assumption $ by simp)
      (orRight $ modusPonens (bq.weakening $ List.subset_cons_of_subset _ $ by simp) $ assumption $ by simp))
  | Δ, _, ∀' p,     v₁, v₂, b =>
    let Δ' := (∀' shift.hom ((substs (#0 :> bShift ∘ v₁)).hom p)) :: Δ.map shift.hom
    let v₁' := fun i => Rew.free (#0 :> bShift ∘ v₁ $ i)
    let v₂' := fun i => Rew.free (#0 :> bShift ∘ v₂ $ i)
    have b' : (i : Fin _) → ProofArrow T Δ' (“!!(v₁' i) = !!(v₂' i)”) :=
      Fin.cases (eqRefl _) (fun i => ((b i).shift.weakening (by simp)).cast (by simp))
    have bp : ProofArrow T Δ' ((substs v₁').hom $ shift.hom p) :=
      (specialize &0 (p := shift.hom ((substs (#0 :> bShift ∘ v₁)).hom p)) $ assumption $ by simp).cast
      (by simp[←free_substs_eq_substs_shift]; rw[←Rew.hom_comp_app [→ &0]]; simp[substs_mbar_zero_comp_shift_eq_free])
    have : ProofArrow T Δ' ((substs v₂').hom $ shift.hom p) := modusPonens (formulaExtAux (shift.hom p) v₁' v₂' b') bp
    have : ProofArrow T Δ (∀' (substs (#0 :> bShift ∘ v₁)).hom p ⟶ ∀' (substs (#0 :> bShift ∘ v₂)).hom p) :=
      (intro $ generalize $ this.cast' (by simp) (by simp[free_substs_eq_substs_shift]))
    this.cast (by simp; rfl)
  | Δ, _, ∃' p,     v₁, v₂, b =>
    let Δ' := (substs fun i => Rew.free ((#0 :> bShift ∘ v₁) i)).hom (shift.hom p) ::
        (∃' shift.hom ((substs (#0 :> bShift ∘ v₁)).hom p)) :: Δ.map shift.hom
    let v₁' := fun i => free (#0 :> bShift ∘ v₁ $ i)
    let v₂' := fun i => free (#0 :> bShift ∘ v₂ $ i)
    have b' : (i : Fin _) → ProofArrow T Δ' (“!!(v₁' i) = !!(v₂' i)”) :=
      Fin.cases (eqRefl _) (fun i => ((b i).shift.weakening $ List.subset_cons_of_subset _ $ by simp).cast (by simp))
    have ih : ProofArrow T Δ' ((substs v₁').hom (shift.hom p) ⟶ (substs v₂').hom (shift.hom p)) := formulaExtAux (Δ := Δ') (shift.hom p) v₁' v₂' b'
    have : ProofArrow T Δ' (∃' shift.hom ((substs (#0 :> bShift ∘ v₂)).hom p)) :=
      (useInstance &0 $ (ih.modusPonens (assumption $ by simp)).cast
      (by simp[←free_substs_eq_substs_shift]; rw[←Rew.hom_comp_app [→ &0]]; simp[substs_mbar_zero_comp_shift_eq_free]))
    have : ProofArrow T Δ (∃' (substs (#0 :> bShift ∘ v₁)).hom p ⟶ ∃' (substs (#0 :> bShift ∘ v₂)).hom p) :=
      (intro $ exCases (p := (substs (#0 :> bShift ∘ v₁)).hom p) (assumption $ by simp) (this.cast' (by simp[free_substs_eq_substs_shift]) (by simp)))
    this.cast (by simp; rfl)
  termination_by formulaExtAux p _ _ _ => p.complexity

noncomputable def formulaExt (p : SyntacticSubformula L n) (v₁ v₂ : Fin n → SyntacticTerm L)
  (b : (i : Fin n) → ProofArrow T Δ “!!(v₁ i) = !!(v₂ i)”) (d : ProofArrow T Δ ((substs v₂).hom p)) :
    ProofArrow T Δ ((substs v₁).hom p) :=
  (formulaExtAux p v₂ v₁ (fun i => (b i).eqSymm)).modusPonens d

noncomputable def rewriteEq {p : SyntacticSubformula L 1} {t₁ t₂ : SyntacticTerm L}
  (b : ProofArrow T Δ “!!t₁ = !!t₂”) (d : ProofArrow T Δ ([→ t₂].hom p)) :
    ProofArrow T Δ ([→ t₁].hom p) :=
  ((formulaExtAux p ![t₂] ![t₁] (fun i => b.eqSymm.cast $ by simp)).modusPonens
    (d.cast $ by simp)).cast (by simp)

end Eq

end ProofArrow

variable (T)
variable [L.Eq] [EqTheory T]

inductive Principia : List (SyntacticFormula L) → SyntacticFormula L → Type u
  | tauto {Δ p} : ProofArrow T Δ p → Principia Δ p
  | axm {Δ σ} :
    σ ∈ T → Principia Δ (emb.hom σ)
  | weakening' {Δ Γ p q} :
    ~p :: Δ ⊆ ~q :: Γ → Principia Δ p → Principia Γ q
  | rewrite (f : ℕ → SyntacticTerm L) {p} :
    Principia Δ p → Principia (Δ.map $ (rewrite f).hom) ((rewrite f).hom p)
  | trans {Δ p q} :
    Principia Δ p → Principia (p :: Δ) q → Principia Δ q
  | assumption {Δ p} :
    p ∈ Δ → Principia Δ p
  | contradiction {Δ p} (q) :
    Principia Δ p → Principia Δ (~p) → Principia Δ q
  -- ⊤ - right
  | trivial {Δ} : Principia Δ ⊤
  -- ⊥ - left
  | explode {Δ p} : Principia Δ ⊥ → Principia Δ p
  -- → right
  | intro {Δ p q} : Principia (p :: Δ) q → Principia Δ (p ⟶ q)
  -- → left
  | modusPonens {Δ p q} :
    Principia Δ (p ⟶ q) → Principia Δ p → Principia Δ q
  -- ∧ right
  | split {Δ p q} :
    Principia Δ p → Principia Δ q →Principia Δ (p ⋏ q)
  -- ∧ left
  | andLeft {Δ p q} :
    Principia Δ (p ⋏ q) → Principia Δ p
  | andRight {Δ p q} :
    Principia Δ (p ⋏ q) → Principia Δ q
  -- ∨ right
  | orLeft {Δ p q} :
    Principia Δ p → Principia Δ (p ⋎ q)
  | orRight {Δ p q} :
    Principia Δ q → Principia Δ (p ⋎ q)
  -- ∨ left
  | cases {Δ p q r} :
    Principia Δ (p ⋎ q) → Principia (p :: Δ) r → Principia (q :: Δ) r → Principia Δ r
  -- ∀ right
  | generalize {Δ} {p} :
    Principia (Δ.map shift.hom) (free.hom p) → Principia Δ (∀' p)
  -- ∀ left
  | specialize (t) {Δ p} :
    Principia Δ (∀' p) → Principia Δ ([→ t].hom p)
  -- ∃ right
  | useInstance (t) {Δ p} :
    Principia Δ ([→ t].hom p) → Principia Δ (∃' p)
  -- ∃ left
  | exCases {Δ p q} :
    Principia Δ (∃' p) → Principia (free.hom p :: Δ.map shift.hom) (shift.hom q) → Principia Δ q
  -- =
  | eqRefl {Δ} (t) :
    Principia Δ “!!t = !!t”
  | eqSymm {Δ t₁ t₂} :
    Principia Δ “!!t₁ = !!t₂” → Principia Δ “!!t₂ = !!t₁”
  | eqTrans {Δ t₁ t₂ t₃} :
    Principia Δ “!!t₁ = !!t₂” → Principia Δ “!!t₂ = !!t₃” → Principia Δ “!!t₁ = !!t₃”
  | rewriteEq {Δ} {p : SyntacticSubformula L 1} {t₁ t₂ : SyntacticTerm L} :
    Principia Δ “!!t₁ = !!t₂” → Principia Δ ([→ t₂].hom p) → Principia Δ ([→ t₁].hom p)

notation Δ:0 " ⟹[" T "] " p => Principia T Δ p

variable {T}

namespace Principia
open ProofArrow

section Repr

variable [∀ k, ToString (L.Func k)] [∀ k, ToString (L.Rel k)]

def _root_.String.turnstile {α β} [ToString α] [ToString β] (Γ : List α) (b : β) : String :=
  Γ.seqStr toString ", " ++ " \\vdash " ++ toString b

def _root_.String.Bussproof.axiomc (Γ : String) : String :=
  "\\AxiomC{" ++ Γ ++ "}\n"

def _root_.String.Bussproof.unalyinfc (U s Δ : String) : String :=
  U ++
  "\\RightLabel{\\scriptsize $" ++ s ++ "$}\n" ++
  "\\UnaryInfC{$" ++  Δ ++ "$}\n\n"

def _root_.String.Bussproof.binaryinfc (U₁ U₂ s Δ : String) : String :=
  U₁ ++ U₂ ++
  "\\RightLabel{\\scriptsize $" ++ s ++ "$}\n" ++
  "\\BinaryInfC{$" ++ Δ ++ "$}\n\n"

def _root_.String.Bussproof.trinaryinfc (U₁ U₂ U₃ s Δ : String) : String :=
  U₁ ++ U₂ ++ U₃ ++
  "\\RightLabel{\\scriptsize $" ++ s ++ "$}\n" ++
  "\\TrinaryInfC{$" ++ Δ ++ "$}\n\n"

open String

def toStr : {Δ : List (SyntacticFormula L)} → {p : SyntacticFormula L} → (Δ ⟹[T] p) → String
  | Δ, p, tauto _               =>
    String.Bussproof.unalyinfc (Bussproof.axiomc "") "\\mathsf{OF PROOFARROW}" (String.turnstile Δ p)
  | Δ, _, axm (σ := σ) _        =>
    String.Bussproof.unalyinfc (Bussproof.axiomc "") "\\mathsf{AX}" (String.turnstile Δ σ)
  | Δ, p, weakening' _ d        =>
    String.Bussproof.unalyinfc d.toStr "\\mathsf{W}" (String.turnstile Δ p)
  | _, _, rewrite (Δ := Δ) (p := p) f d           =>
    String.Bussproof.unalyinfc d.toStr "\\mathsf{REW}" (String.turnstile (Δ.map (Rew.rewrite f).hom) ((Rew.rewrite f).hom p))
  | Δ, q, trans c₁ c₂           =>
    String.Bussproof.binaryinfc c₁.toStr c₂.toStr "\\mathsf{CUT}" (String.turnstile Δ q)
  | Δ, p, assumption _          =>
    String.Bussproof.unalyinfc (Bussproof.axiomc "") "\\mathsf{I}" (String.turnstile Δ p)
  | Δ, q, contradiction _ c₁ c₂ =>
    String.Bussproof.binaryinfc c₁.toStr c₂.toStr "\\mathsf{CONTRA}" (String.turnstile Δ q)
  | Δ, _, trivial               =>
    String.Bussproof.unalyinfc (Bussproof.axiomc "") "\\top_\\mathsf{INTRO}" (String.turnstile Δ (⊤ : SyntacticFormula L))
  | Δ, p, explode d             =>
    String.Bussproof.unalyinfc d.toStr "\\bot_\\mathsf{ELIM}" (String.turnstile Δ p)
  | Δ, _, intro (p := p) (q := q) d               =>
    String.Bussproof.unalyinfc d.toStr "\\to_\\mathsf{INTRO}" (String.turnstile Δ (p ⟶ q))
  | Δ, q, modusPonens c₁ c₂     =>
    String.Bussproof.binaryinfc c₁.toStr c₂.toStr "\\to_\\mathsf{ELIM}" (String.turnstile Δ q)
  | Δ, _, split (p := p) (q := q) c₁ c₂           =>
    String.Bussproof.binaryinfc c₁.toStr c₂.toStr "\\wedge_\\mathsf{INTRO}" (String.turnstile Δ (p ⋏ q))
  | Δ, p, andLeft d             =>
    String.Bussproof.unalyinfc d.toStr "\\wedge_\\mathsf{ELIM}" (String.turnstile Δ p)
  | Δ, p, andRight d            =>
    String.Bussproof.unalyinfc d.toStr "\\wedge_\\mathsf{ELIM}" (String.turnstile Δ p)
  | Δ, _, orLeft (p := p) (q := q) d =>
    String.Bussproof.unalyinfc d.toStr "\\vee_\\mathsf{INTRO}" (String.turnstile Δ (p ⋎ q))
  | Δ, _, orRight (p := p) (q := q) d =>
    String.Bussproof.unalyinfc d.toStr "\\vee_\\mathsf{INTRO}" (String.turnstile Δ (p ⋎ q))
  | Δ, r, cases c₀ c₁ c₂        =>
    String.Bussproof.trinaryinfc c₀.toStr c₁.toStr c₂.toStr "\\vee_\\mathsf{ELIM}" (String.turnstile Δ r)
  | Δ, _, generalize (p := p) d =>
    String.Bussproof.unalyinfc d.toStr "\\forall_\\mathsf{INTRO}" (String.turnstile Δ (∀' p))
  | Δ, _, specialize (p := p) t d =>
    String.Bussproof.unalyinfc d.toStr "\\forall_\\mathsf{ELIM}" (String.turnstile Δ ([→ t].hom p))
  | Δ, _, useInstance (p := p) _ d =>
    String.Bussproof.unalyinfc d.toStr "\\exists_\\mathsf{INTRO}" (String.turnstile Δ (∃' p))
  | Δ, q, exCases c₀ c₁         =>
    String.Bussproof.binaryinfc c₀.toStr c₁.toStr "\\exists_\\mathsf{ELIM}" (String.turnstile Δ q)
  | Δ, _, eqRefl t              =>
    String.Bussproof.unalyinfc (Bussproof.axiomc "") "=_\\mathsf{REFL}" (String.turnstile Δ “!!t = !!t”)
  | Δ, _, eqSymm (t₁ := t₁) (t₂ := t₂) d            =>
    String.Bussproof.unalyinfc d.toStr "=_\\mathsf{SYMM}" (String.turnstile Δ “!!t₂ = !!t₁”)
  | Δ, _, eqTrans (t₁ := t₁) (t₃ := t₃) c₁ c₂       =>
    String.Bussproof.binaryinfc c₁.toStr c₂.toStr "=_\\mathsf{TRANS}" (String.turnstile Δ “!!t₁ = !!t₃”)
  | Δ, _, rewriteEq (t₁ := t₁) (p := p) c₁ c₂       =>
    String.Bussproof.binaryinfc c₁.toStr c₂.toStr "=_\\mathsf{REW}" (String.turnstile Δ ([→ t₁].hom p))

instance : Repr (Δ ⟹[T] p) := ⟨fun b _ => b.toStr⟩

instance : ToString (Δ ⟹[T] p) := ⟨toStr⟩

end Repr

noncomputable def toProofArrow : {Δ : List (SyntacticFormula L)} → {p : SyntacticFormula L} →
    (Δ ⟹[T] p) → ProofArrow T Δ p
  | _, _, tauto d               => d
  | _, _, axm h                 => ProofArrow.byAxiom h
  | _, _, weakening' h d        => d.toProofArrow.weakening' h
  | _, _, rewrite f d           => d.toProofArrow.rewrite f
  | _, _, trans d₁ d₂           => d₁.toProofArrow.trans (d₂.toProofArrow)
  | _, _, assumption h          => ProofArrow.assumption h
  | _, _, contradiction _ d₁ d₂ => d₁.toProofArrow.contradiction _ d₂.toProofArrow
  | _, _, trivial               => ProofArrow.trivial
  | _, _, explode d             => d.toProofArrow.explode
  | _, _, intro d               => d.toProofArrow.intro
  | _, _, modusPonens d₁ d₂     => d₁.toProofArrow.modusPonens d₂.toProofArrow
  | _, _, split d₁ d₂           => d₁.toProofArrow.split d₂.toProofArrow
  | _, _, andLeft d             => d.toProofArrow.andLeft
  | _, _, andRight d            => d.toProofArrow.andRight
  | _, _, orLeft d              => d.toProofArrow.orLeft
  | _, _, orRight d             => d.toProofArrow.orRight
  | _, _, cases d₀ d₁ d₂        => d₀.toProofArrow.cases d₁.toProofArrow d₂.toProofArrow
  | _, _, generalize d          => d.toProofArrow.generalize
  | _, _, specialize t d        => d.toProofArrow.specialize t
  | _, _, useInstance t d       => d.toProofArrow.useInstance t
  | _, _, exCases d₀ d₁         => d₀.toProofArrow.exCases d₁.toProofArrow
  | _, _, eqRefl t              => ProofArrow.eqRefl t
  | _, _, eqSymm d              => d.toProofArrow.eqSymm
  | _, _, eqTrans d₁ d₂         => d₁.toProofArrow.eqTrans d₂.toProofArrow
  | _, _, rewriteEq d₀ d₁       => d₀.toProofArrow.rewriteEq d₁.toProofArrow

noncomputable def toProof {σ : Sentence L} :
    ([] ⟹[T] emb.hom σ) → T ⊢ σ := fun b => b.toProofArrow.toProof

def cast {Δ p p'} (h : p = p') (b : Δ ⟹[T] p) : Δ ⟹[T] p' := h ▸ b

def cast' {Δ Δ' p p'} (hΔ : Δ = Δ') (hp : p = p') (b : Δ ⟹[T] p) : Δ' ⟹[T] p' :=
  hΔ ▸ hp ▸ b

def axmOfEq (σ : Sentence L) (hp : emb.hom σ = p) (hσ : σ ∈ T) : Δ ⟹[T] p := by rw[←hp]; exact axm hσ

end Principia

noncomputable def Proof.toPrincipia {σ : Sentence L} :
    T ⊢ σ → ([] ⟹[T] emb.hom σ) := fun b => Principia.tauto (Proof.toProofArrow b)

end FirstOrder
