import Logic.Predicate.FirstOrder.Basic.Calculus
import Logic.Predicate.FirstOrder.Basic.Eq

namespace LO

namespace FirstOrder

variable {L : Language.{u}} [∀ k, DecidableEq (L.func k)] [∀ k, DecidableEq (L.rel k)]

variable {T : Theory L} {μ : Type v}

open Rew SubFormula DerivationCR DerivationCRWA

/-
def SequentList.fvarList (l : List $ SubFormula L μ n) : List μ :=
  l.bind SubFormula.fvarList

def fleshVar (C : List $ SyntacticFormula L) : ℕ := (SequentList.fvarList C).sup
-/

def ProofArrow (T : Theory L) (Δ : List (SyntacticFormula L)) (p : SyntacticFormula L) := T ⊢' insert p (Δ.map (~·)).toFinset

noncomputable def Proof.toProofArrow {σ : Sentence L} (b : T ⊢ σ) : ProofArrow T [] (Rew.embl σ) := b.cast (by simp)

namespace ProofArrow

variable {Δ Γ : List (SyntacticFormula L)}

def toDerivationCWA (b : ProofArrow T Δ p) : T ⊢' insert p (Δ.map (~·)).toFinset := b

def toProof {σ : Sentence L} (b : ProofArrow T [] (Rew.embl σ)) : T ⊢ σ := b.cast (by simp)

def cast {p p'} (b : ProofArrow T Δ p) (h : p = p') : ProofArrow T Δ p' :=
  h ▸ b

def cast' {Δ Δ' p p'} (b : ProofArrow T Δ p) (hΔ : Δ = Δ') (hp : p = p') : ProofArrow T Δ' p' :=
  hΔ ▸ hp ▸ b

protected def rewrite (f : ℕ → SyntacticTerm L) {p} (b : ProofArrow T Δ p) :
    ProofArrow T (Δ.map $ Rew.rewritel f) (Rew.rewritel f p) :=
  (b.toDerivationCWA.rewrite f).cast (by simp[Function.comp, List.toFinset_map, Finset.image_image])

protected def shift {p} (b : ProofArrow T Δ p) : ProofArrow T (Δ.map shiftl) (shiftl p) := b.rewrite _

def byAxiom {σ} (h : σ ∈ T) : ProofArrow T Δ (Rew.embl σ) :=
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
      b₂.toDerivationCWA.weakeningRight (by simpa[Finset.Insert.comm p] using Finset.subset_insert _ _)
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
  (b.toDerivationCWA.weakeningRight (by simpa[Finset.Insert.comm p] using Finset.subset_insert _ _)).or'

def orRight {p q} (b : ProofArrow T Δ q) : ProofArrow T Δ (p ⋎ q) :=
  (b.toDerivationCWA.weakeningRight (by simpa[Finset.Insert.comm q] using Finset.subset_insert _ _)).or'

def cases {p q r} (b₀ : ProofArrow T Δ (p ⋎ q)) (b₁ : ProofArrow T (p :: Δ) r) (b₂ : ProofArrow T (q :: Δ) r) : ProofArrow T Δ r :=
  let b₁' : T ⊢' insert (~p) (insert r (Δ.map (~·)).toFinset) := b₁.toDerivationCWA.cast (by simp[Finset.Insert.comm])
  let b₂' : T ⊢' insert (~q) (insert r (Δ.map (~·)).toFinset) := b₂.toDerivationCWA.cast (by simp[Finset.Insert.comm])
  let b₃ : T ⊢' insert (~(p ⋎ q)) (insert r (Δ.map (~·)).toFinset) := by simpa using b₁'.and' b₂'
  (b₀.toDerivationCWA.cCut b₃).cast (by simp)

def generalize {p} (b : ProofArrow T (Δ.map shiftl) (freel p)) : ProofArrow T Δ (∀' p) :=
  let b' : T ⊢' insert (freel p) (shifts (Δ.map (~·)).toFinset) :=
    b.toDerivationCWA.cast (by simp[shifts_eq_image, List.toFinset_map, Finset.image_image, Function.comp])
  b'.all'

def specialize (t) {p} (b : ProofArrow T Δ (∀' p)) : ProofArrow T Δ ([→ t].hom p) :=
  have b' : T ⊢' insert (∃' ~p) (insert ([→ t].hom p) (Δ.map (~·)).toFinset) :=
    DerivationCRWA.ex' (t := t) (DerivationCRWA.em (p := [→ t].hom p) (by simp) (by simp))
  (b.toDerivationCWA.cCut b').cast (by simp)

def specializes : {n : ℕ} → (v : Fin n → SyntacticTerm L) → {p : SyntacticSubFormula L n} →
    ProofArrow T Δ (univClosure p) → ProofArrow T Δ ((substs v).hom p)
  | 0,     v, p, b => b.cast (by simp)
  | n + 1, v, p, b =>
    let b : ProofArrow T Δ (∀' (substs (#(Fin.last 0) :> bShift ∘ v ∘ Fin.succ)).hom p) :=
      by simpa using specializes (v ∘ Fin.succ) b
    (specialize (v 0) b).cast (by simp[←Rew.hom_comp_app]; congr; ext x <;> simp[Rew.comp_app]; cases x using Fin.cases <;> simp)

def useInstance (t) {p} (b : ProofArrow T Δ ([→ t].hom p)) : ProofArrow T Δ (∃' p) := b.ex'

def exCases {p q} (b₀ : ProofArrow T Δ (∃' p))
  (b₁ : ProofArrow T (freel p :: Δ.map shiftl) (shiftl q)) : ProofArrow T Δ q :=
  let b₁₁ : T ⊢' (insert (freel $ ~p) $ shifts $ insert q (Δ.map (~·)).toFinset) :=
    b₁.toDerivationCWA.cast
      (by simp[shifts_eq_image, List.toFinset_map, Finset.Insert.comm (shiftl q), Finset.image_image, Function.comp])
  let b₁₂ : T ⊢' (insert (∀' ~p) $ insert q (Δ.map (~·)).toFinset) := b₁₁.all'
  (b₀.toDerivationCWA.cCut b₁₂).cast (by simp)

section Eq
variable [L.Eq] [EqTheory T]
open SubTerm SubFormula Theory Eq

def eqRefl (t : SyntacticTerm L) : ProofArrow T Δ (“ᵀ!t = ᵀ!t”) :=
  have b : ProofArrow T Δ (“∀ #0 = #0”) := (byAxiom (EqTheory.eq Theory.Eq.refl)).cast (by simp)
  (specialize t b).cast (by simp)

def eqSymm {t₁ t₂ : SyntacticTerm L} (b : ProofArrow T Δ “ᵀ!t₁ = ᵀ!t₂”) : ProofArrow T Δ “ᵀ!t₂ = ᵀ!t₁” :=
  have : ProofArrow T Δ “∀ ∀ (#1 = #0 → #0 = #1)” :=
    (byAxiom (EqTheory.eq Theory.Eq.symm)).cast (by simp)
  have : ProofArrow T Δ “ᵀ!t₁ = ᵀ!t₂ → ᵀ!t₂ = ᵀ!t₁” := (this.specializes ![t₂, t₁]).cast (by simp)
  this.modusPonens  b

def eqTrans {t₁ t₂ t₃ : SyntacticTerm L} (b₁ : ProofArrow T Δ “ᵀ!t₁ = ᵀ!t₂”) (b₂ : ProofArrow T Δ “ᵀ!t₂ = ᵀ!t₃”) :
    ProofArrow T Δ “ᵀ!t₁ = ᵀ!t₃” :=
  have : ProofArrow T Δ “∀ ∀ ∀ (#2 = #1 → #1 = #0 → #2 = #0)” :=
    (byAxiom (EqTheory.eq Theory.Eq.trans)).cast (by simp)
  have : ProofArrow T Δ “ᵀ!t₁ = ᵀ!t₂ → ᵀ!t₂ = ᵀ!t₃ → ᵀ!t₁ = ᵀ!t₃” := (this.specializes ![t₃, t₂, t₁]).cast (by simp)
  (this.modusPonens b₁).modusPonens b₂

def termExt : (t : SyntacticSubTerm L n) → (v₁ v₂ : Fin n → SyntacticTerm L) →
    ((i : Fin n) → ProofArrow T Δ “ᵀ!(v₁ i) = ᵀ!(v₂ i)”) → ProofArrow T Δ “ᵀ!(substs v₁ t) = ᵀ!(substs v₂ t)”
  | #x,       _,  _,  b => b x
  | &x,       _,  _,  _ => eqRefl &x
  | func f v, v₁, v₂, b =>
    have : ProofArrow T Δ
      “∀* ((⋀ i, ᵀ!(varSumInL i) = ᵀ!(varSumInR i)) →
      ᵀ!(func f varSumInL) = ᵀ!(func f varSumInR))” :=
    (byAxiom (EqTheory.eq (Theory.Eq.funcExt f))).cast (by simp[vecEq, Matrix.hom_conj']; rfl)
    have : ProofArrow T Δ
      “(⋀ i, ᵀ!(substs v₁ $ v i) = ᵀ!(substs v₂ $ v i)) → ᵀ!(func f fun i => substs v₁ (v i)) = ᵀ!(func f fun i => substs v₂ (v i))” :=
      by simpa [Matrix.hom_conj', Rew.func] using
        this.specializes (Matrix.vecAppend rfl (fun i => substs v₁ (v i)) (fun i => substs v₂ (v i)))
    this.modusPonens (splits fun i => termExt (v i) v₁ v₂ b)

private def negImply {p q : SyntacticFormula L} (b : ProofArrow T Δ (p ⟶ q)) : ProofArrow T Δ (~q ⟶ ~p) :=
  (b.trans $ intro $ absurd $ trans (p := q) (modusPonens (p := p) (assumption $ by simp) (assumption $ by simp)) $
    contradiction (p := q) ⊥ (assumption $ by simp) (assumption $ by simp))

private def relExtAux {n} {k} (r : L.rel k) (v : Fin k → SyntacticSubTerm L n) (v₁ v₂ : Fin n → SyntacticTerm L)
  (b : (i : Fin n) → ProofArrow T Δ “ᵀ!(v₁ i) = ᵀ!(v₂ i)”) : ProofArrow T Δ (substsl v₁ (rel r v) ⟶ substsl v₂ (rel r v)) :=
  have : ProofArrow T Δ
    “∀* ((⋀ i, ᵀ!(varSumInL i) = ᵀ!(varSumInR i)) → (!(rel r varSumInL) → !(rel r varSumInR)))” :=
  (byAxiom (EqTheory.eq (Theory.Eq.relExt r))).cast (by simp[vecEq, Matrix.hom_conj']; simp[Rew.rel])
  have : ProofArrow T Δ “(⋀ i, ᵀ!(substs v₁ (v i)) = ᵀ!(substs v₂ (v i))) →
    !(rel r fun i => substs v₁ (v i)) → !(rel r fun i => substs v₂ (v i))” := by
  { have := this.specializes (Matrix.vecAppend rfl (fun i => substs v₁ (v i)) (fun i => substs v₂ (v i)));
    simp[Matrix.hom_conj', Rew.func] at this; simpa[Rew.rel] using this }
  (this.modusPonens (splits fun i => termExt (v i) v₁ v₂ b)).cast (by simp[Rew.rel])

private lemma free_substs_eq_substs_shift {n'} (w : Fin n' → SyntacticSubTerm L (n + 1)) (p : SyntacticSubFormula L n') :
    freel (substsl w p) = substsl (fun i => Rew.free (w i)) (shiftl p) :=
  by simp[←Rew.hom_comp_app]; apply Rew.hom_ext'; ext x <;> simp[Rew.comp_app]

-- 不要だが計算を軽くするために`noncomputable`をつけている
noncomputable def formulaExtAux : {Δ : List (SyntacticFormula L)} → {n : ℕ} → (p : SyntacticSubFormula L n) → (v₁ v₂ : Fin n → SyntacticTerm L) →
    ((i : Fin n) → ProofArrow T Δ “ᵀ!(v₁ i) = ᵀ!(v₂ i)”) → ProofArrow T Δ (substsl v₁ p ⟶ substsl v₂ p)
  | Δ, _, ⊤,        v₁, v₂, _ => (intro $ assumption $ by simp)
  | Δ, _, ⊥,        v₁, v₂, _ => (intro $ assumption $ by simp)
  | Δ, _, rel r v,  v₁, v₂, b => relExtAux r v v₁ v₂ b
  | Δ, _, nrel r v, v₁, v₂, b => (relExtAux r v v₂ v₁ (fun i => eqSymm (b i))).negImply.cast (by simp[Rew.rel, Rew.nrel])
  | Δ, _, p ⋏ q,    v₁, v₂, b => by
    simp
    have bp : ProofArrow T Δ (substsl v₁ p ⟶ substsl v₂ p) := formulaExtAux p v₁ v₂ b
    have bq : ProofArrow T Δ (substsl v₁ q ⟶ substsl v₂ q) := formulaExtAux q v₁ v₂ b
    exact (intro $ split
      (modusPonens (bp.weakening $ by simp) (andLeft (q := substsl v₁ q) $ assumption $ by simp))
      (modusPonens (bq.weakening $ by simp) (andRight (p := substsl v₁ p) $ assumption $ by simp)))
  | Δ, _, p ⋎ q,    v₁, v₂, b => by
    simp
    have bp : ProofArrow T Δ (substsl v₁ p ⟶ substsl v₂ p) := formulaExtAux p v₁ v₂ b
    have bq : ProofArrow T Δ (substsl v₁ q ⟶ substsl v₂ q) := formulaExtAux q v₁ v₂ b
    exact (intro $ cases (p := substsl v₁ p) (q := substsl v₁ q) (assumption $ by simp)
      (orLeft $ modusPonens (bp.weakening $ List.subset_cons_of_subset _ $ by simp) $ assumption $ by simp)
      (orRight $ modusPonens (bq.weakening $ List.subset_cons_of_subset _ $ by simp) $ assumption $ by simp))
  | Δ, _, ∀' p,     v₁, v₂, b =>
    let Δ' := (∀' shiftl (substsl (#0 :> bShift ∘ v₁) p)) :: Δ.map shiftl
    let v₁' := fun i => Rew.free (#0 :> bShift ∘ v₁ $ i)
    let v₂' := fun i => Rew.free (#0 :> bShift ∘ v₂ $ i)
    have b' : (i : Fin _) → ProofArrow T Δ' (“ᵀ!(v₁' i) = ᵀ!(v₂' i)”) :=
      Fin.cases (eqRefl _) (fun i => ((b i).shift.weakening (by simp)).cast (by simp))
    have bp : ProofArrow T Δ' (substsl v₁' $ shiftl p) :=
      (specialize &0 (p := shiftl (substsl (#0 :> bShift ∘ v₁) p)) $ assumption $ by simp).cast
      (by simp[←free_substs_eq_substs_shift]; rw[←Rew.hom_comp_app [→ &0]]; simp[substs_mbar_zero_comp_shift_eq_free])
    have : ProofArrow T Δ' (substsl v₂' $ shiftl p) := modusPonens (formulaExtAux (shiftl p) v₁' v₂' b') bp
    have : ProofArrow T Δ (∀' substsl (#0 :> bShift ∘ v₁) p ⟶ ∀' substsl (#0 :> bShift ∘ v₂) p) :=
      (intro $ generalize $ this.cast' (by simp) (by simp[free_substs_eq_substs_shift]))
    this.cast (by simp; rfl)
  | Δ, _, ∃' p,     v₁, v₂, b =>
    let Δ' := substsl (fun i => Rew.free ((#0 :> bShift ∘ v₁) i)) (shiftl p) :: (∃' shiftl (substsl (#0 :> bShift ∘ v₁) p)) :: Δ.map shiftl
    let v₁' := fun i => free (#0 :> bShift ∘ v₁ $ i)
    let v₂' := fun i => free (#0 :> bShift ∘ v₂ $ i)
    have b' : (i : Fin _) → ProofArrow T Δ' (“ᵀ!(v₁' i) = ᵀ!(v₂' i)”) :=
      Fin.cases (eqRefl _) (fun i => ((b i).shift.weakening $ List.subset_cons_of_subset _ $ by simp).cast (by simp))
    have ih : ProofArrow T Δ' (substsl v₁' (shiftl p) ⟶ substsl v₂' (shiftl p)) := formulaExtAux (Δ := Δ') (shiftl p) v₁' v₂' b'
    have : ProofArrow T Δ' (∃' shiftl (substsl (#0 :> bShift ∘ v₂) p)) :=
      (useInstance &0 $ (ih.modusPonens (assumption $ by simp)).cast
      (by simp[←free_substs_eq_substs_shift]; rw[←Rew.hom_comp_app [→ &0]]; simp[substs_mbar_zero_comp_shift_eq_free]))
    have : ProofArrow T Δ (∃' substsl (#0 :> bShift ∘ v₁) p ⟶ ∃' substsl (#0 :> bShift ∘ v₂) p) :=
      (intro $ exCases (p := substsl (#0 :> bShift ∘ v₁) p) (assumption $ by simp) (this.cast' (by simp[free_substs_eq_substs_shift]) (by simp)))
    this.cast (by simp; rfl)
  termination_by formulaExtAux p _ _ _ => p.complexity

noncomputable def formulaExt (p : SyntacticSubFormula L n) (v₁ v₂ : Fin n → SyntacticTerm L) 
  (b : (i : Fin n) → ProofArrow T Δ “ᵀ!(v₁ i) = ᵀ!(v₂ i)”) (d : ProofArrow T Δ (substsl v₂ p)) :
    ProofArrow T Δ (substsl v₁ p) :=
  (formulaExtAux p v₂ v₁ (fun i => (b i).eqSymm)).modusPonens d

noncomputable def rewriteEq {p : SyntacticSubFormula L 1} {t₁ t₂ : SyntacticTerm L}
  (b : ProofArrow T Δ “ᵀ!t₁ = ᵀ!t₂”) (d : ProofArrow T Δ ([→ t₂].hom p)) :
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
    σ ∈ T → Principia Δ (embl σ)
  | weakening' {Δ Γ p q} :
    ~p :: Δ ⊆ ~q :: Γ → Principia Δ p → Principia Γ q
  | rewrite (f : ℕ → SyntacticTerm L) {p} :
    Principia Δ p → Principia (Δ.map $ rewritel f) (rewritel f p)    
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
    Principia (Δ.map shiftl) (freel p) → Principia Δ (∀' p)
  -- ∀ left
  | specialize (t) {Δ p} :
    Principia Δ (∀' p) → Principia Δ ([→ t].hom p)
  -- ∃ right
  | useInstance (t) {Δ p} :
    Principia Δ ([→ t].hom p) → Principia Δ (∃' p)
  -- ∃ left
  | exCases {Δ p q} :
    Principia Δ (∃' p) → Principia (freel p :: Δ.map shiftl) (shiftl q) → Principia Δ q
  -- =
  | eqRefl {Δ} (t) :
    Principia Δ “ᵀ!t = ᵀ!t”
  | eqSymm {Δ t₁ t₂} :
    Principia Δ “ᵀ!t₁ = ᵀ!t₂” → Principia Δ “ᵀ!t₂ = ᵀ!t₁”
  | eqTrans {Δ t₁ t₂ t₃} :
    Principia Δ “ᵀ!t₁ = ᵀ!t₂” → Principia Δ “ᵀ!t₂ = ᵀ!t₃” → Principia Δ “ᵀ!t₁ = ᵀ!t₃”
  | rewriteEq {Δ} {p : SyntacticSubFormula L 1} {t₁ t₂ : SyntacticTerm L} :
    Principia Δ “ᵀ!t₁ = ᵀ!t₂” → Principia Δ ([→ t₂].hom p) → Principia Δ ([→ t₁].hom p)

notation Δ:0 " ⟹[" T "] " p => Principia T Δ p

variable {T}

namespace Principia
open ProofArrow

def toStr : {Δ : List (SyntacticFormula L)} → {p : SyntacticFormula L} → (Δ ⟹[T] p) → String
  | _, _, tauto _               => "tauto"
  | _, _, axm _                 => "axiom"
  | _, _, weakening' _ d        => "weakening\n" ++ d.toStr
  | _, _, rewrite _ d           => "rewrite\n" ++ d.toStr
  | _, _, trans c₁ c₂           => "have: {\n" ++ c₁.toStr ++ "\n}\n" ++ c₂.toStr
  | _, _, assumption _          => "assumption"
  | _, _, contradiction _ c₁ c₂ => "contradiction: {\n" ++ c₁.toStr ++ "\n}\nand: {\n" ++ c₂.toStr ++ "\n}"
  | _, _, trivial               => "trivial"
  | _, _, explode c             => "explode" ++ c.toStr
  | _, _, intro c               => "intro\n" ++ c.toStr
  | _, _, modusPonens c₁ c₂     => "have: {\n" ++ c₁.toStr ++ "\n}\nand: {\n" ++ c₂.toStr ++ "\n}"
  | _, _, split c₁ c₂           => "∧ split: {\n" ++ c₁.toStr ++ "\n}\nand: {\n" ++ c₂.toStr ++ "\n}"
  | _, _, andLeft c             => "∧ left\n" ++ c.toStr
  | _, _, andRight c            => "∧ right\n" ++ c.toStr
  | _, _, orLeft c              => "∨ left\n" ++ c.toStr
  | _, _, orRight c             => "∨ right\n" ++ c.toStr
  | _, _, cases c₀ c₁ c₂        => "∨ split: {\n" ++ c₀.toStr ++ "\n}\nor left: {\n" ++ c₁.toStr ++ "\n}\nor right: {\n" ++ c₂.toStr ++ "\n}"
  | _, _, generalize c          => "generalize\n" ++ c.toStr
  | _, _, specialize _ c        => "specialize\n" ++ c.toStr
  | _, _, useInstance _ c       => "use\n" ++ c.toStr
  | _, _, exCases c₀ c₁         => "∃ cases: {\n" ++ c₀.toStr ++ "\n}\n" ++ c₁.toStr
  | _, _, eqRefl _              => "refl"
  | _, _, eqSymm c              => "symmetry" ++ c.toStr
  | _, _, eqTrans c₁ c₂         => "trans: {\n" ++ c₁.toStr ++ "\n}\n and: {\n" ++ c₂.toStr ++ "\n}"
  | _, _, rewriteEq c₁ c₂       => "rewrite: {\n" ++ c₁.toStr ++ "\n}\n" ++ c₂.toStr

instance : Repr (Δ ⟹[T] p) := ⟨fun b _ => b.toStr⟩

instance : ToString (Δ ⟹[T] p) := ⟨toStr⟩

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
    ([] ⟹[T] embl σ) → T ⊢ σ := fun b => b.toProofArrow.toProof

def cast {Δ p p'} (h : p = p') (b : Δ ⟹[T] p) : Δ ⟹[T] p' := h ▸ b 

def cast' {Δ Δ' p p'} (hΔ : Δ = Δ') (hp : p = p') (b : Δ ⟹[T] p) : Δ' ⟹[T] p' :=
  hΔ ▸ hp ▸ b

def axmOfEq (σ : Sentence L) (hp : embl σ = p) (hσ : σ ∈ T) : Δ ⟹[T] p := by rw[←hp]; exact axm hσ

end Principia

noncomputable def Proof.toPrincipia {σ : Sentence L} :
    T ⊢ σ → ([] ⟹[T] embl σ) := fun b => Principia.tauto (Proof.toProofArrow b)

end FirstOrder