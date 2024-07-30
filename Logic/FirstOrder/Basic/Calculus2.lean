import Logic.FirstOrder.Basic.Calculus

/-!

# Derivation2

Different characterizations of proof.

-/

namespace LO.FirstOrder

variable {L : Language} [(k : ℕ) → DecidableEq (L.Func k)] [(k : ℕ) → DecidableEq (L.Rel k)]

variable [L.ConstantInhabited]

open Semiformula

def SyntacticTheory.close (T : SyntacticTheory L) : Theory L := Semiformula.close '' T

instance : Coe (Theory L) (SyntacticTheory L) := ⟨fun T ↦ Rew.embs.hom '' T⟩

@[simp] lemma Theory.open_close (T : Theory L) : SyntacticTheory.close (T : SyntacticTheory L) = T := by
  ext σ; simp [SyntacticTheory.close]

inductive Derivation2 (T : SyntacticTheory L) : Sequent L → Type _
| closed (Γ p) : Derivation2 T (p :: ~p :: Γ)
| root (Γ p)   : p ∈ T → Derivation2 T (p :: Γ)
| verum (Γ)    : Derivation2 T (⊤ :: Γ)
| or {Γ p q}   : Derivation2 T (p :: q :: Γ) → Derivation2 T (p ⋎ q :: Γ)
| and {Γ p q}  : Derivation2 T (p :: Γ) → Derivation2 T (q :: Γ) → Derivation2 T (p ⋏ q :: Γ)
| all {Γ p}    : Derivation2 T (Rew.free.hom p :: Γ⁺) → Derivation2 T ((∀' p) :: Γ)
| ex {Γ p} (t) : Derivation2 T (p/[t] :: Γ) → Derivation2 T ((∃' p) :: Γ)
| wk {Γ Δ}     : Derivation2 T Γ → Γ ⊆ Δ → Derivation2 T Δ
| cut {Γ p}    : Derivation2 T (p :: Γ) → Derivation2 T (~p :: Γ) → Derivation2 T Γ

scoped infix: 45 " ⊢₂ " => Derivation2

abbrev Derivable2 (T : SyntacticTheory L) (Γ : Sequent L) : Prop := Nonempty (T ⊢₂ Γ)

scoped infix: 45 " ⊢₂! " => Derivable2

abbrev Derivation2SingleConseq (T : SyntacticTheory L) (p : SyntacticFormula L) : Type _ := T ⊢₂ [p]

abbrev Derivable2SingleConseq (T : SyntacticTheory L) (p : SyntacticFormula L) : Prop := Nonempty (T ⊢₂ [p])

scoped infix: 45 " ⊢₂. " => Derivation2SingleConseq

scoped infix: 45 " ⊢₂.! " => Derivable2SingleConseq

def Derivation.toDerivation2 : {Γ : Sequent L} → ⊢¹ Γ → T ⊢₂ Γ
  | _, Derivation.axL Δ r v => Derivation2.closed Δ (Semiformula.rel r v)
  | _, Derivation.verum Δ   => Derivation2.verum Δ
  | _, Derivation.and dp dq => Derivation2.and (toDerivation2 dp) (toDerivation2 dq)
  | _, Derivation.or dpq    => Derivation2.or (toDerivation2 dpq)
  | _, Derivation.all dp    => Derivation2.all (toDerivation2 dp)
  | _, Derivation.ex t dp   => Derivation2.ex t (toDerivation2 dp)
  | _, Derivation.wk d h    => Derivation2.wk (toDerivation2 d) h
  | _, Derivation.cut d₁ d₂ => Derivation2.cut (toDerivation2 d₁) (toDerivation2 d₂)

lemma Derivable.toDerivable2 {Γ : Sequent L} (h : ⊢¹! Γ) : T ⊢₂! Γ := ⟨Derivation.toDerivation2 <| Classical.choice h⟩

namespace Derivable2

lemma wk! {Γ Δ : Sequent L} (d : T ⊢₂! Γ) (h : Γ ⊆ Δ) : T ⊢₂! Δ := ⟨d.some.wk h⟩

end Derivable2

namespace Derivation2

variable {T : SyntacticTheory L}

lemma toDerivable2 {Γ : Sequent L} (d : T ⊢₂ Γ) : T ⊢₂! Γ := ⟨d⟩

def closed' (Δ p) (h : p ∈ Δ := by simp) (hn : ~p ∈ Δ := by simp) : T ⊢₂ Δ := (closed Δ p).wk (by simp[h, hn])

def verum' (h : ⊤ ∈ Δ) : T ⊢₂ Δ := (verum Δ).wk (by simp[h])

def root' (p) (hT : p ∈ T) (h : p ∈ Δ) : T ⊢₂ Δ := (root Δ p hT).wk (by simp[h])

def and' {p q} (h : p ⋏ q ∈ Δ) (dp : T ⊢₂ p :: Δ) (dq : T ⊢₂ q :: Δ) : T ⊢₂ Δ := (and dp dq).wk (by simp[h])

def or' {p q} (h : p ⋎ q ∈ Δ) (d : T ⊢₂ p :: q :: Δ) : T ⊢₂ Δ := (or d).wk (by simp[h])

def axL' (p) (h : p ∈ Δ) (hn : ~p ∈ Δ) : T ⊢₂ Δ := (closed Δ p).wk (by simp[h, hn])

def all' {p} (h : ∀' p ∈ Δ) (d : T ⊢₂ Rew.free.hom p :: Δ⁺) : T ⊢₂ Δ := d.all.wk (by simp [h])

def ex' {p} (h : ∃' p ∈ Δ) (t) (d : T ⊢₂ p/[t] :: Δ) : T ⊢₂ Δ := (d.ex t).wk (by simp [h])

def cast (d : T ⊢₂ Γ) (h : Γ = Δ) : T ⊢₂ Δ := h ▸ d

def allClosureFixitr {p : SyntacticFormula L} (dp : T ⊢₂. p) : (m : ℕ) → T ⊢₂. ∀* (Rew.fixitr 0 m).hom p
  | 0     => by simpa
  | m + 1 => by
    simp [Semiformula.allClosure_fixitr]
    apply all; simpa using allClosureFixitr dp m

def close {p : SyntacticFormula L} (dp : T ⊢₂. p) : T ⊢₂. Rew.embs.hom p.close := by
  simpa [Semiformula.embs_close] using allClosureFixitr dp p.upper

def cutList : (Δ : Sequent L) → T ⊢₂ Δ ++ Γ → (∀ q ∈ Δ, T ⊢₂ ~q :: Γ) → T ⊢₂ Γ
  | [],     d, _  => d
  | p :: Δ, d, ds =>
    let d : T ⊢₂ Δ ++ p :: Γ := d.wk (by intro x; simp; tauto)
    let dp : T ⊢₂ p :: Γ := cutList Δ d (fun q hq ↦ (ds q (by simp [hq])).wk (by intro x; simp; tauto))
    dp.cut (ds p (by simp))

lemma cutList! (Δ : Sequent L) (h : T ⊢₂! Δ ++ Γ) (H : ∀ q ∈ Δ, T ⊢₂! ~q :: Γ) : T ⊢₂! Γ :=
  ⟨cutList Δ h.some (fun q hq ↦ (H q hq).some)⟩

def specialize {p : SyntacticSemiformula L 1} (d : T ⊢₂ (∀' p) :: Γ) (t) : T ⊢₂ p/[t] :: Γ :=
  have : T ⊢₂ ~p/[t] :: p/[t] :: Γ := closed' _ (p/[t])
  have dn : T ⊢₂ ~(∀' p) :: p/[t] :: Γ := by simpa using ex t (by simpa using this)
  have d  : T ⊢₂ (∀' p) :: p/[t] :: Γ := wk d (List.cons_subset_cons _ <| by simp)
  d.cut dn

def specializeVec : {n : ℕ} → {p : SyntacticSemiformula L n} →
    T ⊢₂ (∀* p) :: Γ → (v : Fin n → SyntacticTerm L) → T ⊢₂ (Rew.substs v |>.hom p) :: Γ
  | 0, p, d, _ => by simpa using d
  | n + 1, p, d, v =>
    have d : T ⊢₂ (∀* ∀' p) :: Γ := d
    have : T ⊢₂ (∀' (Rew.substs (v ·.succ)).q.hom p) :: Γ := by simpa using specializeVec d (v ·.succ)
    (this.specialize (v 0)).cast (by
      simp [←Rew.hom_comp_app]; congr 2
      ext x
      · cases x using Fin.cases <;> simp [Rew.comp_app]
      · simp [Rew.comp_app])

def rew1 {p : SyntacticFormula L} (d : T ⊢₂. p) (f) : T ⊢₂. (Rew.rewrite f).hom p := by
  have : T ⊢₂. ∀* (Rew.hom (Rew.fixitr 0 (upper p))) p := by simpa [Semiformula.embs_close] using d.close
  simpa using this.specializeVec (fun x ↦ f x)

def rewrite : {Γ : Sequent L} → T ⊢₂ Γ → (f : ℕ → SyntacticTerm L) → T ⊢₂ Γ.map (Rew.rewrite f).hom
  | _, closed Γ p,                  f => closed' _ (Rew.rewrite f |>.hom p)
  | _, root Γ p hp,                 f =>
    have : T ⊢₂. p := root _ _ hp
    (this.rew1 f).wk (by simp)
  | _, verum Γ,                     f => verum' (by simp)
  | _, and (p := p) (q := q) dp dq, f =>
    and' (p := Rew.rewrite f |>.hom p) (q := Rew.rewrite f |>.hom q) (by simp)
      ((dp.rewrite f).wk <| by simp; apply List.subset_cons_of_subset; simp)
      ((dq.rewrite f).wk <| by simp; apply List.subset_cons_of_subset; simp)
  | _, or (p := p) (q := q) d,      f =>
    or' (p := Rew.rewrite f |>.hom p) (q := Rew.rewrite f |>.hom q) (by simp)
      ((d.rewrite f).wk <| by simp; apply List.subset_cons_of_subset; apply List.subset_cons_of_subset; simp)
  | _, all (Γ := Δ) (p := p) d,     f =>
    have : T ⊢₂ ((Rew.free.hom p) :: Δ⁺).map (Rew.rewrite (&0 :>ₙ fun x ↦ Rew.shift (f x))).hom :=
      d.rewrite (&0 :>ₙ fun x ↦ Rew.shift (f x))
    have : T ⊢₂ (∀' (Rew.rewrite (Rew.bShift ∘ f)).hom p) :: Δ.map ((Rew.rewrite f).hom) :=
      all (.cast this (by simp [free_rewrite_eq, shifts, shift_rewrite_eq, Finset.image_image, Function.comp]))
    .cast this (by simp[Rew.q_rewrite])
  | _, ex (Γ := Δ) (p := p) t d,    f =>
    have : T ⊢₂ (p/[t] :: Δ).map ((Rew.rewrite f).hom) := rewrite d f
    have : T ⊢₂ (∃' (Rew.rewrite (Rew.bShift ∘ f)).hom p) :: Δ.map ((Rew.rewrite f).hom) :=
      ex (Rew.rewrite f t) (.cast this (by simp[rewrite_subst_eq]))
    .cast this (by simp[Rew.q_rewrite])
  | _, wk d h,                      f => (d.rewrite f).wk (List.map_subset _ h)
  | _, cut (Γ := Δ) (p := p) dp dn, f =>
    have dΔ : T ⊢₂ ((Rew.rewrite f).hom p) :: Δ.map ((Rew.rewrite f).hom) := .cast (rewrite dp f) (by simp)
    have dΓ : T ⊢₂ (~(Rew.rewrite f).hom p) :: Δ.map ((Rew.rewrite f).hom) := .cast (rewrite dn f) (by simp)
    .cast (cut dΔ dΓ) (by simp)

def shift (d : T ⊢₂ Γ) : T ⊢₂ Γ⁺ := .cast (d.rewrite (fun x ↦ &(x + 1)))
  (by simp [shifts, List.map_inj_left]; intro x _; rfl)

end Derivation2

open Derivation2

section

variable {T : SyntacticTheory L}

def Provable.toDerivation2 {σ} (b : T.close ⊢! σ) : T ⊢₂.! Rew.embs.hom σ := by
  let ⟨Γ, hΓ, d⟩ := Gentzen.provable_iff.mp (provable_iff.mp b)
  let b : T ⊢₂! List.map (~·) Γ ++ [Rew.emb.hom σ] := Derivable.toDerivable2 d
  refine cutList! _ b (fun p hp ↦ by
    have : ∃ x ∈ Γ, ~x = p := by simpa using hp
    rcases this with ⟨p, Hp, rfl⟩
    have : ∃ x ∈ T, Rew.embs.hom (x.close) = p := by
      simpa [SyntacticTheory.close] using hΓ p Hp
    rcases this with ⟨p, hpT, rfl⟩
    simpa using (Derivation2.root [] _ hpT).close.toDerivable2.wk! (by simp))

def Derivation2.toDisjconseqTr : {Γ : Sequent L} → T ⊢₂ Γ → T.close ⊢'' Γ
  | _, closed Δ p         => Gentzen.Disjconseq.em p (by simp) (by simp)
  | _, root Γ (p := p) hp =>
    have : T.close ⊢'' [∀* (Rew.fixitr 0 p.upper).hom p] :=
      Gentzen.Disjconseq.byAxm _ (by simp [SyntacticTheory.close]; exact ⟨p, hp, by simp [Semiformula.embs_close]⟩)
    have : T.close ⊢'' [p] := by simpa using System.specializeVec (fun x ↦ &x) this
    Gentzen.Disjconseq.wk this (by simp)
  | _, verum Γ            => Gentzen.Disjconseq.verum Γ
  | _, and dp dq          => Gentzen.Disjconseq.and (toDisjconseqTr dp) (toDisjconseqTr dq)
  | _, or dpq             => Gentzen.Disjconseq.or (toDisjconseqTr dpq)
  | _, all dp             => System.generalize (toDisjconseqTr dp)
  | _, ex t dp            => System.witness t (toDisjconseqTr dp)
  | _, wk d h             => Gentzen.Disjconseq.wk (toDisjconseqTr d) h
  | _, cut dp dn          => Gentzen.Disjconseq.cut (toDisjconseqTr dp) (toDisjconseqTr dn)

def provable_iff_derivable2 {σ} : T.close ⊢! σ ↔ T ⊢₂.! Rew.embs.hom σ :=
  ⟨Provable.toDerivation2, fun b ↦ provable_iff.mpr ⟨b.some.toDisjconseqTr⟩⟩

def provable_iff_derivable2' {T : Theory L} {σ} : T ⊢! σ ↔ T ⊢₂.! Rew.embs.hom σ := by simp [←provable_iff_derivable2]

end

section

variable {T : Theory L}



end
