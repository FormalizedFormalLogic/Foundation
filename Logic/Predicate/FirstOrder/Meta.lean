import Logic.Predicate.FirstOrder.Calculus
import Logic.Predicate.Meta
open Qq Lean Elab Meta Tactic

universe u v

namespace FirstOrder

namespace SubFormula

namespace Meta

section lemmata
variable {L L' : Language} {μ μ' : Type v} {n n' : ℕ} {f : SubFormula L μ n →L SubFormula L' μ' n'}

lemma hom_and_eq_of_eq {p q : SubFormula L μ n} {p' q'} (hp : f p = p') (hq : f q = q') :
    f (p ⋏ q) = p' ⋏ q' := by simp[←hp, ←hq]

lemma hom_or_eq_of_eq {p q : SubFormula L μ n} {p' q'} (hp : f p = p') (hq : f q = q') :
    f (p ⋎ q) = p' ⋎ q' := by simp[←hp, ←hq]

lemma hom_neg_eq_of_eq {p : SubFormula L μ n} {p'} (h : f p = p') :
    f (~p) = ~p' := by simp[←h]

lemma free_rel₀ (r : L.rel 0) :
    free (rel r ![] : SyntacticSubFormula L (n + 1)) = rel r ![] := by simp[free_rel]

lemma free_rel₁ (r : L.rel 1) {t : SyntacticSubTerm L (n + 1)} {t'} (h : t.free = t') :
    free (rel r ![t]) = rel r ![t'] := by
  simp[←h, free_rel]; funext i; cases' i using Fin.cases with i <;> simp

lemma free_rel₂ (r : L.rel 2) {t₁ t₂ : SyntacticSubTerm L (n + 1)} {t₁' t₂'}
  (h₁ : t₁.free = t₁') (h₂ : t₂.free = t₂') :
    free (rel r ![t₁, t₂]) = rel r ![t₁', t₂'] := by
  simp[←h₁, ←h₂, free_rel]; funext i; cases' i using Fin.cases with i <;> simp

lemma free_nrel₀ (r : L.rel 0) :
    free (nrel r ![] : SyntacticSubFormula L (n + 1)) = nrel r ![] := by simp[free_nrel]

lemma free_nrel₁ (r : L.rel 1) {t : SyntacticSubTerm L (n + 1)} {t'} (h : t.free = t') :
    free (nrel r ![t]) = nrel r ![t'] := by
  simp[←h, free_nrel]; funext i; cases' i using Fin.cases with i <;> simp

lemma free_nrel₂ (r : L.rel 2) {t₁ t₂ : SyntacticSubTerm L (n + 1)} {t₁' t₂'}
  (h₁ : t₁.free = t₁') (h₂ : t₂.free = t₂') :
    free (nrel r ![t₁, t₂]) = nrel r ![t₁', t₂'] := by
  simp[←h₁, ←h₂, free_nrel]; funext i; cases' i using Fin.cases with i <;> simp

lemma free_all_eq_of_eq {p : SyntacticSubFormula L (n + 1 + 1)} {p'} (h : free p = p') :
    free (∀' p) = ∀' p' := by simp[←h]

lemma free_ex_eq_of_eq {p : SyntacticSubFormula L (n + 1 + 1)} {p'} (h : free p = p') :
    free (∃' p) = ∃' p' := by simp[←h]

lemma subst_rel₀ {s : SubTerm L μ n} (r : L.rel 0) :
    subst s (rel r ![] : SubFormula L μ (n + 1)) = rel r ![] := by simp[subst_rel]

lemma subst_rel₁ {s : SubTerm L μ n} (r : L.rel 1) {t : SubTerm L μ (n + 1)} {t'} (h : SubTerm.subst s t = t') :
    subst s (rel r ![t]) = rel r ![t'] := by
  simp[←h, subst_rel]; funext i; cases' i using Fin.cases with i <;> simp

lemma subst_rel₂ {s : SubTerm L μ n} (r : L.rel 2) {t₁ t₂ : SubTerm L μ (n + 1)} {t₁' t₂'}
  (h₁ : SubTerm.subst s t₁ = t₁') (h₂ : SubTerm.subst s t₂ = t₂') :
    subst s (rel r ![t₁, t₂]) = rel r ![t₁', t₂'] := by
  simp[←h₁, ←h₂, subst_rel]; funext i; cases' i using Fin.cases with i <;> simp

lemma subst_nrel₀ {s : SubTerm L μ n} (r : L.rel 0) :
    subst s (nrel r ![] : SubFormula L μ (n + 1)) = nrel r ![] := by simp[subst_nrel]

lemma subst_nrel₁ {s : SubTerm L μ n} (r : L.rel 1) {t : SubTerm L μ (n + 1)} {t'} (h : SubTerm.subst s t = t') :
    subst s (nrel r ![t]) = nrel r ![t'] := by
  simp[←h, subst_nrel]; funext i; cases' i using Fin.cases with i <;> simp

lemma subst_nrel₂ {s : SubTerm L μ n} (r : L.rel 2) {t₁ t₂ : SubTerm L μ (n + 1)} {t₁' t₂'}
  (h₁ : SubTerm.subst s t₁ = t₁') (h₂ : SubTerm.subst s t₂ = t₂') :
    subst s (nrel r ![t₁, t₂]) = nrel r ![t₁', t₂'] := by
  simp[←h₁, ←h₂, subst_nrel]; funext i; cases' i using Fin.cases with i <;> simp

lemma subst_all_eq_of_eq {s : SubTerm L μ n} {s'} {p : SubFormula L μ (n + 1 + 1)} {p'}
  (hs : SubTerm.bShift s = s') (hp : subst s' p = p') :
    subst s (∀' p) = ∀' p' := by simp[←hs, ←hp]

lemma subst_ex_eq_of_eq {s : SubTerm L μ n} {s'} {p : SubFormula L μ (n + 1 + 1)} {p'}
  (hs : SubTerm.bShift s = s') (hp : subst s' p = p') :
    subst s (∃' p) = ∃' p' := by simp[←hs, ←hp]

lemma shift_rel₀ (r : L.rel 0) :
    shift (rel r ![] : SyntacticSubFormula L n) = rel r ![] := by simp[shift_rel]

lemma shift_rel₁ (r : L.rel 1) {t : SyntacticSubTerm L n} {t'} (h : t.shift = t') :
    shift (rel r ![t]) = rel r ![t'] := by
  simp[←h, shift_rel]; funext i; cases' i using Fin.cases with i <;> simp

lemma shift_rel₂ (r : L.rel 2) {t₁ t₂ : SyntacticSubTerm L n} {t₁' t₂'}
  (h₁ : t₁.shift = t₁') (h₂ : t₂.shift = t₂') :
    shift (rel r ![t₁, t₂]) = rel r ![t₁', t₂'] := by
  simp[←h₁, ←h₂, shift_rel]; funext i; cases' i using Fin.cases with i <;> simp

lemma shift_nrel₀ (r : L.rel 0) :
    shift (nrel r ![] : SyntacticSubFormula L n) = nrel r ![] := by simp[shift_nrel]

lemma shift_nrel₁ (r : L.rel 1) {t : SyntacticSubTerm L n} {t'} (h : t.shift = t') :
    shift (nrel r ![t]) = nrel r ![t'] := by
  simp[←h, shift_nrel]; funext i; cases' i using Fin.cases with i <;> simp

lemma shift_nrel₂ (r : L.rel 2) {t₁ t₂ : SyntacticSubTerm L n} {t₁' t₂'}
  (h₁ : t₁.shift = t₁') (h₂ : t₂.shift = t₂') :
    shift (nrel r ![t₁, t₂]) = nrel r ![t₁', t₂'] := by
  simp[←h₁, ←h₂, shift_nrel]; funext i; cases' i using Fin.cases with i <;> simp

lemma shift_all_eq_of_eq {p : SyntacticSubFormula L (n + 1)} {p'} (h : shift p = p') :
    shift (∀' p) = ∀' p' := by simp[←h]

lemma shift_ex_eq_of_eq {p : SyntacticSubFormula L (n + 1)} {p'} (h : shift p = p') :
    shift (∃' p) = ∃' p' := by simp[←h]

lemma shift_subst_eq_of_eq {s : SyntacticSubTerm L n} {p : SyntacticSubFormula L (n + 1)} {s' p'}
  (hs : s.shift = s') (hp : shift p = p') :
    shift (subst s p) = subst s' p' := by simp[←hs, ←hp, shift_subst]

lemma neg_and_eq_of_eq {p q : SubFormula L μ n} {p' q'} (hp : ~p = p') (hq : ~q = q') :
    ~(p ⋏ q) = p' ⋎ q' := by simp[←hp, ←hq]

lemma neg_or_eq_of_eq {p q : SubFormula L μ n} {p' q'} (hp : ~p = p') (hq : ~q = q') :
    ~(p ⋎ q) = p' ⋏ q' := by simp[←hp, ←hq]

lemma neg_rel {k} (r : L.rel k) (v : Fin k → SubTerm L μ n) :
    ~(rel r v) = nrel r v := rfl

lemma neg_nrel {k} (r : L.rel k) (v : Fin k → SubTerm L μ n) :
    ~(nrel r v) = rel r v := rfl

lemma neg_all_eq_of_eq {p : SyntacticSubFormula L (n + 1)} {p'} (h : ~p = p') :
    ~(∀' p) = ∃' p' := by simp[←h]

lemma neg_ex_eq_of_eq {p : SyntacticSubFormula L (n + 1)} {p'} (h : ~p = p') :
    ~(∃' p) = ∀' p' := by simp[←h]

lemma rel₁_congr {r : L.rel 1} {t t' : SubTerm L μ n} (h : t = t') :
    rel r ![t] = rel r ![t'] := congr_arg _ (by simp[h])

lemma rel₂_congr {r : L.rel 2} {t₁ t₂ t₁' t₂' : SubTerm L μ n} (h₁ : t₁ = t₁') (h₂ : t₂ = t₂') :
    rel r ![t₁, t₂] = rel r ![t₁', t₂'] := congr_arg _ (by simp[h₁, h₂])

lemma nrel₁_congr {r : L.rel 1} {t t' : SubTerm L μ n} (h : t = t') :
    nrel r ![t] = nrel r ![t'] := congr_arg _ (by simp[h])

lemma nrel₂_congr {r : L.rel 2} {t₁ t₂ t₁' t₂' : SubTerm L μ n} (h₁ : t₁ = t₁') (h₂ : t₂ = t₂') :
    nrel r ![t₁, t₂] = nrel r ![t₁', t₂'] := congr_arg _ (by simp[h₁, h₂])

lemma and_congr {p q p' q': SyntacticSubFormula L n} (hp : p = p') (hq : q = q') :
    p ⋏ q = p' ⋏ q' := congr_arg₂ _ hp hq

lemma or_congr {p q p' q': SyntacticSubFormula L n} (hp : p = p') (hq : q = q') :
    p ⋎ q = p' ⋎ q' := congr_arg₂ _ hp hq

lemma all_congr {p p' : SyntacticSubFormula L (n + 1)} (hp : p = p') :
    ∀' p = ∀' p' := congr_arg _ hp

lemma ex_congr {p p' : SyntacticSubFormula L (n + 1)} (hp : p = p') :
    ∃' p = ∃' p' := congr_arg _ hp

lemma neg_congr_eq {p p' : SubFormula L μ n} {q} (e : p = p') (h : ~p' = q) :
  ~p = q := Eq.trans (congr_arg _ e) h

lemma imp_eq_of_eq {p q p' q' p'' : SubFormula L μ n} (hp : p = p') (hq : q = q') (hp' : ~p' = p'') :
    p ⟶ q = p'' ⋎ q' := by simp[←hp, ←hq, ←hp', imp_eq]

lemma iff_eq_of_eq {p q p' q' p'' q'' : SubFormula L μ n} (hp : p = p') (hq : q = q') (hp' : ~p' = p'') (hq' : ~q' = q'') :
    (p ⟷ q) = (p'' ⋎ q') ⋏ (q'' ⋎ p') := by simp[←hp, ←hq, ←hp', ←hq', iff_eq]

lemma free_congr_eq {p p' : SyntacticSubFormula L (n + 1)} {q} (e : p = p') (h : free p' = q) :
  free p = q := Eq.trans (congr_arg _ e) h

lemma subst_congr_eq {s s' : SubTerm L μ n} {p p' q} (es : s = s') (ep : p = p') (h : subst s' p' = q) :
  subst s p = q := Eq.trans (congr_arg₂ _ (by simp[es]) ep) h

lemma shift_congr_eq {p p' : SyntacticSubFormula L n} {q} (e : p = p') (h : shift p' = q) :
  shift p = q := Eq.trans (congr_arg _ e) h

end lemmata

partial def resultFree {L : Q(Language.{u})} {n : Q(ℕ)} : (p : Q(SyntacticSubFormula $L ($n + 1))) →
    MetaM ((res : Q(SyntacticSubFormula $L $n)) × Q(free $p = $res))
  | ~q(⊤)                   => pure ⟨q(⊤), q(rfl)⟩
  | ~q(⊥)                   => pure ⟨q(⊥), q(rfl)⟩
  | ~q($p ⋏ $q)             => do
    let ⟨pn, pe⟩ ← resultFree p
    let ⟨qn, qe⟩ ← resultFree q
    return ⟨q($pn ⋏ $qn), q(hom_and_eq_of_eq $pe $qe)⟩
  | ~q($p ⋎ $q)             => do
    let ⟨pn, pe⟩ ← resultFree p
    let ⟨qn, qe⟩ ← resultFree q
    return ⟨q($pn ⋎ $qn), q(hom_or_eq_of_eq $pe $qe)⟩
  | ~q(~$p)             => do
    let ⟨pn, pe⟩ ← resultFree p
    return ⟨q(~$pn), q(hom_neg_eq_of_eq $pe)⟩
  | ~q(∀' $p)               => do
    let ⟨pn, e⟩ ← resultFree p
    return ⟨q(∀' $pn), q(free_all_eq_of_eq $e)⟩
  | ~q(∃' $p)               => do
    let ⟨pn, e⟩ ← resultFree p
    return ⟨q(∃' $pn), q(free_ex_eq_of_eq $e)⟩
  | ~q(rel $r ![])          => pure ⟨q(rel $r ![]), q(free_rel₀ $r)⟩
  | ~q(rel $r ![$t])        => do
    let ⟨tn, e⟩ ← SubTerm.Meta.resultFree (L := L) (n := n) t
    return ⟨q(rel $r ![$tn]), q(free_rel₁ $r $e)⟩
  | ~q(rel $r ![$t₁, $t₂])  => do
    let ⟨tn₁, e₁⟩ ← SubTerm.Meta.resultFree (L := L) (n := n) t₁
    let ⟨tn₂, e₂⟩ ← SubTerm.Meta.resultFree (L := L) (n := n) t₂
    return ⟨q(rel $r ![$tn₁, $tn₂]), q(free_rel₂ $r $e₁ $e₂)⟩
  | ~q(nrel $r ![])         => pure ⟨q(nrel $r ![]), q(free_nrel₀ $r)⟩
  | ~q(nrel $r ![$t])       => do
    let ⟨tn, e⟩ ← SubTerm.Meta.resultFree (L := L) (n := n) t
    return ⟨q(nrel $r ![$tn]), q(free_nrel₁ $r $e)⟩
  | ~q(nrel $r ![$t₁, $t₂]) => do
    let ⟨tn₁, e₁⟩ ← SubTerm.Meta.resultFree (L := L) (n := n) t₁
    let ⟨tn₂, e₂⟩ ← SubTerm.Meta.resultFree (L := L) (n := n) t₂
    return ⟨q(nrel $r ![$tn₁, $tn₂]), q(free_nrel₂ $r $e₁ $e₂)⟩
  | ~q($p)                  => pure ⟨q(free $p), q(rfl)⟩

partial def resultSubst {L : Q(Language.{u})} {n : Q(ℕ)} (s : Q(SyntacticSubTerm $L $n)) :
    (p : Q(SyntacticSubFormula $L ($n + 1))) → MetaM ((res : Q(SyntacticSubFormula $L $n)) × Q(subst $s $p = $res))
  | ~q(⊤)                   => pure ⟨q(⊤), q(rfl)⟩
  | ~q(⊥)                   => pure ⟨q(⊥), q(rfl)⟩
  | ~q($p ⋏ $q)             => do
    let ⟨pn, pe⟩ ← resultSubst s p
    let ⟨qn, qe⟩ ← resultSubst s q
    return ⟨q($pn ⋏ $qn), q(hom_and_eq_of_eq $pe $qe)⟩
  | ~q($p ⋎ $q)             => do
    let ⟨pn, pe⟩ ← resultSubst s p
    let ⟨qn, qe⟩ ← resultSubst s q
    return ⟨q($pn ⋎ $qn), q(hom_or_eq_of_eq $pe $qe)⟩
  | ~q(~$p)             => do
    let ⟨pn, pe⟩ ← resultSubst s p
    return ⟨q(~$pn), q(hom_neg_eq_of_eq $pe)⟩
  | ~q(∀' $p)               => do
    let ⟨sn, se⟩ ← SubTerm.Meta.resultBShift s
    let ⟨pn, pe⟩ ← resultSubst sn p
    return ⟨q(∀' $pn), q(subst_all_eq_of_eq $se $pe)⟩
  | ~q(∃' $p)               => do
    let ⟨sn, se⟩ ← SubTerm.Meta.resultBShift s
    let ⟨pn, pe⟩ ← resultSubst sn p
    return ⟨q(∃' $pn), q(subst_ex_eq_of_eq $se $pe)⟩
  | ~q(rel $r ![])          => pure ⟨q(rel $r ![]), q(subst_rel₀ $r)⟩
  | ~q(rel $r ![$t])        => do
    let ⟨tn, e⟩ ← SubTerm.Meta.resultSubst (L := L) (n := n) s t
    return ⟨q(rel $r ![$tn]), q(subst_rel₁ $r $e)⟩
  | ~q(rel $r ![$t₁, $t₂])  => do
    let ⟨tn₁, e₁⟩ ← SubTerm.Meta.resultSubst (L := L) (n := n) s t₁
    let ⟨tn₂, e₂⟩ ← SubTerm.Meta.resultSubst (L := L) (n := n) s t₂
    return ⟨q(rel $r ![$tn₁, $tn₂]), q(subst_rel₂ $r $e₁ $e₂)⟩
  | ~q(nrel $r ![])         => pure ⟨q(nrel $r ![]), q(subst_nrel₀ $r)⟩
  | ~q(nrel $r ![$t])       => do
    let ⟨tn, e⟩ ← SubTerm.Meta.resultSubst (L := L) (n := n) s t
    return ⟨q(nrel $r ![$tn]), q(subst_nrel₁ $r $e)⟩
  | ~q(nrel $r ![$t₁, $t₂]) => do
    let ⟨tn₁, e₁⟩ ← SubTerm.Meta.resultSubst (L := L) (n := n) s t₁
    let ⟨tn₂, e₂⟩ ← SubTerm.Meta.resultSubst (L := L) (n := n) s t₂
    return ⟨q(nrel $r ![$tn₁, $tn₂]), q(subst_nrel₂ $r $e₁ $e₂)⟩
  | ~q($p)                  => pure ⟨q(subst $s $p), q(rfl)⟩

partial def resultShift {L : Q(Language.{u})} {n : Q(ℕ)} : (p : Q(SyntacticSubFormula $L $n)) →
    MetaM ((res : Q(SyntacticSubFormula $L $n)) × Q(shift $p = $res))
  | ~q(⊤)                   => pure ⟨q(⊤), q(rfl)⟩
  | ~q(⊥)                   => pure ⟨q(⊥), q(rfl)⟩
  | ~q($p ⋏ $q)             => do
    let ⟨pn, pe⟩ ← resultShift p
    let ⟨qn, qe⟩ ← resultShift q
    return ⟨q($pn ⋏ $qn), q(hom_and_eq_of_eq $pe $qe)⟩
  | ~q($p ⋎ $q)             => do
    let ⟨pn, pe⟩ ← resultShift p
    let ⟨qn, qe⟩ ← resultShift q
    return ⟨q($pn ⋎ $qn), q(hom_or_eq_of_eq $pe $qe)⟩
  | ~q(~$p)             => do
    let ⟨pn, pe⟩ ← resultShift p
    return ⟨q(~$pn), q(hom_neg_eq_of_eq $pe)⟩
  | ~q(∀' $p)               => do
    let ⟨pn, e⟩ ← resultShift p
    return ⟨q(∀' $pn), q(shift_all_eq_of_eq $e)⟩
  | ~q(∃' $p)               => do
    let ⟨pn, e⟩ ← resultShift p
    return ⟨q(∃' $pn), q(shift_ex_eq_of_eq $e)⟩
  | ~q(rel $r ![])          => pure ⟨q(rel $r ![]), q(shift_rel₀ $r)⟩
  | ~q(rel $r ![$t])        => do
    let ⟨tn, e⟩ ← SubTerm.Meta.resultShift (L := L) (n := n) t
    return ⟨q(rel $r ![$tn]), q(shift_rel₁ $r $e)⟩
  | ~q(rel $r ![$t₁, $t₂])  => do
    let ⟨tn₁, e₁⟩ ← SubTerm.Meta.resultShift (L := L) (n := n) t₁
    let ⟨tn₂, e₂⟩ ← SubTerm.Meta.resultShift (L := L) (n := n) t₂
    return ⟨q(rel $r ![$tn₁, $tn₂]), q(shift_rel₂ $r $e₁ $e₂)⟩
  | ~q(nrel $r ![])         => pure ⟨q(nrel $r ![]), q(shift_nrel₀ $r)⟩
  | ~q(nrel $r ![$t])       => do
    let ⟨tn, e⟩ ← SubTerm.Meta.resultShift (L := L) (n := n) t
    return ⟨q(nrel $r ![$tn]), q(shift_nrel₁ $r $e)⟩
  | ~q(nrel $r ![$t₁, $t₂]) => do
    let ⟨tn₁, e₁⟩ ← SubTerm.Meta.resultShift (L := L) (n := n) t₁
    let ⟨tn₂, e₂⟩ ← SubTerm.Meta.resultShift (L := L) (n := n) t₂
    return ⟨q(nrel $r ![$tn₁, $tn₂]), q(shift_nrel₂ $r $e₁ $e₂)⟩
  | ~q(subst $s $p)         => do
    let ⟨sn, se⟩ ← SubTerm.Meta.resultShift (L := L) (n := n) s
    let ⟨pn, pe⟩ ← resultShift (L := L) (n := q($n + 1)) p
    return ⟨q(subst $sn $pn), q(shift_subst_eq_of_eq $se $pe)⟩
  | ~q($p)                  => pure ⟨q(shift $p), q(rfl)⟩

partial def resultNeg {L : Q(Language.{u})} {n : Q(ℕ)} : (p : Q(SyntacticSubFormula $L $n)) →
    MetaM ((res : Q(SyntacticSubFormula $L $n)) × Q(~$p = $res))
  | ~q(⊤)                   => pure ⟨q(⊥), q(rfl)⟩
  | ~q(⊥)                   => pure ⟨q(⊤), q(rfl)⟩
  | ~q($p ⋏ $q)             => do
    let ⟨pn, pe⟩ ← resultNeg p
    let ⟨qn, qe⟩ ← resultNeg q
    return ⟨q($pn ⋎ $qn), q(neg_and_eq_of_eq $pe $qe)⟩
  | ~q($p ⋎ $q)             => do
    let ⟨pn, pe⟩ ← resultNeg p
    let ⟨qn, qe⟩ ← resultNeg q
    return ⟨q($pn ⋏ $qn), q(neg_or_eq_of_eq $pe $qe)⟩
  | ~q(~$p)             => do
    return ⟨q($p), q(neg_neg' $p)⟩
  | ~q(∀' $p)               => do
    let ⟨pn, e⟩ ← resultNeg p
    return ⟨q(∃' $pn), q(neg_all_eq_of_eq $e)⟩
  | ~q(∃' $p)               => do
    let ⟨pn, e⟩ ← resultNeg p
    return ⟨q(∀' $pn), q(neg_ex_eq_of_eq $e)⟩
  | ~q(rel $r ![])          => pure ⟨q(nrel $r ![]), q(neg_rel $r _)⟩
  | ~q(rel $r ![$t])        => do
    return ⟨q(nrel $r ![$t]), q(neg_rel $r _)⟩
  | ~q(rel $r ![$t₁, $t₂])  => do
    return ⟨q(nrel $r ![$t₁, $t₂]), q(neg_rel $r _)⟩
  | ~q(nrel $r ![])         => pure ⟨q(rel $r ![]), q(neg_nrel $r _)⟩
  | ~q(nrel $r ![$t])       => do
    return ⟨q(rel $r ![$t]), q(neg_nrel $r _)⟩
  | ~q(nrel $r ![$t₁, $t₂]) => do
    return ⟨q(rel $r ![$t₁, $t₂]), q(neg_nrel $r _)⟩
  | ~q($p)                  => pure ⟨q(~$p), q(rfl)⟩

partial def result {L : Q(Language.{u})} {n : Q(ℕ)} : (p : Q(SyntacticSubFormula $L $n)) →
    MetaM ((res : Q(SyntacticSubFormula $L $n)) × Q($p = $res))
  | ~q(⊤)                   => pure ⟨q(⊤), q(rfl)⟩
  | ~q(⊥)                   => pure ⟨q(⊥), q(rfl)⟩
  | ~q($p ⋏ $q)             => do
    let ⟨pn, pe⟩ ← result p
    let ⟨qn, qe⟩ ← result q
    return ⟨q($pn ⋏ $qn), q(and_congr $pe $qe)⟩
  | ~q(~$p)                 => do
    let ⟨pn, e⟩ ← result p
    let ⟨pnn, ee⟩ ← resultNeg pn
    return ⟨q($pnn), q(neg_congr_eq $e $ee)⟩
  | ~q($p ⟶ $q)            => do
    let ⟨pn, pe⟩ ← result (L := L) (n := n) p
    let ⟨pnn, pee⟩ ← resultNeg pn
    let ⟨qn, qe⟩ ← result (L := L) (n := n) q
    return ⟨q($pnn ⋎ $qn), q(imp_eq_of_eq $pe $qe $pee)⟩
  | ~q($p ⟷ $q)            => do
    let ⟨pn, pe⟩ ← result (L := L) (n := n) p
    let ⟨pnn, pee⟩ ← resultNeg pn
    let ⟨qn, qe⟩ ← result (L := L) (n := n) q
    let ⟨qnn, qee⟩ ← resultNeg qn
    return ⟨q(($pnn ⋎ $qn) ⋏ ($qnn ⋎ $pn)), q(iff_eq_of_eq $pe $qe $pee $qee)⟩
  | ~q($p ⋎ $q)             => do
    let ⟨pn, pe⟩ ← result p
    let ⟨qn, qe⟩ ← result q
    return ⟨q($pn ⋎ $qn), q(or_congr $pe $qe)⟩
  | ~q(∀' $p)               => do
    let ⟨pn, pe⟩ ← result p
    return ⟨q(∀' $pn), q(all_congr $pe)⟩
  | ~q(∃' $p)               => do
    let ⟨pn, pe⟩ ← result p
    return ⟨q(∃' $pn), q(ex_congr $pe)⟩
  | ~q(rel $r ![])          => pure ⟨q(rel $r ![]), q(rfl)⟩
  | ~q(rel $r ![$t])        => do
    let ⟨tn, e⟩ ← SubTerm.Meta.result (L := L) (n := n) t
    return ⟨q(rel $r ![$tn]), q(rel₁_congr $e)⟩
  | ~q(rel $r ![$t₁, $t₂])  => do
    let ⟨tn₁, e₁⟩ ← SubTerm.Meta.result (L := L) (n := n) t₁
    let ⟨tn₂, e₂⟩ ← SubTerm.Meta.result (L := L) (n := n) t₂
    return ⟨q(rel $r ![$tn₁, $tn₂]), q(rel₂_congr $e₁ $e₂)⟩
  | ~q(nrel $r ![])         => pure ⟨q(nrel $r ![]), q(rfl)⟩
  | ~q(nrel $r ![$t])       => do
    let ⟨tn, e⟩ ← SubTerm.Meta.result (L := L) (n := n) t
    return ⟨q(nrel $r ![$tn]), q(nrel₁_congr $e)⟩
  | ~q(nrel $r ![$t₁, $t₂]) => do
    let ⟨tn₁, e₁⟩ ← SubTerm.Meta.result (L := L) (n := n) t₁
    let ⟨tn₂, e₂⟩ ← SubTerm.Meta.result (L := L) (n := n) t₂
    return ⟨q(nrel $r ![$tn₁, $tn₂]), q(nrel₂_congr $e₁ $e₂)⟩
  | ~q(free $p)             => do
    let ⟨pn, e⟩ ← result (L := L) (n := q($n + 1)) p
    let ⟨pnn, ee⟩ ← resultFree (L := L) (n := n) pn
    return ⟨q($pnn), q(free_congr_eq $e $ee)⟩
  | ~q(subst $s $p)         => do
    let ⟨sn, se⟩ ← SubTerm.Meta.result (L := L) (n := q($n)) s
    let ⟨pn, pe⟩ ← result (L := L) (n := q($n + 1)) p
    let ⟨n, e⟩ ← resultSubst (L := L) (n := n) sn pn
    return ⟨q($n), q(subst_congr_eq $se $pe $e)⟩
  | ~q(shift $p)            => do
    let ⟨pn, e⟩ ← result (L := L) (n := n) p
    let ⟨pnn, ee⟩ ← resultShift (L := L) (n := n) pn
    return ⟨q($pnn), q(shift_congr_eq $e $ee)⟩
  | ~q($p)                  => do
    -- logInfo m!"match fail: {p}"
    return ⟨q($p), q(rfl)⟩

partial def result' {L : Q(Language.{u})} {n : Q(ℕ)} (p : Q(SyntacticSubFormula $L $n)) :
    MetaM (Result (u := u) q(SyntacticSubFormula $L $n) p) := do
    let ⟨res, e⟩ ← result p
    return ⟨res, e⟩

partial def result₀ {L : Q(Language.{u})} (p : Q(SyntacticFormula $L)) :
    MetaM ((res : Q(SyntacticFormula $L)) × Q($p = $res)) :=
  result (L := L) (n := q(0)) p

partial def result₀_res {L : Q(Language.{u})} (p : Q(SyntacticFormula $L)) :
    MetaM Q(SyntacticFormula $L) := do
  let ⟨res, _⟩ ← result₀ (L := L) p
  return res

partial def result₀List {L : Q(Language.{u})} (l : List Q(SyntacticFormula $L)) :
    MetaM $ (res : List Q(SyntacticFormula $L)) × Q($(toQList (u := u) l) = $(toQList (u := u) res)) :=
  resultList result₀ l

partial def resultShift₀ {L : Q(Language.{u})} (p : Q(SyntacticFormula $L)) :
    MetaM $ (res : Q(SyntacticFormula $L)) × Q(shift $p = $res) :=
  resultShift (L := L) (n := q(0)) p

partial def resultShift₀List {L : Q(Language.{u})} (l : List Q(SyntacticFormula $L)) :
    MetaM $ (res : List Q(SyntacticFormula $L)) × Q(List.map shift $(toQList (u := u) l) = $(toQList (u := u) res)) :=
  funResultList (u := u) (α := q(SyntacticFormula $L)) q(shift) resultShift₀ l

partial def resultSubst₀ {L : Q(Language.{u})} (p : Q(SyntacticSubFormula $L 1)) (s : Q(SyntacticTerm $L)) :
    MetaM $ (res : Q(SyntacticFormula $L)) × Q(subst $s $p = $res) :=
  resultSubst (L := L) (n := q(0)) s p

partial def resultSubst₀List {L : Q(Language.{u})} (v : List Q(SyntacticTerm $L)) (p : Q(SyntacticSubFormula $L 1)) :
    MetaM $ (res : List Q(SyntacticFormula $L)) × Q(List.map (SubFormula.subst · $p) $(toQList (u := u) v) = $(toQList (u := u) res)) :=
  funResultList (u := u) (α := q(SyntacticTerm $L)) q((subst · $p)) (resultSubst₀ p) v

private inductive ResultTest (α : Type u) : (a : α) → Type u
  | result : (a b : α) → a = b → ResultTest α a

elab "dbg" : tactic => do
  let goalType ← Elab.Tactic.getMainTarget
  let some ⟨.succ u, ty⟩ ← checkSortQ' goalType | throwError "error: not a type"
  let ~q(ResultTest (SyntacticSubFormula $L $n) $p) := ty | throwError "error: not a type"
  logInfo m!"p = {p} : SyntacticSubFormula {L} {n}"
  let p : Q(SyntacticSubFormula $L $n) ← withReducible <| whnf p

  let ⟨pn, e⟩ ← result (L := L) (n := n) p
  logInfo m!"pn = {pn}"
  logInfo m!"e = {e}"
  let c : Q(ResultTest (SyntacticSubFormula $L $n) $p) := (q(ResultTest.result ($p) $pn $e) : Expr)
  Lean.Elab.Tactic.closeMainGoal c

example {t : SyntacticSubTerm Language.oring 14} : ResultTest (SyntacticSubFormula Language.oring 12)
    $ shift “⊤ → ∀ !(shift $ subst &99 “(!t) + (#6 * 8) < &7”)” :=
  by dbg

end Meta

end SubFormula

namespace DerivationList
open Derivation
variable {L : Language.{u}} [∀ k, DecidableEq (L.func k)] [∀ k, DecidableEq (L.rel k)] {G : List (SyntacticFormula L)}

def congr {G G' : List (SyntacticFormula L)} (e : G = G')
  (d : DerivationList G) : DerivationList G' := by rw [←e]; exact d

def head {p} (d : DerivationList (G ++ [p])) : DerivationList (p :: G) := d.cast (by ext; simp[or_comm])

def headVerum : DerivationList (⊤ :: G) := Derivation.verum _ (by simp)

def verum (h : ⊤ ∈ G) : DerivationList G := Derivation.verum _ (by simp[h])

def tailVerum (p) (h : ⊤ ∈ G) : DerivationList (p :: G) := Derivation.verum _ (by simp[h])

def headEm {p} (h : ~p ∈ G) : DerivationList (p :: G) := Derivation.em (p := p) (by simp) (by simp[h])

def headEm' {p np} (e : ~p = np) (h : np ∈ G) :
  DerivationList (p :: G) := Derivation.em (p := p) (by simp) (by simp[h, e])

def rotate {p} (d : DerivationList (G ++ [p])) : DerivationList (p :: G) :=
  d.cast (by ext; simp[or_comm])

def headWeakening {p} (d : DerivationList G) : DerivationList (p :: G) :=
  Derivation.weakening d (by simp; exact Finset.subset_insert  _ _)

def headWeakeningOfValid {p p'} (h : p = p') (d : Valid p) : DerivationList (p' :: G) :=
  Derivation.weakening d (by simp[h])

def headOr {p q} (d : DerivationList (G ++ [p, q])) : DerivationList (p ⋎ q :: G) :=
  (Derivation.or (Δ := G.toFinset) (p := p) (q := q) (d.cast $ by ext; simp; tauto)).cast (by simp)

def headAnd {p q} (dp : DerivationList (G ++ [p])) (dq : DerivationList (G ++ [q])) : DerivationList (p ⋏ q :: G) :=
  (Derivation.and (Δ := G.toFinset) (p := p) (q := q)
    (dp.cast $ by ext; simp[or_comm]) (dq.cast $ by ext; simp[or_comm])).cast (by simp)

def headAll {p : SyntacticSubFormula L 1} (d : DerivationList (G.map SubFormula.shift ++ [SubFormula.free p])) :
    DerivationList ((∀' p) :: G) :=
  (Derivation.all G.toFinset p (d.cast $ by ext; simp[shifts, SubFormula.shiftEmb, or_comm])).cast (by simp)

def headAllOfEq {G'} (eG : G.map SubFormula.shift = G') {p : SyntacticSubFormula L 1} {p} (ep : SubFormula.free p = p')
  (d : DerivationList (G' ++ [p'])) :
    DerivationList ((∀' p) :: G) :=
  (Derivation.all G.toFinset p (d.cast $ by ext; simp[←eG, ←ep, shifts, SubFormula.shiftEmb, or_comm])).cast (by simp)

def headEx {t} {p : SyntacticSubFormula L 1} (d : DerivationList (G ++ [SubFormula.subst t p])) :
    DerivationList ((∃' p) :: G) :=
  (Derivation.ex G.toFinset t p (d.cast $ by ext; simp[or_comm])).cast (by simp)

def headExInstances {v : List (SyntacticTerm L)} {p : SyntacticSubFormula L 1} (d : DerivationList (G ++ v.map (SubFormula.subst · p))) :
    DerivationList ((∃' p) :: G) :=
  (Derivation.exOfInstances (Γ := G.toFinset) v p (d.cast $ by ext x; simp[or_comm])).cast (by simp)

def headExInstancesOfEq {v : List (SyntacticTerm L)} {p : SyntacticSubFormula L 1} {pi : List (SyntacticFormula L)}
  (ev : v.map (SubFormula.subst · p) = pi) (d : DerivationList (G ++ pi)) :
    DerivationList ((∃' p) :: G) :=
  (Derivation.exOfInstances (Γ := G.toFinset) v p (d.cast $ by ext x; simp[←ev, or_comm])).cast (by simp)

end DerivationList

namespace Valid
open Derivation
variable {L : Language.{u}} [∀ k, DecidableEq (L.func k)] [∀ k, DecidableEq (L.rel k)]

def congr {p p' : SyntacticFormula L} (e : p' = p) (d : Valid p) : Valid p' :=
  e ▸ d

end Valid

set_option linter.unusedVariables false in
abbrev DerivationListQ (L : Q(Language.{u}))
  (dfunc : Q(∀ k, DecidableEq (($L).func k))) (drel : Q(∀ k, DecidableEq (($L).rel k)))
  (G : List Q(SyntacticFormula $L)) :=
  Q(DerivationList $(toQList (u := u) G))

namespace DerivationListQ
open SubFormula Derivation
variable (L : Q(Language.{u}))
  (dfunc : Q(∀ k, DecidableEq (($L).func k))) (drel : Q(∀ k, DecidableEq (($L).rel k))) (G : List Q(SyntacticFormula $L))

def toValidQ (p : Q(SyntacticFormula $L)) (d : DerivationListQ L dfunc drel [p]) : Q(Valid $p) :=
  q($d)

def congrQ {G G' : List Q(SyntacticFormula $L)} (e : Q($(toQList (u := u) G) = $(toQList (u := u) G')))
  (d : DerivationListQ L dfunc drel G) : DerivationListQ L dfunc drel G' :=
  q(DerivationList.congr $e $d)

def verum (h : G.elem q(⊤)) : DerivationListQ L dfunc drel G :=
  (q(DerivationList.verum $(Qq.toQListOfElem (u := u) h)) : Q(DerivationList $(toQList (u := u) G)))

-- assume q(⊤) ∈ G
def verumDec : MetaM (DerivationListQ L dfunc drel G) := do
  let h ← decideTQ q(⊤ ∈ $(toQList (u := u) G))
  return q(DerivationList.verum $h)

def headVerum : DerivationListQ L dfunc drel (q(⊤) :: G) :=
  q(DerivationList.headVerum)

def tailVerum (p : Q(SyntacticFormula $L)) (h : G.elem q(⊤)) :
  DerivationListQ L dfunc drel (p :: G) :=
  (q(DerivationList.tailVerum $p $(Qq.toQListOfElem (u := u) h)) : Q(DerivationList $(toQList (u := u) (p :: G))))

-- assume q(⊤) ∈ G
def tailVerumDec (p : Q(SyntacticFormula $L)) :
  MetaM $ DerivationListQ L dfunc drel (p :: G) := do
  let h ← decideTQ q(⊤ ∈ $(toQList (u := u) G))
  logInfo m!"h = {h}"
  return q(DerivationList.tailVerum $p $h)

def headWeakening {p} (d : DerivationListQ L dfunc drel G) : DerivationListQ L dfunc drel (p :: G) :=
  q(DerivationList.headWeakening $d)

def headWeakeningOfValid (p p' : Q(SyntacticFormula $L)) (h : Q($p = $p')) (d : Q(Valid $p)) : DerivationListQ L dfunc drel (p' :: G) :=
  q(DerivationList.headWeakeningOfValid $h $d)

-- def headEm {p : Q(SyntacticFormula $L)} (h : G.elem q(~$p)) : DerivationListQ L dfunc drel (p :: G) :=
--   q(DerivationList.headEm $(Qq.toQListOfElem (u := u) h))

def headEm {p np : Q(SyntacticFormula $L)} (e : Q(~$p = $np)) (h : G.elem np) : DerivationListQ L dfunc drel (p :: G) :=
  q(DerivationList.headEm' $e $(Qq.toQListOfElem (u := u) h))

-- assume np ∈ G
def headEmDec {p np : Q(SyntacticFormula $L)} (e : Q(~$p = $np)) : MetaM (DerivationListQ L dfunc drel (p :: G)) := do
  let h ← decideTQ q($np ∈ $(toQList (u := u) G))
  logInfo m!"h = {h}"
  return q(DerivationList.headEm' $e $h)

def rotate (p : Q(SyntacticFormula $L)) (d : DerivationListQ L dfunc drel (G ++ [p])) :
  DerivationListQ L dfunc drel (p :: G) :=
  let x : Q(DerivationList $ $(toQList (u := u) G) ++ [$p]) := d
  (q(DerivationList.rotate $x) : Q(DerivationList $(toQList (u := u) (p :: G))))

def headOr {p q : Q(SyntacticFormula $L)}
  (d : DerivationListQ L dfunc drel (Append.append G [q($p), q($q)])) :
    DerivationListQ L dfunc drel (q($p ⋎ $q) :: G) :=
  let x : Q(DerivationList $ Append.append  $(toQList (u := u) G) [$p, $q]) := d
  (q(DerivationList.headOr $x) : Q(DerivationList ($p ⋎ $q :: $(toQList (u := u) G))))

def headAnd {p q : Q(SyntacticFormula $L)}
  (dp : DerivationListQ L dfunc drel (G ++ [p]))
  (dq : DerivationListQ L dfunc drel (G ++ [q])) :
    DerivationListQ L dfunc drel (q($p ⋏ $q) :: G) :=
  let xp : Q(DerivationList $ Append.append  $(toQList (u := u) G) [$p]) := dp
  let xq : Q(DerivationList $ Append.append  $(toQList (u := u) G) [$q]) := dq
  (q(DerivationList.headAnd $xp $xq) : Q(DerivationList ($p ⋏ $q :: $(toQList (u := u) G))))

def headAll (sG : List Q(SyntacticFormula $L)) (eG : Q(List.map shift $(toQList (u := u) G) = $(toQList (u := u) sG)))
  {p : Q(SyntacticSubFormula $L 1)} {fp : Q(SyntacticFormula $L)} (ep : Q(free $p = $fp))
  (d : DerivationListQ L dfunc drel (Append.append sG [fp])) :
    DerivationListQ L dfunc drel (q(∀' $p) :: G) :=
  let x : Q(DerivationList $ $(toQList (u := u) (Append.append sG [fp]))) := d
  let x : Q(DerivationList $ Append.append $(toQList (u := u) sG) [$fp]) := d
  (q(DerivationList.headAllOfEq $eG (p := $p) $ep $x) : Q(DerivationList ((∀' $p) :: $(toQList (u := u) G))))

/-
def headAll (sG : List Q(SyntacticFormula $L)) (eG : Q(List.map shift $(toQList (u := u) G) = $(toQList (u := u) sG)))
  {p : Q(SyntacticSubFormula $L 1)} {fp : Q(SyntacticFormula $L)} (ep : Q(free $p = $fp))
  (d : DerivationListQ L dfunc drel (Append.append sG [fp])) :
    DerivationListQ L dfunc drel (q(∀' $p) :: G) :=
  let x : Q(DerivationList $ $(toQList (u := u) (Append.append sG [fp]))) := d
  let x : Q(DerivationList $ Append.append $(toQList (u := u) sG) [$fp]) := d
  let x : Q(DerivationList $ Append.append (List.map shift $(toQList (u := u) G)) [SubFormula.free $p]) :=
  -- TODO
    q(by rw[($eG), ($ep)]; exact $x)
  (q(DerivationList.headAll $x) : Q(DerivationList ((∀' $p) :: $(toQList (u := u) G))))
-/

def headEx (v : List Q(SyntacticTerm $L)) (p : Q(SyntacticSubFormula $L 1)) (pi : List Q(SyntacticFormula $L))
  (ev : Q(List.map (SubFormula.subst · $p) $(toQList (u := u) v) = $(toQList (u := u) pi)))
  (d : DerivationListQ L dfunc drel (G ++ pi)) :
    DerivationListQ L dfunc drel (q(∃' $p) :: G) :=
  -- let x : Q(DerivationList $ $(toQList (u := u) (G ++ pi))) := d
  let x : Q(DerivationList $ $(toQList (u := u) G) ++ $(toQList (u := u) pi)) := d
  q(DerivationList.headExInstancesOfEq $ev $x)

/-
def headEx (v : List Q(SyntacticTerm $L)) (p : Q(SyntacticSubFormula $L 1)) (pi : List Q(SyntacticFormula $L))
  (ev : Q(List.map (SubFormula.subst · $p) $(toQList (u := u) v) = $(toQList (u := u) pi)))
  (d : DerivationListQ L dfunc drel (G ++ pi)) :
    DerivationListQ L dfunc drel (q(∃' $p) :: G) :=
  -- let x : Q(DerivationList $ $(toQList (u := u) (G ++ pi))) := d
  let x : Q(DerivationList $ $(toQList (u := u) G) ++ $(toQList (u := u) pi)) := d
  let x : Q(DerivationList $ $(toQList (u := u) G) ++ List.map (SubFormula.subst · $p) $(toQList (u := u) v)) :=
  -- TODO
    q(by { rw[($ev)]; exact $x })
  q(DerivationList.headExInstances $x)
-/

def getFormula (e : Q(Type u)) : MetaM $ Option Q(SyntacticFormula $L) := do
  if let ~q(@Valid $L' $dfunc' $drel' $p) := e then
    if (← isDefEq (← whnf L) (← whnf L')) then
      return some p
    else return none
  else return none

section tauto

def tryProveByHyp (L : Q(Language.{u})) (dfunc : Q(∀ k, DecidableEq (($L).func k))) (drel : Q(∀ k, DecidableEq (($L).rel k)))
  (p : Q(SyntacticFormula $L)) (G : List Q(SyntacticFormula $L)) : MetaM $ Option (DerivationListQ (u := u) L dfunc drel (p :: G)) := do
  let ctx ← Lean.MonadLCtx.getLCtx
    let hyp ← ctx.findDeclM? fun decl: Lean.LocalDecl => do
      if !decl.isImplementationDetail then
        let declExpr := decl.toExpr
        let declType ← Lean.Meta.inferType declExpr
        let some p' ← getFormula L declType | return none
        let ⟨pn', e'⟩ ← Meta.result₀ p'
        if ← isDefEq p pn' then
          let some d ← checkTypeQ (u := .succ u) declExpr q(@Valid $L $dfunc $drel $p') | return none
            return some (p', e', d)
        else return none
      else return none
    if let some (p', e', d') := hyp then
      return some $ headWeakeningOfValid L dfunc drel G p p' e' d'
    else return none

def proveDerivationListQTauto (hypSearch : Bool)
  (L : Q(Language.{u})) (dfunc : Q(∀ k, DecidableEq (($L).func k))) (drel : Q(∀ k, DecidableEq (($L).rel k))) :
    ℕ → (G : List Q(SyntacticFormula $L)) → MetaM (DerivationListQ (u := u) L dfunc drel G)
  | 0,     _      => throwError "failed!"
  | _,     []     => throwError "empty goal"
  | s + 1, p :: G => do
    -- hypothesis search
    if let some d ← tryProveByHyp L dfunc drel p G then
      return d
    else 
    -- proof search
    let ⟨npn, npe⟩ ← SubFormula.Meta.resultNeg (L := L) (n := q(0)) p
    if h : G.elem npn then
      return DerivationListQ.headEm L dfunc drel G npe h
    else
    (match p with
    | ~q(⊤)       => pure $ headVerum L dfunc drel G
    | ~q(⊥)       => do
      let d ← proveDerivationListQTauto hypSearch L dfunc drel s G
      return headWeakening L dfunc drel G d
    | ~q($p ⋎ $q) => do
      let d ← proveDerivationListQTauto hypSearch L dfunc drel s (G ++ [p, q])
      return (headOr L dfunc drel G d)
    | ~q($p ⋏ $q) => do
      let dp ← proveDerivationListQTauto hypSearch L dfunc drel s (G ++ [p])
      let dq ← proveDerivationListQTauto hypSearch L dfunc drel s (G ++ [q])
      return (headAnd L dfunc drel G dp dq)
    | ~q($p)      => do
      let d ← proveDerivationListQTauto hypSearch L dfunc drel s (G ++ [p])
      return rotate L dfunc drel G p d
      : MetaM Q(DerivationList $ $p :: $(toQList (u := u) G)))

def proveValidTauto (L : Q(Language.{u})) (dfunc : Q(∀ k, DecidableEq (($L).func k))) (drel : Q(∀ k, DecidableEq (($L).rel k)))
  (s : ℕ) (p : Q(SyntacticFormula $L)) : MetaM Q(Valid $p) := do
  let ⟨pn, e⟩ ← SubFormula.Meta.result₀ (L := L) p
  let d ← proveDerivationListQTauto true L dfunc drel s [pn]
  let h := toValidQ L dfunc drel _ d
  return q(Valid.congr $e $h)

elab "proveTauto" n:(num)? : tactic => do
  let goalType ← Elab.Tactic.getMainTarget
  let some ⟨.succ _, ty⟩ ← checkSortQ' goalType | throwError "not a type"
  let ~q(@Valid $L $dfunc $drel $p) := ty | throwError "not a type: Valid p"
  let s : ℕ :=
    match n with
    | some n => n.getNat
    | none   => 16
  let b ← proveValidTauto L dfunc drel s p
  Lean.Elab.Tactic.closeMainGoal b

section
variable {L : Language.{u}} [∀ k, DecidableEq (L.func k)] [∀ k, DecidableEq (L.rel k)] (p q r s : SyntacticFormula L)

example : Valid ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r) := by proveTauto

example : Valid “((!p → !q) → !p) → !p” := by proveTauto

example : Valid “!p ∧ !q ∧ !r ↔ !r ∧ !p ∧ !q”  := by proveTauto

example (d : Valid p) : Valid “!p ∨ !q”  := by proveTauto

example (_ : Valid “¬(!p ∧ !q)”) (_ : Valid s) : Valid “!s → !p ∧ !q → !r”  := by proveTauto

example (_ : Valid “¬(!p ∧ !q)”) : Valid “¬!p ∨ ¬!q”  := by proveTauto

end

end tauto

def proveDerivationListQ (L : Q(Language.{u})) (dfunc : Q(∀ k, DecidableEq (($L).func k))) (drel : Q(∀ k, DecidableEq (($L).rel k)))
  (ts : List Q(SyntacticTerm $L)) :
    ℕ → (G : List Q(SyntacticFormula $L)) → MetaM (DerivationListQ (u := u) L dfunc drel G)
  | 0,     _      => throwError "failed!"
  | _,     []     => throwError "empty goal"
  | s + 1, p :: G => do
   -- hypothesis search
    if let some d ← tryProveByHyp L dfunc drel p G then
      return d
    else 
    -- proof search
    let ⟨npn, npe⟩ ← SubFormula.Meta.resultNeg (L := L) (n := q(0)) p
    if h : G.elem npn then
      return DerivationListQ.headEm L dfunc drel G npe h
    else
    (match p with
    | ~q(⊤) => pure $ headVerum L dfunc drel G
    | ~q(⊥) => do
      let d ← proveDerivationListQ L dfunc drel ts s G
      return headWeakening L dfunc drel G d
    | ~q($p ⋎ $q) => do
      let d ← proveDerivationListQ L dfunc drel ts s (G ++ [p, q])
      return (headOr L dfunc drel G d)
     | ~q($p ⋏ $q) => do
      let dp ← proveDerivationListQ L dfunc drel ts s (G ++ [p])
      let dq ← proveDerivationListQ L dfunc drel ts s (G ++ [q])
      return (headAnd L dfunc drel G dp dq)   
    | ~q(∀' $p)  => do
      let ⟨fp, fpe⟩ ← Meta.resultFree p
      let ⟨sG, sGe⟩ ← Meta.resultShift₀List G
      let d ← proveDerivationListQ L dfunc drel ts s (Append.append sG [fp])
      return headAll L dfunc drel G sG sGe fpe d
    | ~q(∃' $p)   => do
      let ⟨pi, pie⟩ ← Meta.resultSubst₀List ts p
      let d ← proveDerivationListQ L dfunc drel ts s (G ++ pi)
      return headEx L dfunc drel G ts p pi pie d
    | ~q($p) => do
      let d ← proveDerivationListQ L dfunc drel ts s (G ++ [p])
      return rotate L dfunc drel G p d
         : MetaM Q(DerivationList $ $p :: $(toQList (u := u) G)))

def proveValid (L : Q(Language.{u})) (dfunc : Q(∀ k, DecidableEq (($L).func k))) (drel : Q(∀ k, DecidableEq (($L).rel k)))
  (ts : List Q(SyntacticTerm $L)) (s : ℕ) (p : Q(SyntacticFormula $L)) : MetaM Q(Valid $p) := do
  let ⟨pn, e⟩ ← SubFormula.Meta.result₀ (L := L) p
  let d ← proveDerivationListQ L dfunc drel ts s [pn]
  let h := toValidQ L dfunc drel _ d
  return q(Valid.congr $e $h)

syntax termSeq := " [" (term,*) "]"

elab "prove" n:(num)? seq:(termSeq)? : tactic => do
  let goalType ← Elab.Tactic.getMainTarget
  let some ⟨.succ _, ty⟩ ← checkSortQ' goalType | throwError "error: not a type"
  let ~q(@Valid $L $dfunc $drel $p) := ty | throwError "error: not a type 2"
  let s : ℕ :=
    match n with
    | some n => n.getNat
    | none   => 16
  let ts : Array Q(SyntacticTerm $L) ←
    match seq with
    | some seq =>
      match seq with
      | `(termSeq| [ $ss,* ] ) => do ss.getElems.mapM (Term.elabTerm · (some q(SyntacticTerm $L)))
      | _                      => pure #[]
    | _        => pure #[q(&0 : SyntacticTerm $L), q(&1 : SyntacticTerm $L)]
  let b ← proveValid L dfunc drel ts.toList s p
  Lean.Elab.Tactic.closeMainGoal b

section
variable {L : Language.{u}} [∀ k, DecidableEq (L.func k)] [∀ k, DecidableEq (L.rel k)] (p q r s : SyntacticFormula L)
open Language

example (_ : Valid “¬(!p ∧ !q)”) : Valid “¬!p ∨ ¬!q”  := by proveTauto

example : Valid (L := oring) “&0 < 3 → ∃ &0 < #0” := by prove [T“3”]

example : Valid (L := oring) “&0 < &1 → ∃ ∃ #0 < #1” := by prove

example (_ : Valid (L := oring) “0 < 4 + 9”) : Valid (L := oring) “⊤ ∧ (∃ 0 < 4 + #0)”  := by prove [T“9”]

end

end DerivationListQ

end FirstOrder
