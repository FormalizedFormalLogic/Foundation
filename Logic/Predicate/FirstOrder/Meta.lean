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
    logInfo m!"match fail: {p}"
    return ⟨q($p), q(rfl)⟩

partial def result' {L : Q(Language.{u})} {n : Q(ℕ)} (p : Q(SyntacticSubFormula $L $n)) :
    MetaM (Result (u := u) q(SyntacticSubFormula $L $n) p) := do
    let ⟨res, e⟩ ← result p
    return ⟨res, e⟩

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

end FirstOrder
