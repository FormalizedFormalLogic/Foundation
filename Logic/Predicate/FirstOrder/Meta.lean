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

lemma hom_imply_eq_of_eq {p q : SubFormula L μ n} {p' q'} (hp : f p = p') (hq : f q = q') :
    f (p ⟶ q) = p' ⟶ q' := by simp[←hp, ←hq]

lemma hom_iff_eq_of_eq {p q : SubFormula L μ n} {p' q'} (hp : f p = p') (hq : f q = q') :
    f (p ⟷ q) = p' ⟷ q' := by simp[←hp, ←hq]

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

lemma free_substs₀ {n'} {v : Fin 0 → SyntacticSubTerm L (n' + 1)} {p : SyntacticFormula L} :
    free (substs v p) = substs ![] (shift p) := by
  simp[free_substs, Matrix.empty_eq]

lemma free_substs₁ {n'} {t : SyntacticSubTerm L (n' + 1)} {p : SyntacticSubFormula L 1} :
    free (substs ![t] p) = substs ![t.free] (shift p) := by
  simp[free_substs, Function.comp, Matrix.constant_eq_singleton]

lemma free_substs₂ {n'} {t₁ t₂ : SyntacticSubTerm L (n' + 1)} {p : SyntacticSubFormula L 2} :
    free (substs ![t₁, t₂] p) = substs ![t₁.free, t₂.free] (shift p) := by
  simp[free_substs, Function.comp]; congr; funext i; cases' i using Fin.cases with i <;> simp

lemma free_substs₃ {n'} {t₁ t₂ t₃ : SyntacticSubTerm L (n' + 1)} {p : SyntacticSubFormula L 3} :
    free (substs ![t₁, t₂, t₃] p) = substs ![t₁.free, t₂.free, t₃.free] (shift p) := by
  simp[free_substs, Function.comp]; congr; funext i
  repeat (cases' i using Fin.cases with i <;> simp)

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

lemma neg_imp_eq_of_eq {p q qn : SubFormula L μ n} (hq : ~q = qn) :
    ~(p ⟶ q) = p ⋏ qn := by simp[←hq, imp_eq]

lemma neg_iff_eq_of_eq {p q pn qn : SubFormula L μ n} (hp : ~p = pn) (hq : ~q = qn) :
    ~(p ⟷ q) = (p ⋏ qn) ⋎ (q ⋏ pn) := by simp[←hp, ←hq, iff_eq]

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

lemma neg_congr {p p' : SubFormula L μ n} (e : p = p') :
  ~p = ~p' := congr_arg _ e

lemma imply_congr {p q p' q' : SubFormula L μ n} (ep : p = p') (eq : q = q') :
  (p ⟶ q) = (p' ⟶ q') := congr (congr_arg (fun p q => p ⟶ q) ep) eq

lemma iff_congr {p q p' q' : SubFormula L μ n} (ep : p = p') (eq : q = q') :
  (p ⟷ q) = (p' ⟷ q') := congr (congr_arg (fun p q => p ⟷ q) ep) eq

end lemmata

mutual

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
  | ~q(∀' $p)               => do
    let ⟨pn, e⟩ ← resultFree (n := q($n + 1)) p
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
  | ~q(~$p)             => do
    let ⟨pn, pe⟩ ← resultFree p
    return ⟨q(~$pn), q(hom_neg_eq_of_eq $pe)⟩
  | ~q($p ⟶ $q)        => do
    let ⟨pn, pe⟩ ← resultFree p
    let ⟨qn, qe⟩ ← resultFree q
    return ⟨q($pn ⟶ $qn), q(hom_imply_eq_of_eq $pe $qe)⟩
  | ~q($p ⟷ $q)        => do
    let ⟨pn, pe⟩ ← resultFree p
    let ⟨qn, qe⟩ ← resultFree q
    return ⟨q($pn ⟷ $qn), q(hom_iff_eq_of_eq $pe $qe)⟩
  | ~q(substs (n := 0) $v $p)        => do
    return ⟨q(⟦→ ![]⟧ (shift $p)), q(free_substs₀)⟩
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
  | ~q(~$p)                 => do
    let ⟨pn, pe⟩ ← resultSubst s p
    return ⟨q(~$pn), q(hom_neg_eq_of_eq $pe)⟩
  | ~q($p ⟶ $q)        => do
    let ⟨pn, pe⟩ ← resultSubst s p
    let ⟨qn, qe⟩ ← resultSubst s q
    return ⟨q($pn ⟶ $qn), q(hom_imply_eq_of_eq $pe $qe)⟩
  | ~q($p ⟷ $q)        => do
    let ⟨pn, pe⟩ ← resultSubst s p
    let ⟨qn, qe⟩ ← resultSubst s q
    return ⟨q($pn ⟷ $qn), q(hom_iff_eq_of_eq $pe $qe)⟩
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
  | ~q(~$p)                 => do
    let ⟨pn, pe⟩ ← resultShift p
    return ⟨q(~$pn), q(hom_neg_eq_of_eq $pe)⟩
  | ~q($p ⟶ $q)        => do
    let ⟨pn, pe⟩ ← resultShift p
    let ⟨qn, qe⟩ ← resultShift q
    return ⟨q($pn ⟶ $qn), q(hom_imply_eq_of_eq $pe $qe)⟩
  | ~q($p ⟷ $q)        => do
    let ⟨pn, pe⟩ ← resultShift p
    let ⟨qn, qe⟩ ← resultShift q
    return ⟨q($pn ⟷ $qn), q(hom_iff_eq_of_eq $pe $qe)⟩
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
  | ~q(~$p)                 => do
    return ⟨q($p), q(neg_neg' $p)⟩
  | ~q($p ⟶ $q)             => do
    let ⟨qn, e⟩ ← resultNeg q
    return ⟨q($p ⋏ $qn), q(neg_imp_eq_of_eq $e)⟩
  | ~q($p ⟷ $q)             => do
    let ⟨pn, pe⟩ ← resultNeg p
    let ⟨qn, qe⟩ ← resultNeg q
    return ⟨q(($p ⋏ $qn) ⋎ ($q ⋏ $pn)), q(neg_iff_eq_of_eq $pe $qe)⟩
  | ~q($p)                  => pure ⟨q(~$p), q(rfl)⟩

end

inductive UnfoldOption
  | neg
  | imply
  | iff
  | bUniv
  | bEx
  deriving DecidableEq, BEq

def unfoldAll : UnfoldOption → Bool := fun _ => true

def unfoldNone : UnfoldOption → Bool := fun _ => false

def unfoldOfList (l : List UnfoldOption) : UnfoldOption → Bool := l.elem 

variable (tp : SubTerm.Meta.NumeralUnfoldOption) (unfoldOpt : UnfoldOption → Bool)

partial def result {L : Q(Language.{u})} {n : Q(ℕ)} : (p : Q(SyntacticSubFormula $L $n)) →
    MetaM ((res : Q(SyntacticSubFormula $L $n)) × Q($p = $res))
  | ~q(⊤)                   => pure ⟨q(⊤), q(rfl)⟩
  | ~q(⊥)                   => pure ⟨q(⊥), q(rfl)⟩
  | ~q($p ⋏ $q)             => do
    let ⟨pn, pe⟩ ← result p
    let ⟨qn, qe⟩ ← result q
    return ⟨q($pn ⋏ $qn), q(and_congr $pe $qe)⟩
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
    let ⟨tn, e⟩ ← SubTerm.Meta.result tp (L := L) (n := n) t
    return ⟨q(rel $r ![$tn]), q(rel₁_congr $e)⟩
  | ~q(rel $r ![$t₁, $t₂])  => do
    let ⟨tn₁, e₁⟩ ← SubTerm.Meta.result tp (L := L) (n := n) t₁
    let ⟨tn₂, e₂⟩ ← SubTerm.Meta.result tp (L := L) (n := n) t₂
    return ⟨q(rel $r ![$tn₁, $tn₂]), q(rel₂_congr $e₁ $e₂)⟩
  | ~q(nrel $r ![])         => pure ⟨q(nrel $r ![]), q(rfl)⟩
  | ~q(nrel $r ![$t])       => do
    let ⟨tn, e⟩ ← SubTerm.Meta.result tp (L := L) (n := n) t
    return ⟨q(nrel $r ![$tn]), q(nrel₁_congr $e)⟩
  | ~q(nrel $r ![$t₁, $t₂]) => do
    let ⟨tn₁, e₁⟩ ← SubTerm.Meta.result tp (L := L) (n := n) t₁
    let ⟨tn₂, e₂⟩ ← SubTerm.Meta.result tp (L := L) (n := n) t₂

    return ⟨q(nrel $r ![$tn₁, $tn₂]), q(nrel₂_congr $e₁ $e₂)⟩
  | ~q(free $p)             => do
    let ⟨pn, e⟩ ← result (L := L) (n := q($n + 1)) p
    let ⟨pnn, ee⟩ ← resultFree (L := L) (n := n) pn
    return ⟨q($pnn), q(free_congr_eq $e $ee)⟩
  | ~q(subst $s $p)         => do
    let ⟨sn, se⟩ ← SubTerm.Meta.result tp (L := L) (n := q($n)) s
    let ⟨pn, pe⟩ ← result (L := L) (n := q($n + 1)) p
    let ⟨n, e⟩ ← resultSubst (L := L) (n := n) sn pn
    return ⟨q($n), q(subst_congr_eq $se $pe $e)⟩
  | ~q(shift $p)            => do
    let ⟨pn, e⟩ ← result (L := L) (n := n) p
    let ⟨pnn, ee⟩ ← resultShift (L := L) (n := n) pn
    return ⟨q($pnn), q(shift_congr_eq $e $ee)⟩
  | ~q(~$p)                 => do
    let ⟨pn, e⟩ ← result p
    if unfoldOpt UnfoldOption.neg then
      let ⟨pnn, ee⟩ ← resultNeg pn
      return ⟨q($pnn), q(neg_congr_eq $e $ee)⟩
    else return ⟨q(~$pn), q(neg_congr $e)⟩
  | ~q($p ⟶ $q)            => do
    let ⟨pn, pe⟩ ← result (L := L) (n := n) p
    let ⟨qn, qe⟩ ← result (L := L) (n := n) q    
    if unfoldOpt UnfoldOption.imply then
      if unfoldOpt UnfoldOption.neg then
        let ⟨pnn, pee⟩ ← resultNeg pn
        return ⟨q($pnn ⋎ $qn), q(imp_eq_of_eq $pe $qe $pee)⟩
      return ⟨q(~$pn ⋎ $qn), q(imply_congr $pe $qe)⟩
    else return ⟨q($pn ⟶ $qn), q(imply_congr $pe $qe)⟩
  | ~q($p ⟷ $q)            => do
    let ⟨pn, pe⟩ ← result (L := L) (n := n) p
    let ⟨qn, qe⟩ ← result (L := L) (n := n) q
    if unfoldOpt UnfoldOption.iff then
      if unfoldOpt UnfoldOption.imply then
        if unfoldOpt UnfoldOption.neg then
          let ⟨pnn, pee⟩ ← resultNeg pn
          let ⟨qnn, qee⟩ ← resultNeg qn
          return ⟨q(($pnn ⋎ $qn) ⋏ ($qnn ⋎ $pn)), q(iff_eq_of_eq $pe $qe $pee $qee)⟩
        else return ⟨q((~$pn ⋎ $qn) ⋏ (~$qn ⋎ $pn)), q(iff_congr $pe $qe)⟩
      else
        return ⟨q(($pn ⟶ $qn) ⋏ ($qn ⟶ $pn)), q(iff_congr $pe $qe)⟩
    else return ⟨q($pn ⟷ $qn), q(iff_congr $pe $qe)⟩
  | ~q($p)                  => do
    -- logInfo m!"match fail: {p}"
    return ⟨q($p), q(rfl)⟩

partial def result₀ {L : Q(Language.{u})} (p : Q(SyntacticFormula $L)) :
    MetaM ((res : Q(SyntacticFormula $L)) × Q($p = $res)) :=
  result tp unfoldOpt (L := L) (n := q(0)) p

partial def result₀_res {L : Q(Language.{u})} (p : Q(SyntacticFormula $L)) :
    MetaM Q(SyntacticFormula $L) := do
  let ⟨res, _⟩ ← result₀ tp unfoldOpt (L := L) p
  return res

partial def result₀List {L : Q(Language.{u})} (l : List Q(SyntacticFormula $L)) :
    MetaM $ (res : List Q(SyntacticFormula $L)) × Q($(toQList (u := u) l) = $(toQList (u := u) res)) :=
  resultList (result₀ tp unfoldOpt) l

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

  let ⟨pn, e⟩ ← result SubTerm.Meta.NumeralUnfoldOption.unfoldSucc (unfoldOfList [UnfoldOption.iff]) (L := L) (n := n) p
  logInfo m!"pn = {pn}"
  -- logInfo m!"e = {e}"
  let c : Q(ResultTest (SyntacticSubFormula $L $n) $p) := (q(ResultTest.result ($p) $pn $e) : Expr)
  Lean.Elab.Tactic.closeMainGoal c

example {t : SyntacticSubTerm Language.oring 14} : ResultTest (SyntacticSubFormula Language.oring 12)
    $ shift “3 < #4 ↔ ∀ !(shift $ subst &99 “(!t) + (#6 * 8) < &7”)” :=
  by dbg

example {t : SyntacticSubTerm Language.oring 14} : ResultTest (SyntacticSubFormula Language.oring 12)
    $ “0 < 2” :=
  by dbg

end Meta

end SubFormula

namespace DerivationList
open DerivationCutRestricted
variable {L : Language.{u}} [∀ k, DecidableEq (L.func k)] [∀ k, DecidableEq (L.rel k)] {G : List (SyntacticFormula L)}

def congr {G G' : List (SyntacticFormula L)} (e : G' = G)
  (d : DerivationList G) : DerivationList G' := by rw [e]; exact d

def head {p} (d : DerivationList (G ++ [p])) : DerivationList (p :: G) := d.cast (by ext; simp[or_comm])

def headVerum : DerivationList (⊤ :: G) := DerivationCutRestricted.verum _ (by simp)

def verum (h : ⊤ ∈ G) : DerivationList G := DerivationCutRestricted.verum _ (by simp[h])

def headEm {p} (h : ~p ∈ G) : DerivationList (p :: G) := DerivationCutRestricted.em (p := p) (by simp) (by simp[h])

def headEm' {p np} (e : ~p = np) (h : np ∈ G) :
  DerivationList (p :: G) := DerivationCutRestricted.em (p := p) (by simp) (by simp[h, e])

def rotate {p} (d : DerivationList (G ++ [p])) : DerivationList (p :: G) :=
  d.cast (by ext; simp[or_comm])

def headWeakening {p} (d : DerivationList G) : DerivationList (p :: G) :=
  DerivationCutRestricted.weakening d (by simp; exact Finset.subset_insert  _ _)

def headWeakeningOfDerivation₁ {p p'} (h : p = p') (d : Derivation₁ p) : DerivationList (p' :: G) :=
  DerivationCutRestricted.weakening d (by simp[h])

def headOr {p q} (d : DerivationList (G ++ [p, q])) : DerivationList (p ⋎ q :: G) :=
  (DerivationCutRestricted.or (Δ := G.toFinset) (p := p) (q := q) (d.cast $ by ext; simp; tauto)).cast (by simp)

def headAnd {p q} (dp : DerivationList (G ++ [p])) (dq : DerivationList (G ++ [q])) : DerivationList (p ⋏ q :: G) :=
  (DerivationCutRestricted.and (Δ := G.toFinset) (p := p) (q := q)
    (dp.cast $ by ext; simp[or_comm]) (dq.cast $ by ext; simp[or_comm])).cast (by simp)

def headAll {p : SyntacticSubFormula L 1} (d : DerivationList (G.map SubFormula.shift ++ [SubFormula.free p])) :
    DerivationList ((∀' p) :: G) :=
  (DerivationCutRestricted.all G.toFinset p (d.cast $ by ext; simp[shifts, SubFormula.shiftEmb, or_comm])).cast (by simp)

def headAllOfEq {G'} (eG : G.map SubFormula.shift = G') {p : SyntacticSubFormula L 1} {p} (ep : SubFormula.free p = p')
  (d : DerivationList (G' ++ [p'])) :
    DerivationList ((∀' p) :: G) :=
  (DerivationCutRestricted.all G.toFinset p (d.cast $ by ext; simp[←eG, ←ep, shifts, SubFormula.shiftEmb, or_comm])).cast (by simp)

def headEx {t} {p : SyntacticSubFormula L 1} (d : DerivationList (G ++ [SubFormula.subst t p])) :
    DerivationList ((∃' p) :: G) :=
  (DerivationCutRestricted.ex G.toFinset t p (d.cast $ by ext; simp[or_comm])).cast (by simp)

def headExInstances {v : List (SyntacticTerm L)} {p : SyntacticSubFormula L 1} (d : DerivationList (G ++ v.map (SubFormula.subst · p))) :
    DerivationList ((∃' p) :: G) :=
  (DerivationCutRestricted.exOfInstances (Γ := G.toFinset) v p (d.cast $ by ext x; simp[or_comm])).cast (by simp)

def headExInstancesOfEq' {v : List (SyntacticTerm L)} {p : SyntacticSubFormula L 1} {pi : List (SyntacticFormula L)}
  (ev : v.map (SubFormula.subst · p) = pi) (d : DerivationList (G ++ pi ++ [∃' p])) :
    DerivationList ((∃' p) :: G) :=
  (DerivationCutRestricted.exOfInstances' (Γ := G.toFinset) v p
    (d.cast $ by
      simp[ev, Finset.insert_eq];
      rw[Finset.union_comm {∃' p}, ←Finset.union_assoc, Finset.union_comm pi.toFinset])).cast (by simp)

def headExInstancesOfEq {v : List (SyntacticTerm L)} {p : SyntacticSubFormula L 1} {pi : List (SyntacticFormula L)}
  (ev : v.map (SubFormula.subst · p) = pi) (d : DerivationList (G ++ pi)) :
    DerivationList ((∃' p) :: G) :=
  (DerivationCutRestricted.exOfInstances (Γ := G.toFinset) v p (d.cast $ by ext x; simp[←ev, or_comm])).cast (by simp)

end DerivationList

namespace Derivation₁
open DerivationCutRestricted
variable {L : Language.{u}} [∀ k, DecidableEq (L.func k)] [∀ k, DecidableEq (L.rel k)]

def congr {p p' : SyntacticFormula L} (e : p' = p) (d : Derivation₁ p) : Derivation₁ p' :=
  e ▸ d

end Derivation₁

set_option linter.unusedVariables false in
abbrev DerivationListQ (L : Q(Language.{u}))
  (dfunc : Q(∀ k, DecidableEq (($L).func k))) (drel : Q(∀ k, DecidableEq (($L).rel k)))
  (G : List Q(SyntacticFormula $L)) :=
  Q(DerivationList $(toQList (u := u) G))

namespace DerivationListQ
open SubFormula DerivationCutRestricted
variable (L : Q(Language.{u}))
  (dfunc : Q(∀ k, DecidableEq (($L).func k))) (drel : Q(∀ k, DecidableEq (($L).rel k))) (G : List Q(SyntacticFormula $L))

def toDerivation₁Q (p : Q(SyntacticFormula $L)) (d : DerivationListQ L dfunc drel [p]) : Q(Derivation₁ $p) :=
  q($d)

def headVerum : DerivationListQ L dfunc drel (q(⊤) :: G) :=
  q(DerivationList.headVerum)

def headWeakening {p} (d : DerivationListQ L dfunc drel G) : DerivationListQ L dfunc drel (p :: G) :=
  q(DerivationList.headWeakening $d)

def headWeakeningOfDerivation₁ (p p' : Q(SyntacticFormula $L)) (h : Q($p = $p')) (d : Q(Derivation₁ $p)) : DerivationListQ L dfunc drel (p' :: G) :=
  q(DerivationList.headWeakeningOfDerivation₁ $h $d)

def headEm (p np : Q(SyntacticFormula $L)) (e : Q(~$p = $np)) :
    MetaM (DerivationListQ L dfunc drel (p :: G)) := do
  let some h ← Qq.memQList? (u := u) np G | throwError m! "failed to prove {np} ∈ {G}"
  return q(DerivationList.headEm' $e $h)

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

def headEx' (v : List Q(SyntacticTerm $L)) (p : Q(SyntacticSubFormula $L 1)) (pi : List Q(SyntacticFormula $L))
  (ev : Q(List.map (SubFormula.subst · $p) $(toQList (u := u) v) = $(toQList (u := u) pi)))
  (d : DerivationListQ L dfunc drel (G ++ pi ++ [(q(∃' $p) : Q(SyntacticFormula $L))])) :
    DerivationListQ L dfunc drel (q(∃' $p) :: G) :=
  -- let x : Q(DerivationList $ $(toQList (u := u) (G ++ pi))) := d
  let x : Q(DerivationList $ $(toQList (u := u) G) ++ $(toQList (u := u) pi) ++ [∃' $p]) := d
  q(DerivationList.headExInstancesOfEq' $ev $x)

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
  if let ~q(@Derivation₁ $L' $dfunc' $drel' $p) := e then
    if (← isDefEq (← whnf L) (← whnf L')) then
      return some p
    else return none
  else return none

variable (tp : SubTerm.Meta.NumeralUnfoldOption) (unfoldOpt : SubFormula.Meta.UnfoldOption → Bool)

section tauto

def tryProveByHyp (L : Q(Language.{u})) (dfunc : Q(∀ k, DecidableEq (($L).func k))) (drel : Q(∀ k, DecidableEq (($L).rel k)))
  (p : Q(SyntacticFormula $L)) (G : List Q(SyntacticFormula $L)) : MetaM $ Option (DerivationListQ (u := u) L dfunc drel (p :: G)) := do
  let ctx ← Lean.MonadLCtx.getLCtx
    let hyp ← ctx.findDeclM? fun decl: Lean.LocalDecl => do
      if !decl.isImplementationDetail then
        let declExpr := decl.toExpr
        let declType ← Lean.Meta.inferType declExpr
        let some p' ← getFormula L declType | return none
        let ⟨pn', e'⟩ ← Meta.result₀ tp unfoldOpt p'
        if ← isDefEq p pn' then
          let some d ← checkTypeQ (u := .succ u) declExpr q(@Derivation₁ $L $dfunc $drel $p') | return none
            return some (p', e', d)
        else return none
      else return none
    if let some (p', e', d') := hyp then
      return some $ headWeakeningOfDerivation₁ L dfunc drel G p p' e' d'
    else return none

def proveDerivationListQTauto (hypSearch : Bool)
  (L : Q(Language.{u})) (dfunc : Q(∀ k, DecidableEq (($L).func k))) (drel : Q(∀ k, DecidableEq (($L).rel k))) :
    ℕ → (G : List Q(SyntacticFormula $L)) → MetaM (DerivationListQ (u := u) L dfunc drel G)
  | 0,     _      => throwError "failed!"
  | _,     []     => throwError "empty goal"
  | s + 1, p :: G => do
    -- hypothesis search
    if let some d ← tryProveByHyp tp unfoldOpt L dfunc drel p G then
      return d
    else 
    -- proof search
    let ⟨npn, npe⟩ ← SubFormula.Meta.resultNeg (L := L) (n := q(0)) p
    if (← G.elemM isStrongEq npn) then
      DerivationListQ.headEm L dfunc drel G p npn npe
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

def proveDerivation₁Tauto (L : Q(Language.{u})) (dfunc : Q(∀ k, DecidableEq (($L).func k))) (drel : Q(∀ k, DecidableEq (($L).rel k)))
  (s : ℕ) (p : Q(SyntacticFormula $L)) : MetaM Q(Derivation₁ $p) := do
  let ⟨pn, e⟩ ← SubFormula.Meta.result₀ tp unfoldOpt (L := L) p
  let d ← proveDerivationListQTauto tp unfoldOpt true L dfunc drel s [pn]
  let h := toDerivation₁Q L dfunc drel _ d
  return q(Derivation₁.congr $e $h)

elab "proveTauto" n:(num)? : tactic => do
  let goalType ← Elab.Tactic.getMainTarget
  let some ⟨.succ _, ty⟩ ← checkSortQ' goalType | throwError "not a type"
  let ~q(@Derivation₁ $L $dfunc $drel $p) := ty | throwError "not a type: Derivation₁ p"
  let s : ℕ :=
    match n with
    | some n => n.getNat
    | none   => 16
  let b ← proveDerivation₁Tauto SubTerm.Meta.NumeralUnfoldOption.none SubFormula.Meta.unfoldAll L dfunc drel s p
  Lean.Elab.Tactic.closeMainGoal b

/-
section
variable {L : Language.{u}} [∀ k, DecidableEq (L.func k)] [∀ k, DecidableEq (L.rel k)] (p q r s : SyntacticFormula L)

example : Derivation₁ ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r) := by proveTauto

example : Derivation₁ “((!p → !q) → !p) → !p” := by proveTauto

example : Derivation₁ “!p ∧ !q ∧ !r ↔ !r ∧ !p ∧ !q”  := by proveTauto

example (d : Derivation₁ p) : Derivation₁ “!p ∨ !q”  := by proveTauto

example (_ : Derivation₁ “¬(!p ∧ !q)”) (_ : Derivation₁ s) : Derivation₁ “!s → !p ∧ !q → !r”  := by proveTauto

example (_ : Derivation₁ “¬(!p ∧ !q)”) : Derivation₁ “¬!p ∨ ¬!q”  := by proveTauto

end
-/
end tauto

def proveDerivationListQ (L : Q(Language.{u})) (dfunc : Q(∀ k, DecidableEq (($L).func k))) (drel : Q(∀ k, DecidableEq (($L).rel k)))
  (ts : List Q(SyntacticTerm $L)) :
    ℕ → (G : List Q(SyntacticFormula $L)) → MetaM (DerivationListQ (u := u) L dfunc drel G)
  | 0,     _      => throwError "failed!"
  | _,     []     => throwError "empty goal"
  | s + 1, p :: G => do
    -- logInfo m! "s = {s}"
    -- logInfo m! "p :: G = {p :: G}"
   -- hypothesis search
    if let some d ← tryProveByHyp tp unfoldOpt L dfunc drel p G then
      return d
    else 
    -- proof search
    let ⟨npn, npe⟩ ← SubFormula.Meta.resultNeg (L := L) (n := q(0)) p
    if (← G.elemM isStrongEq npn) then
      DerivationListQ.headEm L dfunc drel G p npn npe
    else
    (match p with
    | ~q(⊤)       => pure $ headVerum L dfunc drel G
    | ~q(⊥)       => do
      let d ← proveDerivationListQ L dfunc drel ts s G
      return headWeakening L dfunc drel G d
    | ~q($p ⋎ $q) => do
      let d ← proveDerivationListQ L dfunc drel ts s (G ++ [p, q])
      return (headOr L dfunc drel G d)
    | ~q($p ⋏ $q) => do
      let dp ← proveDerivationListQ L dfunc drel ts s (G ++ [p])
      let dq ← proveDerivationListQ L dfunc drel ts s (G ++ [q])
      return (headAnd L dfunc drel G dp dq)   
    | ~q(∀' $p)   => do
      let ⟨fp, fpe⟩ ← Meta.resultFree p
      let ⟨sG, sGe⟩ ← Meta.resultShift₀List G
      let d ← proveDerivationListQ L dfunc drel ts s (Append.append sG [fp])
      return headAll L dfunc drel G sG sGe fpe d
    | ~q(∃' $p)   => do
      let ⟨pi, pie⟩ ← Meta.resultSubst₀List ts p
      let d ← proveDerivationListQ L dfunc drel ts s (G ++ pi ++ [q(∃' $p)])
      return headEx' L dfunc drel G ts p pi pie d
    | ~q($p)      => do
      let d ← proveDerivationListQ L dfunc drel ts s (G ++ [p])
      return rotate L dfunc drel G p d
         : MetaM Q(DerivationList $ $p :: $(toQList (u := u) G)))

def proveDerivationList (L : Q(Language.{u})) (dfunc : Q(∀ k, DecidableEq (($L).func k))) (drel : Q(∀ k, DecidableEq (($L).rel k)))
  (ts : List Q(SyntacticTerm $L)) (s : ℕ) (Γ : Q(List (SyntacticFormula $L))) : MetaM Q(DerivationList $Γ) := do
  let G ← Qq.ofQList Γ
  let ⟨G', e⟩ ← SubFormula.Meta.result₀List tp unfoldOpt (L := L) G
  have e' : Q($Γ = $(Qq.toQList (u := u) G')) := e
  let d : Q(DerivationList $(toQList (u := u) G')) ← proveDerivationListQ tp unfoldOpt L dfunc drel ts s G'
  return q(($d).congr $e')

def proveDerivation₁ (L : Q(Language.{u})) (dfunc : Q(∀ k, DecidableEq (($L).func k))) (drel : Q(∀ k, DecidableEq (($L).rel k)))
  (ts : List Q(SyntacticTerm $L)) (s : ℕ) (p : Q(SyntacticFormula $L)) : MetaM Q(Derivation₁ $p) := do
  let ⟨pn, e⟩ ← SubFormula.Meta.result₀ tp unfoldOpt (L := L) p
  let d ← proveDerivationListQ tp unfoldOpt L dfunc drel ts s [pn]
  let h := toDerivation₁Q L dfunc drel _ d
  return q(Derivation₁.congr $e $h)

syntax termSeq := " [" (term,*) "]"

elab "proveDerivationList" n:(num)? seq:(termSeq)? : tactic => do
  let goalType ← Elab.Tactic.getMainTarget
  let some ⟨.succ _, ty⟩ ← checkSortQ' goalType | throwError "error: not a type"
  let ~q(@DerivationList $L $dfunc $drel $Γ) := ty | throwError "error: not a type 2"
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
  let b ← proveDerivationList SubTerm.Meta.NumeralUnfoldOption.none SubFormula.Meta.unfoldAll
    L dfunc drel ts.toList s Γ
  Lean.Elab.Tactic.closeMainGoal b

elab "proveDerivation₁" n:(num)? seq:(termSeq)? : tactic => do
  let goalType ← Elab.Tactic.getMainTarget
  let some ⟨.succ _, ty⟩ ← checkSortQ' goalType | throwError "error: not a type"
  let ~q(@Derivation₁ $L $dfunc $drel $p) := ty | throwError "error: not a type 2"
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
  let b ← proveDerivation₁ SubTerm.Meta.NumeralUnfoldOption.none SubFormula.Meta.unfoldAll
    L dfunc drel ts.toList s p
  Lean.Elab.Tactic.closeMainGoal b

/-
section
variable {L : Language.{u}} [∀ k, DecidableEq (L.func k)] [∀ k, DecidableEq (L.rel k)] (p q r s : SyntacticFormula L)
open Language

example (_ : Derivation₁ “¬(!p ∧ !q)”) : Derivation₁ “¬!p ∨ ¬!q”  := by proveTauto

example : Derivation₁ (L := oring) “&0 < 3 → ∃ &0 < #0” := by proveDerivation₁ [T“3”]

example : Derivation₁ (L := oring) “&0 < 4 + &1 → ∃ ∃ ∃ #0 < #1 + #2” := by proveDerivation₁ 32 [&1, T“4”, &0]

example (_ : Derivation₁ (L := oring) “0 < 4 + 9”) : Derivation₁ (L := oring) “⊤ ∧ (∃ 0 < 4 + #0)”  := by proveDerivation₁ [T“9”]

example : Derivation₁ (L := oring) “0 < 4 + 9 → (∃ 0 < 4 + #0)”  := by proveDerivation₁ [T“9”]

example : DerivationList (L := oring) [“¬(0 + &9 < 2)”, “∃ #0 < 2”] := by simp; proveDerivationList [T“0 + &9”]

end
-/

end DerivationListQ

end FirstOrder
