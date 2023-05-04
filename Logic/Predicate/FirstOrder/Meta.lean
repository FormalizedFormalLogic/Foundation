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


section substs
variable {k} {w : Fin k → SyntacticSubTerm L n}

lemma substs_rel_of_eq {l} (r : L.rel l) {v : Fin l → SyntacticSubTerm L k} {v'} (h : SubTerm.substs w ∘ v = v') :
    substs w (rel r v) = rel r v' := by
  simp[←h]; rfl

lemma substs_nrel_of_eq {l} (r : L.rel l) {v : Fin l → SyntacticSubTerm L k} {v'} (h : SubTerm.substs w ∘ v = v') :
    substs w (nrel r v) = nrel r v' := by
  simp[←h]; rfl

lemma substs_all_eq_of_eq {p : SyntacticSubFormula L (k + 1)} {w' p'}
  (hw : SubTerm.bShift ∘ w = w') (hp : substs (#0 :> w') p = p') :
    substs w (∀' p) = ∀' p' := by simp[←hw, ←hp, substs_all]

lemma substs_ex_eq_of_eq {p : SyntacticSubFormula L (k + 1)} {w' p'}
  (hw : SubTerm.bShift ∘ w = w') (hp : substs (#0 :> w') p = p') :
    substs w (∃' p) = ∃' p' := by simp[←hw, ←hp, substs_ex]

lemma substs_substs_of_eq {l} {v : Fin n → SyntacticSubTerm L l} {p : SyntacticSubFormula L k} {w' p'}
  (hw : SubTerm.substs v ∘ w = w') (hp : substs w' p = p') :
    substs v (substs w p) = p' := by
  simp[←hw, ←hp, substs_substs]

end substs

section free

lemma free_rel_of_eq {k} (r : L.rel k) {v : Fin k → SyntacticSubTerm L (n + 1)} {v'} (h : SubTerm.free ∘ v = v') :
    free (rel r v) = rel r v' := by
  simp[←h]; rfl

lemma free_nrel_of_eq {k} (r : L.rel k) {v : Fin k → SyntacticSubTerm L (n + 1)} {v'} (h : SubTerm.free ∘ v = v') :
    free (nrel r v) = nrel r v' := by
  simp[←h]; rfl

lemma free_all_eq_of_eq {p : SyntacticSubFormula L (n + 1 + 1)} {p'} (h : free p = p') :
    free (∀' p) = ∀' p' := by simp[←h]

lemma free_ex_eq_of_eq {p : SyntacticSubFormula L (n + 1 + 1)} {p'} (h : free p = p') :
    free (∃' p) = ∃' p' := by simp[←h]

lemma free_substs_of_eq {k} {w : Fin k → SyntacticSubTerm L (n + 1)} {p : SyntacticSubFormula L k} {w' p' p''}
  (hw : SubTerm.free ∘ w = w') (hp : shift p = p') (hp' : substs w' p' = p''):
    free (substs w p) = p'' := by
  simp[←hw, ←hp, ←hp', free_substs, Function.comp]

end free

section shift

lemma shift_rel_of_eq {k} (r : L.rel k) {v : Fin k → SyntacticSubTerm L n} {v'} (h : SubTerm.shift ∘ v = v') :
    shift (rel r v) = rel r v' := by
  simp[←h]; rfl

lemma shift_nrel_of_eq {k} (r : L.rel k) {v : Fin k → SyntacticSubTerm L n} {v'} (h : SubTerm.shift ∘ v = v') :
    shift (nrel r v) = nrel r v' := by
  simp[←h]; rfl

lemma shift_all_eq_of_eq {p : SyntacticSubFormula L (n + 1)} {p'} (h : shift p = p') :
    shift (∀' p) = ∀' p' := by simp[←h]

lemma shift_ex_eq_of_eq {p : SyntacticSubFormula L (n + 1)} {p'} (h : shift p = p') :
    shift (∃' p) = ∃' p' := by simp[←h]

lemma shift_substs_of_eq {k} {w : Fin k → SyntacticSubTerm L n} {p : SyntacticSubFormula L k} {w' p' p''}
  (hw : SubTerm.shift ∘ w = w') (hp : shift p = p') (hp' : substs w' p' = p'') :
    shift (substs w p) = p'' := by
  simp[←hw, ←hp, ←hp', shift_substs, Function.comp]

end shift

section neg

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

lemma neg_substs_of_eq {k} {w : Fin k → SyntacticSubTerm L n} {p : SyntacticSubFormula L k} {p' p''}
  (hp : ~p = p') (hp' : substs w p' = p'') :
    ~(substs w p) = p'' := by
  simp[←hp, ←hp', shift_substs, Function.comp]

end neg

lemma rel_congr {k} (r : L.rel k) {v v' : Fin k → SubTerm L μ n} (h : v = v') :
    rel r v = rel r v' := congr_arg _ (by simp[h])

lemma nrel_congr {k} (r : L.rel k) {v v' : Fin k → SubTerm L μ n} (h : v = v') :
    nrel r v = nrel r v' := congr_arg _ (by simp[h])

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

lemma shift_congr_eq {p p' : SyntacticSubFormula L n} {q} (e : p = p') (h : shift p' = q) :
  shift p = q := Eq.trans (congr_arg _ e) h

lemma substs_congr_eq {k} {w w' : Fin k → SyntacticSubTerm L n} {p p' : SyntacticSubFormula L k} {p''}
  (hw : w = w') (hp : p = p') (h : substs w' p' = p'') :
  substs w p = p'' := hw ▸ hp ▸ h

lemma neg_congr {p p' : SubFormula L μ n} (e : p = p') :
  ~p = ~p' := congr_arg _ e

lemma imply_congr {p q p' q' : SubFormula L μ n} (ep : p = p') (eq : q = q') :
  (p ⟶ q) = (p' ⟶ q') := congr (congr_arg (fun p q => p ⟶ q) ep) eq

lemma iff_congr {p q p' q' : SubFormula L μ n} (ep : p = p') (eq : q = q') :
  (p ⟷ q) = (p' ⟷ q') := congr (congr_arg (fun p q => p ⟷ q) ep) eq

end lemmata

partial def resultSubsts {L : Q(Language.{u})} {k n : Q(ℕ)} (w : Q(Fin $k → SyntacticSubTerm $L $n)) :
    (p : Q(SyntacticSubFormula $L $k)) → MetaM ((res : Q(SyntacticSubFormula $L $n)) × Q(substs $w $p = $res))
  | ~q(⊤)                            => pure ⟨q(⊤), q(rfl)⟩
  | ~q(⊥)                            => pure ⟨q(⊥), q(rfl)⟩
  | ~q(rel (arity := $arity) $r $v)  => do
    let ⟨v', ve⟩ ← resultVectorOfResultFun (u := u) (v := u)
      (α := q(SyntacticSubTerm $L $k)) (β := q(SyntacticSubTerm $L $n))
      q(@SubTerm.substs $L ℕ $k $n $w) (SubTerm.Meta.resultSubsts w) arity v
    return ⟨q(rel $r $v'), q(substs_rel_of_eq $r $ve)⟩
  | ~q(nrel (arity := $arity) $r $v) => do
    let ⟨v', ve⟩ ← resultVectorOfResultFun (u := u) (v := u) (α := q(SyntacticSubTerm $L $k)) (β := q(SyntacticSubTerm $L $n))
      q(@SubTerm.substs $L ℕ $k $n $w) (SubTerm.Meta.resultSubsts w) arity v
    return ⟨q(nrel $r $v'), q(substs_nrel_of_eq $r $ve)⟩
  | ~q($p ⋏ $q)                      => do
    let ⟨pn, pe⟩ ← resultSubsts w p
    let ⟨qn, qe⟩ ← resultSubsts w q
    return ⟨q($pn ⋏ $qn), q(hom_and_eq_of_eq $pe $qe)⟩
  | ~q($p ⋎ $q)                      => do
    let ⟨pn, pe⟩ ← resultSubsts w p
    let ⟨qn, qe⟩ ← resultSubsts w q
    return ⟨q($pn ⋎ $qn), q(hom_or_eq_of_eq $pe $qe)⟩
  | ~q(∀' $p)                        => do
    let ⟨w', we⟩ ← resultVectorOfResultFun (u := u) (v := u) (α := q(SyntacticSubTerm $L $n)) (β := q(SyntacticSubTerm $L ($n + 1)))
      q(@SubTerm.bShift $L ℕ $n) SubTerm.Meta.resultBShift k w
    let ⟨p', pe⟩ ← resultSubsts (n := q($n + 1)) q(#0 :> $w') p
    return ⟨q(∀' $p'), q(substs_all_eq_of_eq $we $pe)⟩
  | ~q(∃' $p)                        => do
    let ⟨w', we⟩ ← resultVectorOfResultFun (u := u) (v := u) (α := q(SyntacticSubTerm $L $n)) (β := q(SyntacticSubTerm $L ($n + 1)))
      q(@SubTerm.bShift $L ℕ $n) SubTerm.Meta.resultBShift k w
    let ⟨p', pe⟩ ← resultSubsts (n := q($n + 1)) q(#0 :> $w') p
    return ⟨q(∃' $p'), q(substs_ex_eq_of_eq $we $pe)⟩
  | ~q(~$p)                          => do
    let ⟨pn, pe⟩ ← resultSubsts w p
    return ⟨q(~$pn), q(hom_neg_eq_of_eq $pe)⟩
  | ~q($p ⟶ $q)                      => do
    let ⟨pn, pe⟩ ← resultSubsts w p
    let ⟨qn, qe⟩ ← resultSubsts w q
    return ⟨q($pn ⟶ $qn), q(hom_imply_eq_of_eq $pe $qe)⟩
  | ~q($p ⟷ $q)                      => do
    let ⟨pn, pe⟩ ← resultSubsts w p
    let ⟨qn, qe⟩ ← resultSubsts w q
    return ⟨q($pn ⟷ $qn), q(hom_iff_eq_of_eq $pe $qe)⟩
  | ~q(substs (n := $l) $v $p)       => do
    let ⟨v', ve⟩ ← resultVectorOfResultFun (u := u) (v := u) (α := q(SyntacticSubTerm $L $k)) (β := q(SyntacticSubTerm $L $n))
      q(@SubTerm.substs $L ℕ $k $n $w) (SubTerm.Meta.resultSubsts w) l v
    let ⟨p', pe⟩ ← resultSubsts v' p
    return ⟨p', q(substs_substs_of_eq $ve $pe)⟩
  | ~q($p)                           => pure ⟨q(substs $w $p), q(rfl)⟩

elab "dbgresultSubsts" : term => do
  let L : Q(Language.{0}) := q(Language.oring)
  let k : Q(ℕ) := q(2)
  let n : Q(ℕ) := q(3)
  let p : Q(SyntacticSubFormula $L $k) := q(“#0 < #1 + 9 * &6 → (∀ #1 < #0 + 7)⟦&4, &3 + #0⟧ ”)
  let w : Q(Fin $k → SyntacticSubTerm $L $n) := q(![ᵀ“2”, ᵀ“&6”])
  let ⟨e, eq⟩ ← resultSubsts (u := levelZero) w p
  let dbgr := q(DbgResult.intro _ $e $eq)
  logInfo m! "⟦→ {w}⟧ {p} \n⟹ \n{e}"
  return dbgr

#eval dbgresultSubsts

partial def resultShift {L : Q(Language.{u})} {n : Q(ℕ)} : (p : Q(SyntacticSubFormula $L $n)) →
    MetaM ((res : Q(SyntacticSubFormula $L $n)) × Q(shift $p = $res))
  | ~q(⊤)                            => pure ⟨q(⊤), q(rfl)⟩
  | ~q(⊥)                            => pure ⟨q(⊥), q(rfl)⟩
  | ~q(rel (arity := $arity) $r $v)  => do
    let ⟨v', ve⟩ ← resultVectorOfResultFun (u := u) (v := u) (α := q(SyntacticSubTerm $L $n)) (β := q(SyntacticSubTerm $L $n))
      q(@SubTerm.shift $L $n) SubTerm.Meta.resultShift arity v
    return ⟨q(rel $r $v'), q(shift_rel_of_eq $r $ve)⟩
  | ~q(nrel (arity := $arity) $r $v) => do
    let ⟨v', ve⟩ ← resultVectorOfResultFun (u := u) (v := u) (α := q(SyntacticSubTerm $L $n)) (β := q(SyntacticSubTerm $L $n))
      q(@SubTerm.shift $L $n) SubTerm.Meta.resultShift arity v
    return ⟨q(nrel $r $v'), q(shift_nrel_of_eq $r $ve)⟩
  | ~q($p ⋏ $q)                      => do
    let ⟨pn, pe⟩ ← resultShift p
    let ⟨qn, qe⟩ ← resultShift q
    return ⟨q($pn ⋏ $qn), q(hom_and_eq_of_eq $pe $qe)⟩
  | ~q($p ⋎ $q)                      => do
    let ⟨pn, pe⟩ ← resultShift p
    let ⟨qn, qe⟩ ← resultShift q
    return ⟨q($pn ⋎ $qn), q(hom_or_eq_of_eq $pe $qe)⟩
  | ~q(∀' $p)                        => do
    let ⟨pn, e⟩ ← resultShift p
    return ⟨q(∀' $pn), q(shift_all_eq_of_eq $e)⟩
  | ~q(∃' $p)                        => do
    let ⟨pn, e⟩ ← resultShift p
    return ⟨q(∃' $pn), q(shift_ex_eq_of_eq $e)⟩
  | ~q(~$p)                          => do
    let ⟨pn, pe⟩ ← resultShift p
    return ⟨q(~$pn), q(hom_neg_eq_of_eq $pe)⟩
  | ~q($p ⟶ $q)                      => do
    let ⟨pn, pe⟩ ← resultShift p
    let ⟨qn, qe⟩ ← resultShift q
    return ⟨q($pn ⟶ $qn), q(hom_imply_eq_of_eq $pe $qe)⟩
  | ~q($p ⟷ $q)                      => do
    let ⟨pn, pe⟩ ← resultShift p
    let ⟨qn, qe⟩ ← resultShift q
    return ⟨q($pn ⟷ $qn), q(hom_iff_eq_of_eq $pe $qe)⟩
  | ~q(substs (n := $k) $w $p)       => do
    let ⟨w', we⟩ ← resultVectorOfResultFun (u := u) (v := u) (α := q(SyntacticSubTerm $L $n)) (β := q(SyntacticSubTerm $L $n))
      q(@SubTerm.shift $L $n) SubTerm.Meta.resultShift k w
    let ⟨p', pe⟩ ← resultShift (n := k) p
    let ⟨p'', p'e⟩ ← resultSubsts w' p'
    return ⟨p'', q(shift_substs_of_eq $we $pe $p'e)⟩
  | ~q($p)                           => pure ⟨q(shift $p), q(rfl)⟩

partial def resultFree {L : Q(Language.{u})} {n : Q(ℕ)} : (p : Q(SyntacticSubFormula $L ($n + 1))) →
    MetaM ((res : Q(SyntacticSubFormula $L $n)) × Q(free $p = $res))
  | ~q(⊤)                            => pure ⟨q(⊤), q(rfl)⟩
  | ~q(⊥)                            => pure ⟨q(⊥), q(rfl)⟩
  | ~q(rel (arity := $arity) $r $v)  => do
    let ⟨v', ve⟩ ← resultVectorOfResultFun (u := u) (v := u)
      (α := q(SyntacticSubTerm $L ($n + 1))) (β := q(SyntacticSubTerm $L $n))
      q(@SubTerm.free $L $n) SubTerm.Meta.resultFree arity v
    return ⟨q(rel $r $v'), q(free_rel_of_eq $r $ve)⟩
  | ~q(nrel (arity := $arity) $r $v) => do
    let ⟨v', ve⟩ ← resultVectorOfResultFun (u := u) (v := u)
      (α := q(SyntacticSubTerm $L ($n + 1))) (β := q(SyntacticSubTerm $L $n))
      q(@SubTerm.free $L $n) SubTerm.Meta.resultFree arity v
    let e : Q(SyntacticSubFormula $L $n) := q(nrel $r $v')
    return ⟨e, q(free_nrel_of_eq $r $ve)⟩
  | ~q($p ⋏ $q)                      => do
    let ⟨pn, pe⟩ ← resultFree p
    let ⟨qn, qe⟩ ← resultFree q
    return ⟨q($pn ⋏ $qn), q(hom_and_eq_of_eq $pe $qe)⟩
  | ~q($p ⋎ $q)                      => do
    let ⟨pn, pe⟩ ← resultFree p
    let ⟨qn, qe⟩ ← resultFree q
    return ⟨q($pn ⋎ $qn), q(hom_or_eq_of_eq $pe $qe)⟩
  | ~q(∀' $p)                        => do
    let ⟨pn, e⟩ ← resultFree (n := q($n + 1)) p
    return ⟨q(∀' $pn), q(free_all_eq_of_eq $e)⟩
  | ~q(∃' $p)                        => do
    let ⟨pn, e⟩ ← resultFree p
    return ⟨q(∃' $pn), q(free_ex_eq_of_eq $e)⟩
  | ~q(~$p)                          => do
    let ⟨pn, pe⟩ ← resultFree p
    return ⟨q(~$pn), q(hom_neg_eq_of_eq $pe)⟩
  | ~q($p ⟶ $q)                      => do
    let ⟨pn, pe⟩ ← resultFree p
    let ⟨qn, qe⟩ ← resultFree q
    return ⟨q($pn ⟶ $qn), q(hom_imply_eq_of_eq $pe $qe)⟩
  | ~q($p ⟷ $q)                      => do
    let ⟨pn, pe⟩ ← resultFree p
    let ⟨qn, qe⟩ ← resultFree q
    return ⟨q($pn ⟷ $qn), q(hom_iff_eq_of_eq $pe $qe)⟩
  | ~q(substs (n := $k) $w $p)       => do
    let ⟨p', pe⟩ ← resultShift (L := L) (n := k) p
    let ⟨w', we⟩ ← resultVectorOfResultFun (u := u) (v := u) (α := q(SyntacticSubTerm $L ($n + 1))) (β := q(SyntacticSubTerm $L $n))
      q(@SubTerm.free $L $n) SubTerm.Meta.resultShift k w
    let ⟨p'', p'e⟩ ← resultSubsts w' p'
    return ⟨p'', q(free_substs_of_eq $we $pe $p'e)⟩
  | ~q($p)                           => do
    return ⟨q(free $p), q(rfl)⟩
  | e => throwError m! "fail! {e} "

elab "dbgresultFree" : term => do
  let L : Q(Language.{0}) := q(Language.oring)
  let k : Q(ℕ) := q(2)
  let n : Q(ℕ) := q(3)
  let p : Q(SyntacticSubFormula $L ($k + 1)) := q(“#0 + #1 + #2 + #3 < &0 + &1 + &2 + &3”)
  let ⟨e, eq⟩ ← resultFree (L := L) (n := k) p
  let dbgr := q(DbgResult.intro _ $e $eq)
  logInfo m! "free {p} \n⟹ \n{e}"
  return dbgr

#eval dbgresultFree

partial def resultNeg {L : Q(Language.{u})} {n : Q(ℕ)} : (p : Q(SyntacticSubFormula $L $n)) →
    MetaM ((res : Q(SyntacticSubFormula $L $n)) × Q(~$p = $res))
  | ~q(⊤)                      => pure ⟨q(⊥), q(rfl)⟩
  | ~q(⊥)                      => pure ⟨q(⊤), q(rfl)⟩
  | ~q(rel $r $v)              => pure ⟨q(nrel $r $v), q(neg_rel $r _)⟩
  | ~q(nrel $r $v)             => pure ⟨q(rel $r $v), q(neg_nrel $r _)⟩  
  | ~q($p ⋏ $q)                => do
    let ⟨pn, pe⟩ ← resultNeg p
    let ⟨qn, qe⟩ ← resultNeg q
    return ⟨q($pn ⋎ $qn), q(neg_and_eq_of_eq $pe $qe)⟩
  | ~q($p ⋎ $q)                => do
    let ⟨pn, pe⟩ ← resultNeg p
    let ⟨qn, qe⟩ ← resultNeg q
    return ⟨q($pn ⋏ $qn), q(neg_or_eq_of_eq $pe $qe)⟩
  | ~q(∀' $p)                  => do
    let ⟨pn, e⟩ ← resultNeg p
    return ⟨q(∃' $pn), q(neg_all_eq_of_eq $e)⟩
  | ~q(∃' $p)                  => do
    let ⟨pn, e⟩ ← resultNeg p
    return ⟨q(∀' $pn), q(neg_ex_eq_of_eq $e)⟩
  | ~q(~$p)                    => do
    return ⟨q($p), q(neg_neg' $p)⟩
  | ~q($p ⟶ $q)                => do
    let ⟨qn, e⟩ ← resultNeg q
    return ⟨q($p ⋏ $qn), q(neg_imp_eq_of_eq $e)⟩
  | ~q($p ⟷ $q)                => do
    let ⟨pn, pe⟩ ← resultNeg p
    let ⟨qn, qe⟩ ← resultNeg q
    return ⟨q(($p ⋏ $qn) ⋎ ($q ⋏ $pn)), q(neg_iff_eq_of_eq $pe $qe)⟩
  | ~q(substs (n := $k) $w $p) => do
    let ⟨p', pe⟩ ← resultNeg (n := k) p
    let ⟨p'', p'e⟩ ← resultSubsts w p'
    return ⟨p'', q(neg_substs_of_eq $pe $p'e)⟩
  | ~q($p)                     => pure ⟨q(~$p), q(rfl)⟩


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
  | ~q(⊤)                            => pure ⟨q(⊤), q(rfl)⟩
  | ~q(⊥)                            => pure ⟨q(⊥), q(rfl)⟩
  | ~q(rel (arity := $arity) $r $v)  => do
    let ⟨v', ve⟩ ← resultVectorOfResult (u := u) (α := q(SyntacticSubTerm $L $n))
      (SubTerm.Meta.result tp) arity v
    return ⟨q(rel $r $v'), q(rel_congr $r $ve)⟩
  | ~q(nrel (arity := $arity) $r $v) => do
    let ⟨v', ve⟩ ← resultVectorOfResult (u := u) (α := q(SyntacticSubTerm $L $n))
      (SubTerm.Meta.result tp) arity v
    return ⟨q(nrel $r $v'), q(nrel_congr $r $ve)⟩
  | ~q($p ⋏ $q)                      => do
    let ⟨pn, pe⟩ ← result p
    let ⟨qn, qe⟩ ← result q
    return ⟨q($pn ⋏ $qn), q(and_congr $pe $qe)⟩
  | ~q($p ⋎ $q)                      => do
    let ⟨pn, pe⟩ ← result p
    let ⟨qn, qe⟩ ← result q
    return ⟨q($pn ⋎ $qn), q(or_congr $pe $qe)⟩
  | ~q(∀' $p)                        => do
    let ⟨pn, pe⟩ ← result p
    return ⟨q(∀' $pn), q(all_congr $pe)⟩
  | ~q(∃' $p)                        => do
    let ⟨pn, pe⟩ ← result p
    return ⟨q(∃' $pn), q(ex_congr $pe)⟩
  | ~q(free $p)                      => do
    let ⟨pn, e⟩ ← result (L := L) (n := q($n + 1)) p
    let ⟨pnn, ee⟩ ← resultFree (L := L) (n := n) pn
    return ⟨q($pnn), q(free_congr_eq $e $ee)⟩
  | ~q(substs (n := $k) $w $p)       => do
    let ⟨p', pe⟩ ← result (L := L) (n := k) p
    let ⟨w', we⟩ ← resultVectorOfResult (u := u) (α := q(SyntacticSubTerm $L $n))
      (SubTerm.Meta.result tp) k w
    let ⟨n, e⟩ ← resultSubsts (L := L) (n := n) w' p'
    return ⟨q($n), q(substs_congr_eq $we $pe $e)⟩
  | ~q(shift $p)                     => do
    let ⟨pn, e⟩ ← result (L := L) (n := n) p
    let ⟨pnn, ee⟩ ← resultShift (L := L) (n := n) pn
    return ⟨q($pnn), q(shift_congr_eq $e $ee)⟩
  | ~q(~$p)                          => do
    let ⟨pn, e⟩ ← result p
    if unfoldOpt UnfoldOption.neg then
      let ⟨pnn, ee⟩ ← resultNeg pn
      return ⟨q($pnn), q(neg_congr_eq $e $ee)⟩
    else return ⟨q(~$pn), q(neg_congr $e)⟩
  | ~q($p ⟶ $q)                     => do
    let ⟨pn, pe⟩ ← result (L := L) (n := n) p
    let ⟨qn, qe⟩ ← result (L := L) (n := n) q    
    if unfoldOpt UnfoldOption.imply then
      if unfoldOpt UnfoldOption.neg then
        let ⟨pnn, pee⟩ ← resultNeg pn
        return ⟨q($pnn ⋎ $qn), q(imp_eq_of_eq $pe $qe $pee)⟩
      return ⟨q(~$pn ⋎ $qn), q(imply_congr $pe $qe)⟩
    else return ⟨q($pn ⟶ $qn), q(imply_congr $pe $qe)⟩
  | ~q($p ⟷ $q)                     => do
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
  | ~q($p)                           => do
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
    MetaM $ (res : Q(SyntacticFormula $L)) × Q(substs ![$s] $p = $res) :=
  resultSubsts (L := L) (n := q(0)) q(![$s]) p

partial def resultSubst₀List {L : Q(Language.{u})} (v : List Q(SyntacticTerm $L)) (p : Q(SyntacticSubFormula $L 1)) :
    MetaM $ (res : List Q(SyntacticFormula $L)) × Q(List.map (SubFormula.substs ![·] $p) $(toQList (u := u) v) = $(toQList (u := u) res)) :=
  funResultList (u := u) (α := q(SyntacticTerm $L)) q((substs ![·] $p)) (resultSubst₀ p) v


elab "dbgResult" : tactic => do
  let goalType ← Elab.Tactic.getMainTarget
  let some ⟨.succ u, ty⟩ ← checkSortQ' goalType | throwError "error: not a type"
  let ~q(DbgResult (SyntacticSubFormula $L $n) $p) := ty | throwError "error: not a type"
  let p : Q(SyntacticSubFormula $L $n) ← withReducible <| whnf p

  let ⟨pn, e⟩ ← result SubTerm.Meta.NumeralUnfoldOption.none (unfoldOfList []) (L := L) (n := n) p
  logInfo m!"{p}\n ⟹\n {pn}"
  -- logInfo m!"e = {e}"
  let c : Q(DbgResult (SyntacticSubFormula $L $n) $p) := (q(DbgResult.intro ($p) $pn $e) : Expr)
  Lean.Elab.Tactic.closeMainGoal c

example {t : SyntacticSubTerm Language.oring 3} : DbgResult (SyntacticSubFormula Language.oring 12)
    $ shift “3 < #4 ↔ ∀ !(shift $ substs ![&99, &6] “∀ (ᵀ!t) + (#0 * 8) < &7 + #1 + (#3 + 6)”)” :=
  by dbgResult

example : DbgResult (SyntacticSubFormula Language.oring 3)
    $ free “3 * 4 = &6” :=
  by dbgResult

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

def headEx {t} {p : SyntacticSubFormula L 1} (d : DerivationList (G ++ [⟦↦ t⟧ p])) :
    DerivationList ((∃' p) :: G) :=
  (DerivationCutRestricted.ex G.toFinset t p (d.cast $ by ext; simp[or_comm])).cast (by simp)

def headExInstances {v : List (SyntacticTerm L)} {p : SyntacticSubFormula L 1} (d : DerivationList (G ++ v.map (⟦↦ ·⟧ p))) :
    DerivationList ((∃' p) :: G) :=
  (DerivationCutRestricted.exOfInstances (Γ := G.toFinset) v p (d.cast $ by ext x; simp[or_comm])).cast (by simp)

def headExInstancesOfEq' {v : List (SyntacticTerm L)} {p : SyntacticSubFormula L 1} {pi : List (SyntacticFormula L)}
  (ev : v.map (⟦↦ ·⟧ p) = pi) (d : DerivationList (G ++ pi ++ [∃' p])) :
    DerivationList ((∃' p) :: G) :=
  (DerivationCutRestricted.exOfInstances' (Γ := G.toFinset) v p
    (d.cast $ by
      simp[ev, Finset.insert_eq];
      rw[Finset.union_comm {∃' p}, ←Finset.union_assoc, Finset.union_comm pi.toFinset])).cast (by simp)

def headExInstancesOfEq {v : List (SyntacticTerm L)} {p : SyntacticSubFormula L 1} {pi : List (SyntacticFormula L)}
  (ev : v.map (⟦↦ ·⟧ p) = pi) (d : DerivationList (G ++ pi)) :
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
  (ev : Q(List.map (⟦↦ ·⟧ $p) $(toQList (u := u) v) = $(toQList (u := u) pi)))
  (d : DerivationListQ L dfunc drel (G ++ pi ++ [(q(∃' $p) : Q(SyntacticFormula $L))])) :
    DerivationListQ L dfunc drel (q(∃' $p) :: G) :=
  -- let x : Q(DerivationList $ $(toQList (u := u) (G ++ pi))) := d
  let x : Q(DerivationList $ $(toQList (u := u) G) ++ $(toQList (u := u) pi) ++ [∃' $p]) := d
  q(DerivationList.headExInstancesOfEq' $ev $x)

def headEx (v : List Q(SyntacticTerm $L)) (p : Q(SyntacticSubFormula $L 1)) (pi : List Q(SyntacticFormula $L))
  (ev : Q(List.map (⟦↦ ·⟧ $p) $(toQList (u := u) v) = $(toQList (u := u) pi)))
  (d : DerivationListQ L dfunc drel (G ++ pi)) :
    DerivationListQ L dfunc drel (q(∃' $p) :: G) :=
  -- let x : Q(DerivationList $ $(toQList (u := u) (G ++ pi))) := d
  let x : Q(DerivationList $ $(toQList (u := u) G) ++ $(toQList (u := u) pi)) := d
  q(DerivationList.headExInstancesOfEq $ev $x)

/-
def headEx (v : List Q(SyntacticTerm $L)) (p : Q(SyntacticSubFormula $L 1)) (pi : List Q(SyntacticFormula $L))
  (ev : Q(List.map (⟦↦ ·⟧ $p) $(toQList (u := u) v) = $(toQList (u := u) pi)))
  (d : DerivationListQ L dfunc drel (G ++ pi)) :
    DerivationListQ L dfunc drel (q(∃' $p) :: G) :=
  -- let x : Q(DerivationList $ $(toQList (u := u) (G ++ pi))) := d
  let x : Q(DerivationList $ $(toQList (u := u) G) ++ $(toQList (u := u) pi)) := d
  let x : Q(DerivationList $ $(toQList (u := u) G) ++ List.map (⟦↦ ·⟧ $p) $(toQList (u := u) v)) :=
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

example : Derivation₁ (L := oring) “&0 < 3 → ∃ &0 < #0” := by proveDerivation₁ [ᵀ“3”]

example : Derivation₁ (L := oring) “&0 < 4 + &1 → ∃ ∃ ∃ #0 < #1 + #2” := by proveDerivation₁ 32 [&1, ᵀ“4”, &0]

example (_ : Derivation₁ (L := oring) “0 < 4 + 9”) : Derivation₁ (L := oring) “⊤ ∧ (∃ 0 < 4 + #0)”  := by proveDerivation₁ [ᵀ“9”]

example : Derivation₁ (L := oring) “0 < 4 + 9 → (∃ 0 < 4 + #0)”  := by proveDerivation₁ [ᵀ“9”]

example : DerivationList (L := oring) [“¬(0 + &9 < 2)”, “∃ #0 < 2”] := by simp; proveDerivationList [ᵀ“0 + &9”]

end
-/

end DerivationListQ

end FirstOrder
