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

lemma substs_ball_eq_of_eq {p q : SyntacticSubFormula L (k + 1)} {w' p' q'}
  (hw : SubTerm.bShift ∘ w = w') (hp : substs (#0 :> w') p = p') (hq : substs (#0 :> w') q = q') :
    substs w (∀[p] q) = ∀[p'] q' := by simp[←hw, ←hp, ←hq, substs_ball]

lemma substs_bex_eq_of_eq {p : SyntacticSubFormula L (k + 1)} {w' p' q'}
  (hw : SubTerm.bShift ∘ w = w') (hp : substs (#0 :> w') p = p') (hq : substs (#0 :> w') q = q') :
    substs w (∃[p] q) = ∃[p'] q' := by simp[←hw, ←hp, ←hq, substs_bex]

lemma substs_substs_of_eq {l} {v : Fin l → SyntacticSubTerm L k} {p : SyntacticSubFormula L l} {v' p'}
  (hw : SubTerm.substs w ∘ v = v') (hp : substs v' p = p') :
    substs w (substs v p) = p' := by
  simp[←hw, ←hp, substs_substs]

lemma substs_finitary_of_eq {l} (o : Finitary L l) {v : Fin l → SyntacticSubTerm L k} {v'}
  (h : SubTerm.substs w ∘ v = v') :
    substs w (o.operator v) = o.operator v' := by
  simp[←h, Operator.substs_operator o w v]; rfl

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

lemma free_ball_eq_of_eq {p q : SyntacticSubFormula L (n + 1 + 1)} {p' q'}
  (hp : free p = p') (hq : free q = q'):
    free (∀[p] q) = ∀[p'] q' := by simp[←hp, ←hq]

lemma free_bex_eq_of_eq {p q : SyntacticSubFormula L (n + 1 + 1)} {p' q'}
  (hp : free p = p') (hq : free q = q') :
    free (∃[p] q) = ∃[p'] q' := by simp[←hp, ←hq]

lemma free_substs_of_eq {k} {w : Fin k → SyntacticSubTerm L (n + 1)} {p : SyntacticSubFormula L k} {w' p' p''}
  (hw : SubTerm.free ∘ w = w') (hp : shift p = p') (hp' : substs w' p' = p''):
    free (substs w p) = p'' := by
  simp[←hw, ←hp, ←hp', free_substs, Function.comp]

lemma free_finitary_of_eq {k} (o : Finitary L k)
  {v : Fin k → SyntacticSubTerm L (n + 1)} {v'} (h : SubTerm.free ∘ v = v') :
    free (o.operator v) = o.operator v' := by
  simp[←h, Operator.free_operator]; rfl

end free

section fix

lemma fix_rel_of_eq {k} (r : L.rel k) {v : Fin k → SyntacticSubTerm L n} {v'} (h : SubTerm.fix ∘ v = v') :
    fix (rel r v) = rel r v' := by
  simp[←h]; rfl

lemma fix_nrel_of_eq {k} (r : L.rel k) {v : Fin k → SyntacticSubTerm L n} {v'} (h : SubTerm.fix ∘ v = v') :
    fix (nrel r v) = nrel r v' := by
  simp[←h]; rfl

lemma fix_all_eq_of_eq {p : SyntacticSubFormula L (n + 1)} {p'} (h : fix p = p') :
    fix (∀' p) = ∀' p' := by simp[←h]

lemma fix_ex_eq_of_eq {p : SyntacticSubFormula L (n + 1)} {p'} (h : fix p = p') :
    fix (∃' p) = ∃' p' := by simp[←h]

lemma fix_imply_eq_of_eq {p q : SyntacticSubFormula L n} {p' q'} (hp : fix p = p') (hq : fix q = q') :
    fix (p ⟶ q) = p' ⟶ q' := by simp[←hp, ←hq]

lemma fix_iff_eq_of_eq {p q : SyntacticSubFormula L n} {p' q'} (hp : fix p = p') (hq : fix q = q') :
    fix (p ⟷ q) = p' ⟷ q' := by simp[←hp, ←hq]

lemma fix_ball_eq_of_eq {p q : SyntacticSubFormula L (n + 1)} {p'} (hp : fix p = p') (hq : fix q = q') :
    fix (∀[p] q) = ∀[p'] q' := by simp[←hp, ←hq]

lemma fix_bex_eq_of_eq {p : SyntacticSubFormula L (n + 1)} {p'} (hp : fix p = p') (hq : fix q = q') :
    fix (∃[p] q) = ∃[p'] q' := by simp[←hp, ←hq]

lemma fix_substs_of_eq {k} {p : SyntacticSubFormula L k} {w : Fin k → SyntacticSubTerm L n} {p' p'' w' w'' i}
  (ht : fix p = p') (hw : SubTerm.fix ∘ w = w') (hi : Fin.last n = i) (hw' : w' <: #i = w'') (hp' : substs w'' p' = p''):
    fix (substs w p) = p'' := by
  simp[←ht, ←hw, ←hi, ←hw', ←hp', shift, map, fix, substs, bind_bind, Function.comp]; congr
  · funext x; cases x <;> simp

lemma fix_finitary_of_eq {k} (o : Finitary L k) {v : Fin k → SyntacticSubTerm L n} {v'} (h : SubTerm.fix ∘ v = v') :
    fix (o.operator v) = o.operator v' := by
  simp[←h, Operator.fix_operator]; rfl

end fix

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

lemma shift_ball_eq_of_eq {p q : SyntacticSubFormula L (n + 1)} {p' q'} (hp : shift p = p') (hq : shift q = q') :
    shift (∀[p] q) = ∀[p'] q' := by simp[←hp, ←hq]

lemma shift_bex_eq_of_eq {p q : SyntacticSubFormula L (n + 1)} {p' q'} (hp : shift p = p') (hq : shift q = q') :
    shift (∃[p] q) = ∃[p'] q' := by simp[←hp, ←hq]

lemma shift_substs_of_eq {k} {w : Fin k → SyntacticSubTerm L n} {p : SyntacticSubFormula L k} {w' p' p''}
  (hw : SubTerm.shift ∘ w = w') (hp : shift p = p') (hp' : substs w' p' = p'') :
    shift (substs w p) = p'' := by
  simp[←hw, ←hp, ←hp', shift_substs, Function.comp]

lemma shift_finitary_of_eq {k} (o : Finitary L k) {v : Fin k → SyntacticSubTerm L n} {v'} (h : SubTerm.shift ∘ v = v') :
    shift (o.operator v) = o.operator v' := by
  simp[←h, Operator.shift_operator]; rfl

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

lemma neg_ball_eq_of_eq {p q : SyntacticSubFormula L (n + 1)} {q'} (hq : ~q = q') :
    ~(∀[p] q) = ∃[p] q' := by simp[←hq]

lemma neg_bex_eq_of_eq {p q : SyntacticSubFormula L (n + 1)} {q'} (hq : ~q = q') :
    ~(∃[p] q) = ∀[p] q' := by simp[←hq]

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

lemma ball_congr {p p' q q' : SyntacticSubFormula L (n + 1)} (hp : p = p') (hq : q = q') :
    (∀[p] q) = (∀[p'] q') := by simp[hp, hq]

lemma bex_congr {p p' q q' : SyntacticSubFormula L (n + 1)} (hp : p = p') (hq : q = q') :
    (∃[p] q) = (∃[p'] q') := by simp[hp, hq]

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

lemma rel_eq_substs_rel_of_eq {k} {s : Term L μ} (r : L.rel k) {v : Fin k → Term L μ} {v' : Fin k → SubTerm L μ 1}
  (h : ∀ i, v i = SubTerm.substs ![s] (v' i)) : rel r v = ⟦↦ s⟧ (rel r v') := by simp[substs_rel, ←h]

lemma nrel_eq_substs_nrel_of_eq {k} {s : Term L μ} (r : L.rel k) {v : Fin k → Term L μ} {v' : Fin k → SubTerm L μ 1}
  (h : ∀ i, v i = SubTerm.substs ![s] (v' i)) : nrel r v = ⟦↦ s⟧ (nrel r v') := by simp[substs_nrel, ←h]

lemma finitary_congr {k} (o : Finitary L k) {v v' : Fin k → SubTerm L μ n} (h : v = v') :
    o.operator v = o.operator v' := congr_arg _ (by simp[h])

lemma eq_substs_and_of_eq {s : Term L μ} {p q : Formula L μ} {p' q' : SubFormula L μ 1}
  (hp : p = ⟦↦ s⟧ p') (hq : q = ⟦↦ s⟧ q') : p ⋏ q = ⟦↦ s⟧ (p' ⋏ q') := by simp[←hp, ←hq]

lemma eq_substs_or_of_eq {s : Term L μ} {p q : Formula L μ} {p' q' : SubFormula L μ 1}
  (hp : p = ⟦↦ s⟧ p') (hq : q = ⟦↦ s⟧ q') : p ⋎ q = ⟦↦ s⟧ (p' ⋎ q') := by simp[←hp, ←hq]

lemma all_eq_substs_all_of_eq {s : SyntacticTerm L} {s' p p' q q' q''}
  (hp : free p = p') (hs : s.shift = s') (findq : p' = ⟦↦ s'⟧ q)
  (hq : fix q = q') (hq' : ⟦→ ![#1, #0]⟧ q' = q'') : ∀' p = ⟦↦ s⟧ (∀' q'') := by
  have hp : p = fix p' := by simpa using congr_arg fix hp
  simp[hp, ←hs, findq, ←hq, ←hq', substs, fix, bind_bind, Fin.eq_zero]; congr
  · funext; simp[SubTerm.shift, SubTerm.bShift, SubTerm.map, SubTerm.bind_bind, Matrix.empty_eq]
  · funext x; cases x <;> simp

lemma ex_eq_substs_ex_of_eq {s : SyntacticTerm L} {s' p p' q q' q''}
  (hp : free p = p') (hs : s.shift = s') (findq : p' = ⟦↦ s'⟧ q)
  (hq : fix q = q') (hq' : ⟦→ ![#1, #0]⟧ q' = q'') : ∃' p = ⟦↦ s⟧ (∃' q'') := by
  have hp : p = fix p' := by simpa using congr_arg fix hp
  simp[hp, ←hs, findq, ←hq, ←hq', substs, fix, bind_bind, Fin.eq_zero]; congr
  · funext; simp[SubTerm.shift, SubTerm.bShift, SubTerm.map, SubTerm.bind_bind, Matrix.empty_eq]
  · funext x; cases x <;> simp

lemma eq_substs_neg_of_eq {s : Term L μ} {p : Formula L μ} {p' : SubFormula L μ 1}
  (hp : p = ⟦↦ s⟧ p') : ~p = ⟦↦ s⟧ (~p') := by simp[←hp]

lemma eq_substs_imply_of_eq {s : Term L μ} {p q : Formula L μ} {p' q' : SubFormula L μ 1}
  (hp : p = ⟦↦ s⟧ p') (hq : q = ⟦↦ s⟧ q') :
    p ⟶ q = ⟦↦ s⟧ (p' ⟶ q') := by simp[←hp, ←hq]

lemma eq_substs_iff_of_eq {s : Term L μ} {p q : Formula L μ} {p' q' : SubFormula L μ 1}
  (hp : p = ⟦↦ s⟧ p') (hq : q = ⟦↦ s⟧ q') :
    p ⟷ q = ⟦↦ s⟧ (p' ⟷ q') := by simp[←hp, ←hq]

lemma eq_substs_substs_of_eq {k} {s : Term L μ} (p : SubFormula L μ k) {v : Fin k → Term L μ} {v' : Fin k → SubTerm L μ 1}
  (h : ∀ i, v i = SubTerm.substs ![s] (v' i)) :
    substs v p = ⟦↦ s⟧ (substs v' p) := by simp[substs_substs, Function.comp, ←h]

lemma eq_substs_substs_nil (v) (s : Term L μ) {p : Formula L μ} {p'} (ht : substs v p = p') :
  p = substs ![s] p' := by simp[←ht, substs_substs]

lemma univClosure_eq_of_eq {n} {p : SubFormula L μ (n + 1)} {q} (h : univClosure (∀' p) = q) :
  univClosure p = q := by simp[←h]

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
  | ~q(∀[$p] $q)                     => do
    let ⟨w', we⟩ ← resultVectorOfResultFun (u := u) (v := u) (α := q(SyntacticSubTerm $L $n)) (β := q(SyntacticSubTerm $L ($n + 1)))
      q(@SubTerm.bShift $L ℕ $n) SubTerm.Meta.resultBShift k w
    let ⟨p', pe⟩ ← resultSubsts (n := q($n + 1)) q(#0 :> $w') p
    let ⟨q', qe⟩ ← resultSubsts (n := q($n + 1)) q(#0 :> $w') q
    return ⟨q(∀[$p'] $q'), q(substs_ball_eq_of_eq $we $pe $qe)⟩
  | ~q(∃[$p] $q)                     => do
    let ⟨w', we⟩ ← resultVectorOfResultFun (u := u) (v := u) (α := q(SyntacticSubTerm $L $n)) (β := q(SyntacticSubTerm $L ($n + 1)))
      q(@SubTerm.bShift $L ℕ $n) SubTerm.Meta.resultBShift k w
    let ⟨p', pe⟩ ← resultSubsts (n := q($n + 1)) q(#0 :> $w') p
    let ⟨q', qe⟩ ← resultSubsts (n := q($n + 1)) q(#0 :> $w') q
    return ⟨q(∃[$p'] $q'), q(substs_bex_eq_of_eq $we $pe $qe)⟩
  | ~q(substs (n := $l) $v $p)       => do
    let ⟨v', ve⟩ ← resultVectorOfResultFun (u := u) (v := u) (α := q(SyntacticSubTerm $L $k)) (β := q(SyntacticSubTerm $L $n))
      q(@SubTerm.substs $L ℕ $k $n $w) (SubTerm.Meta.resultSubsts w) l v
    let ⟨p', pe⟩ ← resultSubsts v' p
    return ⟨p', q(substs_substs_of_eq $ve $pe)⟩
  | ~q(Operator.operator (ι := Fin $arity) $o $v)  => do
    let ⟨v', ve⟩ ← resultVectorOfResultFun (u := u) (v := u)
      (α := q(SyntacticSubTerm $L $k)) (β := q(SyntacticSubTerm $L $n))
      q(@SubTerm.substs $L ℕ $k $n $w) (SubTerm.Meta.resultSubsts w) arity v
    return ⟨q(Operator.operator $o $v'), q(substs_finitary_of_eq $o $ve)⟩
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
  | ~q(∀[$p] $q)                     => do
    let ⟨p', pe⟩ ← resultShift p
    let ⟨q', qe⟩ ← resultShift q
    return ⟨q(∀[$p'] $q'), q(shift_ball_eq_of_eq $pe $qe)⟩
  | ~q(∃[$p] $q)                     => do
    let ⟨p', pe⟩ ← resultShift p
    let ⟨q', qe⟩ ← resultShift q
    return ⟨q(∃[$p'] $q'), q(shift_bex_eq_of_eq $pe $qe)⟩
  | ~q(substs (n := $k) $w $p)       => do
    let ⟨w', we⟩ ← resultVectorOfResultFun (u := u) (v := u) (α := q(SyntacticSubTerm $L $n)) (β := q(SyntacticSubTerm $L $n))
      q(@SubTerm.shift $L $n) SubTerm.Meta.resultShift k w
    let ⟨p', pe⟩ ← resultShift (n := k) p
    let ⟨p'', p'e⟩ ← resultSubsts w' p'
    return ⟨p'', q(shift_substs_of_eq $we $pe $p'e)⟩
  | ~q(Operator.operator (ι := Fin $arity) $o $v)  => do
    let ⟨v', ve⟩ ← resultVectorOfResultFun (u := u) (v := u) (α := q(SyntacticSubTerm $L $n)) (β := q(SyntacticSubTerm $L $n))
      q(@SubTerm.shift $L $n) SubTerm.Meta.resultShift arity v
    return ⟨q(Operator.operator $o $v'), q(shift_finitary_of_eq $o $ve)⟩
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
  | ~q(∀[$p] $q)                     => do
    let ⟨p', pe⟩ ← resultFree (n := q($n + 1)) p
    let ⟨q', qe⟩ ← resultFree (n := q($n + 1)) q
    return ⟨q(∀[$p'] $q'), q(free_ball_eq_of_eq $pe $qe)⟩
  | ~q(∃' $p)                        => do
    let ⟨pn, e⟩ ← resultFree p
    return ⟨q(∃' $pn), q(free_ex_eq_of_eq $e)⟩
  | ~q(substs (n := $k) $w $p)       => do
    let ⟨p', pe⟩ ← resultShift (L := L) (n := k) p
    let ⟨w', we⟩ ← resultVectorOfResultFun (u := u) (v := u) (α := q(SyntacticSubTerm $L ($n + 1))) (β := q(SyntacticSubTerm $L $n))
      q(@SubTerm.free $L $n) SubTerm.Meta.resultShift k w
    let ⟨p'', p'e⟩ ← resultSubsts w' p'
    return ⟨p'', q(free_substs_of_eq $we $pe $p'e)⟩
  | ~q(Operator.operator (ι := Fin $arity) $o $v)  => do
    let ⟨v', ve⟩ ← resultVectorOfResultFun (u := u) (v := u)
      (α := q(SyntacticSubTerm $L ($n + 1))) (β := q(SyntacticSubTerm $L $n))
      q(@SubTerm.free $L $n) SubTerm.Meta.resultFree arity v
    return ⟨q(Operator.operator $o $v'), q(free_finitary_of_eq $o $ve)⟩
  | ~q($p)                           => do
    return ⟨q(free $p), q(rfl)⟩

elab "dbgresultFree" : term => do
  let L : Q(Language.{0}) := q(Language.oring)
  let k : Q(ℕ) := q(2)
  let p : Q(SyntacticSubFormula $L ($k + 1)) := q(“#0 + #1 + #2 + #3 < &0 + &1 + &2 + &3”)
  let ⟨e, eq⟩ ← resultFree (L := L) (n := k) p
  let dbgr := q(DbgResult.intro _ $e $eq)
  logInfo m! "free {p} \n⟹ \n{e}"
  return dbgr

#eval dbgresultFree

#check fix_substs_of_eq

partial def resultFix {L : Q(Language.{u})} {n : Q(ℕ)} : (p : Q(SyntacticSubFormula $L $n)) →
    MetaM ((res : Q(SyntacticSubFormula $L ($n + 1))) × Q(fix $p = $res))
  | ~q(⊤)                            => pure ⟨q(⊤), q(rfl)⟩
  | ~q(⊥)                            => pure ⟨q(⊥), q(rfl)⟩
  | ~q(rel (arity := $arity) $r $v)  => do
    let ⟨v', ve⟩ ← resultVectorOfResultFun (u := u) (v := u)
      (α := q(SyntacticSubTerm $L $n)) (β := q(SyntacticSubTerm $L ($n + 1)))
      q(@SubTerm.fix $L $n) SubTerm.Meta.resultFix arity v
    return ⟨q(rel $r $v'), q(fix_rel_of_eq $r $ve)⟩
  | ~q(nrel (arity := $arity) $r $v) => do
    let ⟨v', ve⟩ ← resultVectorOfResultFun (u := u) (v := u)
      (α := q(SyntacticSubTerm $L $n)) (β := q(SyntacticSubTerm $L ($n + 1)))
      q(@SubTerm.fix $L $n) SubTerm.Meta.resultFix arity v
    return ⟨q(nrel $r $v'), q(fix_nrel_of_eq $r $ve)⟩
  | ~q($p ⋏ $q)                      => do
    let ⟨pn, pe⟩ ← resultFix p
    let ⟨qn, qe⟩ ← resultFix q
    return ⟨q($pn ⋏ $qn), q(hom_and_eq_of_eq $pe $qe)⟩
  | ~q($p ⋎ $q)                      => do
    let ⟨pn, pe⟩ ← resultFix p
    let ⟨qn, qe⟩ ← resultFix q
    return ⟨q($pn ⋎ $qn), q(hom_or_eq_of_eq $pe $qe)⟩
  | ~q(∀' $p)                        => do
    let ⟨pn, e⟩ ← resultFix (n := q($n + 1)) p
    return ⟨q(∀' $pn), q(fix_all_eq_of_eq $e)⟩
  | ~q(∃' $p)                        => do
    let ⟨pn, e⟩ ← resultFix (n := q($n + 1)) p
    return ⟨q(∃' $pn), q(fix_ex_eq_of_eq $e)⟩
  | ~q(~$p)                          => do
    let ⟨pn, pe⟩ ← resultFix p
    return ⟨q(~$pn), q(hom_neg_eq_of_eq $pe)⟩
  | ~q($p ⟶ $q)                      => do
    let ⟨pn, pe⟩ ← resultFix p
    let ⟨qn, qe⟩ ← resultFix q
    return ⟨q($pn ⟶ $qn), q(hom_imply_eq_of_eq $pe $qe)⟩
  | ~q($p ⟷ $q)                      => do
    let ⟨pn, pe⟩ ← resultFix p
    let ⟨qn, qe⟩ ← resultFix q
    return ⟨q($pn ⟷ $qn), q(hom_iff_eq_of_eq $pe $qe)⟩
  | ~q(∀[$p] $q)                        => do
    let ⟨p', pe⟩ ← resultFix (n := q($n + 1)) p
    let ⟨q', qe⟩ ← resultFix (n := q($n + 1)) q
    return ⟨q(∀[$p'] $q'), q(fix_ball_eq_of_eq $pe $qe)⟩
  | ~q(∃[$p] $q)                        => do
    let ⟨p', pe⟩ ← resultFix (n := q($n + 1)) p
    let ⟨q', qe⟩ ← resultFix (n := q($n + 1)) q
    return ⟨q(∃[$p'] $q'), q(fix_bex_eq_of_eq $pe $qe)⟩
  | ~q(substs (n := $k) $w $p)       => do
    let ⟨p', hp⟩ ← resultFix (L := L) (n := k) p
    let ⟨w', hw⟩ ← resultVectorOfResultFun (u := u) (v := u)
      (α := q(SyntacticSubTerm $L $n)) (β := q(SyntacticSubTerm $L ($n + 1)))
      q(@SubTerm.fix $L $n) SubTerm.Meta.resultFix k w
    let some nval := (←whnf n).natLit? | throwError f!"Fail: natLit: {n}"
    let z : Q(Fin ($n + 1)) ← Lean.Expr.ofNat q(Fin ($n + 1)) nval
    let hz : Q(Fin.last $n = $z) := (q(@rfl (Fin ($n + 1)) $z) : Expr)
    let ⟨w'', hw'⟩ ← vectorAppend k w' q(#$z)
    let ⟨p'', hp'⟩ ← resultSubsts w'' p'
    return ⟨p'', q(fix_substs_of_eq $hp $hw $hz $hw' $hp')⟩
  | ~q(Operator.operator (ι := Fin $arity) $o $v)  => do
    let ⟨v', ve⟩ ← resultVectorOfResultFun (u := u) (v := u)
      (α := q(SyntacticSubTerm $L $n)) (β := q(SyntacticSubTerm $L ($n + 1)))
      q(@SubTerm.fix $L $n) SubTerm.Meta.resultFix arity v
    return ⟨q(Operator.operator $o $v'), q(fix_finitary_of_eq $o $ve)⟩
  | ~q($p)                           => do
    return ⟨q(fix $p), q(rfl)⟩
  | e => throwError m! "fail! {e} "

elab "dbgResultFix'" : term => do
  let L : Q(Language.{0}) := q(Language.oring)
  let n : Q(ℕ) := q(5)
  let p : Q(SyntacticSubFormula $L $n) := q(“#0 + #1 + #2 + #3 < &0 + &1 + &2 + &3 → (#0 = #1)⟦0, &5⟧ ”)
  logInfo m! "{p}"
  let ⟨e, eq⟩ ← resultFix (L := L) (n := n) p
  let dbgr := q(DbgResult.intro _ $e $eq)
  logInfo m! "free {p} \n⟹ \n{e}"
  return dbgr

#eval dbgResultFix'

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
  | ~q(∀[$p] $q)               => do
    let ⟨q', qe⟩ ← resultNeg q
    return ⟨q(∃[$p] $q'), q(neg_ball_eq_of_eq $qe)⟩
  | ~q(∃[$p] $q)               => do
    let ⟨q', qe⟩ ← resultNeg q
    return ⟨q(∀[$p] $q'), q(neg_bex_eq_of_eq $qe)⟩
  | ~q(substs (n := $k) $w $p) => do
    let ⟨p', pe⟩ ← resultNeg (n := k) p
    let ⟨p'', p'e⟩ ← resultSubsts w p'
    return ⟨p'', q(neg_substs_of_eq $pe $p'e)⟩
  | ~q($p)                     => pure ⟨q(~$p), q(rfl)⟩

partial def resultUnivClosure {L : Q(Language.{u})} {n : Q(ℕ)} (p : Q(SyntacticSubFormula $L $n)) :
    MetaM ((res : Q(SyntacticFormula $L)) × Q(univClosure $p = $res)) :=
  match n with
  | ~q(0)      => return ⟨p, q(rfl)⟩
  | ~q($n + 1) => do
    have p : Q(SyntacticSubFormula $L ($n + 1)) := p
    let ⟨p', hp⟩ ← resultUnivClosure (u := u) (L := L) (n := n) q(∀' $p)
    let h : Q(univClosure $p = $p') := q(univClosure_eq_of_eq (p := $p) (q := $p') $hp)
    return ⟨p', h⟩

inductive UnfoldOption
  | neg
  | imply
  | iff
  | ball
  | bex
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
  | ~q(∀[$p] $q)                     => do
    let ⟨p', pe⟩ ← result p
    let ⟨q', qe⟩ ← result q
    if unfoldOpt UnfoldOption.ball then
      return ⟨q(∀'($p' ⟶ $q')), q(ball_congr $pe $qe)⟩
    else return ⟨q(∀[$p'] $q'), q(ball_congr $pe $qe)⟩
  | ~q(∃[$p] $q)                     => do
    let ⟨p', pe⟩ ← result p
    let ⟨q', qe⟩ ← result q
    if unfoldOpt UnfoldOption.bex then
      return ⟨q(∃'($p' ⋏ $q')), q(bex_congr $pe $qe)⟩
    else return ⟨q(∃[$p'] $q'), q(bex_congr $pe $qe)⟩
  | ~q(Operator.operator (ι := Fin $arity) $o $v)  => do
    let ⟨v', ve⟩ ← resultVectorOfResult (u := u) (α := q(SyntacticSubTerm $L $n))
      (SubTerm.Meta.result tp) arity v
    return ⟨q(Operator.operator $o $v'), q(finitary_congr $o $ve)⟩
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

end FirstOrder
