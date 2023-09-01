import Logic.Predicate.FirstOrder.Basic.Formula.Formula
import Logic.Predicate.FirstOrder.Basic.Formula.Elab
import Logic.Predicate.FirstOrder.Basic.Term.Meta
open Qq Lean Elab Meta Tactic

namespace LO

namespace FirstOrder

namespace SubFormula

namespace Meta

section lemmata
variable {L : Language} {μ₁ μ₂ : Type v} {n₁ n₂ : ℕ} {ω : Rew L μ₁ n₁ μ₂ n₂}

lemma rew_top_eq : ω.hom ⊤ = ⊤ := by simp

lemma rew_bot_eq : ω.hom ⊥ = ⊥ := by simp

lemma rew_and_eq_of_eq {p q : SubFormula L μ₁ n₁} {p' q'} (hp : ω.hom p = p') (hq : ω.hom q = q') :
    ω.hom (p ⋏ q) = p' ⋏ q' := by simp[←hp, ←hq]

lemma rew_or_eq_of_eq {p q : SubFormula L μ₁ n₁} {p' q'} (hp : ω.hom p = p') (hq : ω.hom q = q') :
    ω.hom (p ⋎ q) = p' ⋎ q' := by simp[←hp, ←hq]

lemma rew_neg_eq_of_eq {p : SubFormula L μ₁ n₁} {p'} (h : ω.hom p = p') :
    ω.hom (~p) = ~p' := by simp[←h]

lemma rew_imply_eq_of_eq {p q : SubFormula L μ₁ n₁} {p' q'} (hp : ω.hom p = p') (hq : ω.hom q = q') :
    ω.hom (p ⟶ q) = p' ⟶ q' := by simp[←hp, ←hq]

lemma rew_iff_eq_of_eq {p q : SubFormula L μ₁ n₁} {p' q'} (hp : ω.hom p = p') (hq : ω.hom q = q') :
    ω.hom (p ⟷ q) = p' ⟷ q' := by simp[←hp, ←hq]

lemma rew_rel_eq_of_eq {k} (r : L.rel k) {v : Fin k → SubTerm L μ₁ n₁} {v'} (h : ω ∘ v = v') :
    ω.hom (rel r v) = rel r v' := by simp[←h, ω.rel]; rfl

lemma rew_nrel_eq_of_eq {k} (r : L.rel k) {v : Fin k → SubTerm L μ₁ n₁} {v'} (h : ω ∘ v = v') :
    ω.hom (nrel r v) = nrel r v' := by simp[←h, ω.nrel]; rfl

lemma rew_finitary_eq_of_eq {k} (o : Finitary L k) {v : Fin k → SubTerm L μ₁ n₁} {v' : Fin k → SubTerm L μ₂ n₂} (h : ω ∘ v = v') :
    ω.hom (o.operator v) = o.operator v' := by simp[←h, o.rew_operator, Function.comp]

section substs
variable {k} {w : Fin k → SyntacticSubTerm L n}

lemma substs_all_eq_of_eq {p : SyntacticSubFormula L (k + 1)} {w' p'}
  (hw : Rew.bShift ∘ w = w') (hp : Rew.substsl (#0 :> w') p = p') :
    Rew.substsl w (∀' p) = ∀' p' := by simp[←hw, ←hp, Rew.all, Rew.q_substs]

lemma substs_ex_eq_of_eq {p : SyntacticSubFormula L (k + 1)} {w' p'}
  (hw : Rew.bShift ∘ w = w') (hp : Rew.substsl (#0 :> w') p = p') :
    Rew.substsl w (∃' p) = ∃' p' := by simp[←hw, ←hp, Rew.ex, Rew.q_substs]

lemma substs_ball_eq_of_eq {p q : SyntacticSubFormula L (k + 1)} {w' p' q'}
  (hw : Rew.bShift ∘ w = w') (hp : Rew.substsl (#0 :> w') p = p') (hq : Rew.substsl (#0 :> w') q = q') :
    Rew.substsl w (∀[p] q) = ∀[p'] q' := by simp[←hw, ←hp, ←hq, Rew.ball, Rew.q_substs]

lemma substs_bex_eq_of_eq {p : SyntacticSubFormula L (k + 1)} {w' p' q'}
  (hw : Rew.bShift ∘ w = w') (hp : Rew.substsl (#0 :> w') p = p') (hq : Rew.substsl (#0 :> w') q = q') :
    Rew.substsl w (∃[p] q) = ∃[p'] q' := by simp[←hw, ←hp, ←hq, Rew.bex, Rew.q_substs]

lemma substs_substs_of_eq {l} {v : Fin l → SyntacticSubTerm L k} {p : SyntacticSubFormula L l} {v' p'}
  (hw : Rew.substs w ∘ v = v') (hp : Rew.substsl v' p = p') :
    Rew.substsl w (Rew.substsl v p) = p' := by
  simp[←hw, ←hp, ←Rew.hom_comp_app, Rew.substs_comp_substs]

end substs

section free

lemma free_all_eq_of_eq {p : SyntacticSubFormula L (n + 1 + 1)} {p'} (h : Rew.freel p = p') :
    Rew.freel (∀' p) = ∀' p' := by simp[←h]

lemma free_ex_eq_of_eq {p : SyntacticSubFormula L (n + 1 + 1)} {p'} (h : Rew.freel p = p') :
    Rew.freel (∃' p) = ∃' p' := by simp[←h]

lemma free_ball_eq_of_eq {p q : SyntacticSubFormula L (n + 1 + 1)} {p' q'}
  (hp : Rew.freel p = p') (hq : Rew.freel q = q'):
    Rew.freel (∀[p] q) = ∀[p'] q' := by simp[←hp, ←hq]

lemma free_bex_eq_of_eq {p q : SyntacticSubFormula L (n + 1 + 1)} {p' q'}
  (hp : Rew.freel p = p') (hq : Rew.freel q = q') :
    Rew.freel (∃[p] q) = ∃[p'] q' := by simp[←hp, ←hq]

lemma free_substs_of_eq {k} {w : Fin k → SyntacticSubTerm L (n + 1)} {p : SyntacticSubFormula L k} {w' p' p''}
  (hw : Rew.free ∘ w = w') (hp : Rew.shiftl p = p') (hp' : Rew.substsl w' p' = p''):
    Rew.freel (Rew.substsl w p) = p'' := by
  simp[←hw, ←hp, ←hp', ←Rew.hom_comp_app, Rew.free_comp_substs_eq_substs_comp_shift]

end free

section fix

lemma fix_all_eq_of_eq {p : SyntacticSubFormula L (n + 1)} {p'} (h : Rew.fixl p = p') :
    Rew.fixl (∀' p) = ∀' p' := by simp[←h]

lemma fix_ex_eq_of_eq {p : SyntacticSubFormula L (n + 1)} {p'} (h : Rew.fixl p = p') :
    Rew.fixl (∃' p) = ∃' p' := by simp[←h]

lemma fix_imply_eq_of_eq {p q : SyntacticSubFormula L n} {p' q'} (hp : Rew.fixl p = p') (hq : Rew.fixl q = q') :
    Rew.fixl (p ⟶ q) = p' ⟶ q' := by simp[←hp, ←hq]

lemma fix_iff_eq_of_eq {p q : SyntacticSubFormula L n} {p' q'} (hp : Rew.fixl p = p') (hq : Rew.fixl q = q') :
    Rew.fixl (p ⟷ q) = p' ⟷ q' := by simp[←hp, ←hq]

lemma fix_ball_eq_of_eq {p q : SyntacticSubFormula L (n + 1)} {p'} (hp : Rew.fixl p = p') (hq : Rew.fixl q = q') :
    Rew.fixl (∀[p] q) = ∀[p'] q' := by simp[←hp, ←hq]

lemma fix_bex_eq_of_eq {p : SyntacticSubFormula L (n + 1)} {p'} (hp : Rew.fixl p = p') (hq : Rew.fixl q = q') :
    Rew.fixl (∃[p] q) = ∃[p'] q' := by simp[←hp, ←hq]

lemma fix_substs_of_eq {k} {p : SyntacticSubFormula L k} {w : Fin k → SyntacticSubTerm L n} {p' p'' w' w'' i}
  (ht : Rew.fixl p = p') (hw : Rew.fix ∘ w = w') (hi : Fin.last n = i) (hw' : w' <: #i = w'') (hp' : Rew.substsl w'' p' = p''):
    Rew.fixl (Rew.substsl w p) = p'' := by
  simp[←ht, ←hw, ←hi, ←hw', ←hp', ←Rew.hom_comp_app]
  exact (Rew.hom_ext' (by ext x <;> simp[Rew.comp_app]; { cases x <;> simp }))

end fix

section shift

lemma shift_all_eq_of_eq {p : SyntacticSubFormula L (n + 1)} {p'} (h : Rew.shiftl p = p') :
    Rew.shiftl (∀' p) = ∀' p' := by simp[←h]

lemma shift_ex_eq_of_eq {p : SyntacticSubFormula L (n + 1)} {p'} (h : Rew.shiftl p = p') :
    Rew.shiftl (∃' p) = ∃' p' := by simp[←h]

lemma shift_ball_eq_of_eq {p q : SyntacticSubFormula L (n + 1)} {p' q'} (hp : Rew.shiftl p = p') (hq : Rew.shiftl q = q') :
    Rew.shiftl (∀[p] q) = ∀[p'] q' := by simp[←hp, ←hq]

lemma shift_bex_eq_of_eq {p q : SyntacticSubFormula L (n + 1)} {p' q'} (hp : Rew.shiftl p = p') (hq : Rew.shiftl q = q') :
    Rew.shiftl (∃[p] q) = ∃[p'] q' := by simp[←hp, ←hq]

lemma shift_substs_of_eq {k} {w : Fin k → SyntacticSubTerm L n} {p : SyntacticSubFormula L k} {w' p' p''}
  (hw : Rew.shift ∘ w = w') (hp : Rew.shiftl p = p') (hp' : Rew.substsl w' p' = p'') :
    Rew.shiftl (Rew.substsl w p) = p'' := by
  simp[←hw, ←hp, ←hp', ←Rew.hom_comp_app]; exact (Rew.hom_ext' (by ext <;> simp[Rew.comp_app]))

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
  (hp : ~p = p') (hp' : Rew.substsl w p' = p'') :
    ~(Rew.substsl w p) = p'' := by simp[←hp, ←hp']

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

lemma free_congr_eq {p p' : SyntacticSubFormula L (n + 1)} {q} (e : p = p') (h : Rew.freel p' = q) :
  Rew.freel p = q := Eq.trans (congr_arg _ e) h

lemma shift_congr_eq {p p' : SyntacticSubFormula L n} {q} (e : p = p') (h : Rew.shiftl p' = q) :
  Rew.shiftl p = q := Eq.trans (congr_arg _ e) h

lemma substs_congr_eq {k} {w w' : Fin k → SyntacticSubTerm L n} {p p' : SyntacticSubFormula L k} {p''}
  (hw : w = w') (hp : p = p') (h : Rew.substsl w' p' = p'') :
  Rew.substsl w p = p'' := hw ▸ hp ▸ h

lemma neg_congr {p p' : SubFormula L μ n} (e : p = p') :
  ~p = ~p' := congr_arg _ e

lemma imply_congr {p q p' q' : SubFormula L μ n} (ep : p = p') (eq : q = q') :
  (p ⟶ q) = (p' ⟶ q') := congr (congr_arg (fun p q => p ⟶ q) ep) eq

lemma iff_congr {p q p' q' : SubFormula L μ n} (ep : p = p') (eq : q = q') :
  (p ⟷ q) = (p' ⟷ q') := congr (congr_arg (fun p q => p ⟷ q) ep) eq

lemma finitary_congr {k} (o : Finitary L k) {v v' : Fin k → SubTerm L μ n} (h : v = v') :
    o.operator v = o.operator v' := congr_arg _ (by simp[h])

lemma univClosure_eq_of_eq {n} {p : SubFormula L μ (n + 1)} {q} (h : univClosure (∀' p) = q) :
  univClosure p = q := by simp[←h]

end lemmata

#check LogicSymbol.HomClass.map_top

partial def resultSubsts (L : Q(Language.{u})) (k n : Q(ℕ)) (w : Q(Fin $k → SyntacticSubTerm $L $n)) :
    (p : Q(SyntacticSubFormula $L $k)) → MetaM ((res : Q(SyntacticSubFormula $L $n)) × Q(Rew.substsl $w $p = $res))
  | ~q(⊤)                            => pure ⟨q(⊤), q(LogicSymbol.HomClass.map_top _)⟩
  | ~q(⊥)                            => pure ⟨q(⊥), q(LogicSymbol.HomClass.map_bot _)⟩
  | ~q(rel (arity := $arity) $r $v)  => do
    let ⟨v', ve⟩ ← resultVectorOfResultFun (u := u) (v := u)
      (α := q(SyntacticSubTerm $L $k)) (β := q(SyntacticSubTerm $L $n))
      q(Rew.substs $w) (SubTerm.Meta.resultSubsts L k n w) arity v
    return ⟨q(rel $r $v'), q(rew_rel_eq_of_eq $r $ve)⟩
  | ~q(nrel (arity := $arity) $r $v) => do
    let ⟨v', ve⟩ ← resultVectorOfResultFun (u := u) (v := u) (α := q(SyntacticSubTerm $L $k)) (β := q(SyntacticSubTerm $L $n))
      q(Rew.substs $w) (SubTerm.Meta.resultSubsts L k n w) arity v
    return ⟨q(nrel $r $v'), q(rew_nrel_eq_of_eq $r $ve)⟩
  | ~q($p ⋏ $q)                      => do
    let ⟨pn, pe⟩ ← resultSubsts L k n w p
    let ⟨qn, qe⟩ ← resultSubsts L k n w q
    return ⟨q($pn ⋏ $qn), q(rew_and_eq_of_eq $pe $qe)⟩
  | ~q($p ⋎ $q)                      => do
    let ⟨pn, pe⟩ ← resultSubsts L k n w p
    let ⟨qn, qe⟩ ← resultSubsts L k n w q
    return ⟨q($pn ⋎ $qn), q(rew_or_eq_of_eq $pe $qe)⟩
  | ~q(∀' $p)                        => do
    let ⟨w', we⟩ ← resultVectorOfResultFun (u := u) (v := u) (α := q(SyntacticSubTerm $L $n)) (β := q(SyntacticSubTerm $L ($n + 1)))
      q(Rew.bShift) (SubTerm.Meta.resultBShift L n) k w
    let ⟨p', pe⟩ ← resultSubsts L q($k + 1) q($n + 1) q(#0 :> $w') p
    return ⟨q(∀' $p'), q(substs_all_eq_of_eq $we $pe)⟩
  | ~q(∃' $p)                        => do
    let ⟨w', we⟩ ← resultVectorOfResultFun (u := u) (v := u) (α := q(SyntacticSubTerm $L $n)) (β := q(SyntacticSubTerm $L ($n + 1)))
      q(Rew.bShift) (SubTerm.Meta.resultBShift L n) k w
    let ⟨p', pe⟩ ← resultSubsts L q($k + 1) q($n + 1) q(#0 :> $w') p
    return ⟨q(∃' $p'), q(substs_ex_eq_of_eq $we $pe)⟩
  | ~q(~$p)                          => do
    let ⟨pn, pe⟩ ← resultSubsts L k n w p
    return ⟨q(~$pn), q(rew_neg_eq_of_eq $pe)⟩
  | ~q($p ⟶ $q)                      => do
    let ⟨pn, pe⟩ ← resultSubsts L k n w p
    let ⟨qn, qe⟩ ← resultSubsts L k n w q
    return ⟨q($pn ⟶ $qn), q(rew_imply_eq_of_eq $pe $qe)⟩
  | ~q($p ⟷ $q)                      => do
    let ⟨pn, pe⟩ ← resultSubsts L k n w p
    let ⟨qn, qe⟩ ← resultSubsts L k n w q
    return ⟨q($pn ⟷ $qn), q(rew_iff_eq_of_eq $pe $qe)⟩
  | ~q(∀[$p] $q)                     => do
    let ⟨w', we⟩ ← resultVectorOfResultFun (u := u) (v := u) (α := q(SyntacticSubTerm $L $n)) (β := q(SyntacticSubTerm $L ($n + 1)))
      q(Rew.bShift) (SubTerm.Meta.resultBShift L n) k w
    let ⟨p', pe⟩ ← resultSubsts L q($k + 1) q($n + 1) q(#0 :> $w') p
    let ⟨q', qe⟩ ← resultSubsts L q($k + 1) q($n + 1) q(#0 :> $w') q
    return ⟨q(∀[$p'] $q'), q(substs_ball_eq_of_eq $we $pe $qe)⟩
  | ~q(∃[$p] $q)                     => do
    let ⟨w', we⟩ ← resultVectorOfResultFun (u := u) (v := u) (α := q(SyntacticSubTerm $L $n)) (β := q(SyntacticSubTerm $L ($n + 1)))
      q(Rew.bShift) (SubTerm.Meta.resultBShift L n) k w
    let ⟨p', pe⟩ ← resultSubsts L q($k + 1) q($n + 1) q(#0 :> $w') p
    let ⟨q', qe⟩ ← resultSubsts L q($k + 1) q($n + 1) q(#0 :> $w') q
    return ⟨q(∃[$p'] $q'), q(substs_bex_eq_of_eq $we $pe $qe)⟩
  | ~q(Rew.substsl (n := $l) $v $p)       => do
    let ⟨v', ve⟩ ← resultVectorOfResultFun (u := u) (v := u) (α := q(SyntacticSubTerm $L $k)) (β := q(SyntacticSubTerm $L $n))
      q(Rew.substs $w) (SubTerm.Meta.resultSubsts L k n w) l v
    let ⟨p', pe⟩ ← resultSubsts L l n v' p
    return ⟨p', q(substs_substs_of_eq $ve $pe)⟩
  | ~q(Operator.operator (ι := Fin $arity) $o $v)  => do
    let ⟨v', ve⟩ ← resultVectorOfResultFun (u := u) (v := u)
      (α := q(SyntacticSubTerm $L $k)) (β := q(SyntacticSubTerm $L $n))
      q(Rew.substs $w) (SubTerm.Meta.resultSubsts L k n w) arity v
    return ⟨q(Operator.operator $o $v'), q(rew_finitary_eq_of_eq $o $ve)⟩
  | ~q($p)                           => pure ⟨q(Rew.substsl $w $p), q(rfl)⟩

elab "dbgresultSubsts" : term => do
  let L : Q(Language.{0}) := q(Language.oRing)
  let k : Q(ℕ) := q(2)
  let n : Q(ℕ) := q(3)
  let p : Q(SyntacticSubFormula $L $k) := q(“ #0 < #1 + 9 * &6 → (∀ #1 < #0 + 7) [#0, &3] ”)
  let w : Q(Fin $k → SyntacticSubTerm $L $n) := q(![ᵀ“2”, ᵀ“&6”])
  let ⟨e, eq⟩ ← resultSubsts (u := levelZero) L q(2) q(3) w p
  let dbgr := q(DbgResult.intro _ $e $eq)
  logInfo m! "substsl w {p} \n⟹ \n{e}"
  return dbgr

#eval dbgresultSubsts

partial def resultShift (L : Q(Language.{u})) (n : Q(ℕ)) : (p : Q(SyntacticSubFormula $L $n)) →
    MetaM ((res : Q(SyntacticSubFormula $L $n)) × Q(Rew.shiftl $p = $res))
  | ~q(⊤)                            => pure ⟨q(⊤), q(LogicSymbol.HomClass.map_top _)⟩
  | ~q(⊥)                            => pure ⟨q(⊥), q(LogicSymbol.HomClass.map_bot _)⟩
  | ~q(rel (arity := $arity) $r $v)  => do
    let ⟨v', ve⟩ ← resultVectorOfResultFun (u := u) (v := u) (α := q(SyntacticSubTerm $L $n)) (β := q(SyntacticSubTerm $L $n))
      q(Rew.shift) (SubTerm.Meta.resultShift L n) arity v
    return ⟨q(rel $r $v'), q(rew_rel_eq_of_eq $r $ve)⟩
  | ~q(nrel (arity := $arity) $r $v) => do
    let ⟨v', ve⟩ ← resultVectorOfResultFun (u := u) (v := u) (α := q(SyntacticSubTerm $L $n)) (β := q(SyntacticSubTerm $L $n))
      q(Rew.shift) (SubTerm.Meta.resultShift L n) arity v
    return ⟨q(nrel $r $v'), q(rew_nrel_eq_of_eq $r $ve)⟩
  | ~q($p ⋏ $q)                      => do
    let ⟨pn, pe⟩ ← resultShift L n p
    let ⟨qn, qe⟩ ← resultShift L n q
    return ⟨q($pn ⋏ $qn), q(rew_and_eq_of_eq $pe $qe)⟩
  | ~q($p ⋎ $q)                      => do
    let ⟨pn, pe⟩ ← resultShift L n p
    let ⟨qn, qe⟩ ← resultShift L n q
    return ⟨q($pn ⋎ $qn), q(rew_or_eq_of_eq $pe $qe)⟩
  | ~q(∀' $p)                        => do
    let ⟨pn, e⟩ ← resultShift L q($n + 1) p
    return ⟨q(∀' $pn), q(shift_all_eq_of_eq $e)⟩
  | ~q(∃' $p)                        => do
    let ⟨pn, e⟩ ← resultShift L q($n + 1) p
    return ⟨q(∃' $pn), q(shift_ex_eq_of_eq $e)⟩
  | ~q(~$p)                          => do
    let ⟨pn, pe⟩ ← resultShift L n p
    return ⟨q(~$pn), q(rew_neg_eq_of_eq $pe)⟩
  | ~q($p ⟶ $q)                      => do
    let ⟨pn, pe⟩ ← resultShift L n p
    let ⟨qn, qe⟩ ← resultShift L n q
    return ⟨q($pn ⟶ $qn), q(rew_imply_eq_of_eq $pe $qe)⟩
  | ~q($p ⟷ $q)                      => do
    let ⟨pn, pe⟩ ← resultShift L n p
    let ⟨qn, qe⟩ ← resultShift L n q
    return ⟨q($pn ⟷ $qn), q(rew_iff_eq_of_eq $pe $qe)⟩
  | ~q(∀[$p] $q)                     => do
    let ⟨p', pe⟩ ← resultShift L q($n + 1) p
    let ⟨q', qe⟩ ← resultShift L q($n + 1) q
    return ⟨q(∀[$p'] $q'), q(shift_ball_eq_of_eq $pe $qe)⟩
  | ~q(∃[$p] $q)                     => do
    let ⟨p', pe⟩ ← resultShift L q($n + 1) p
    let ⟨q', qe⟩ ← resultShift L q($n + 1) q
    return ⟨q(∃[$p'] $q'), q(shift_bex_eq_of_eq $pe $qe)⟩
  | ~q(Rew.substsl (n := $k) $w $p)       => do
    let ⟨w', we⟩ ← resultVectorOfResultFun (u := u) (v := u) (α := q(SyntacticSubTerm $L $n)) (β := q(SyntacticSubTerm $L $n))
      q(Rew.shift) (SubTerm.Meta.resultShift L n) k w
    let ⟨p', pe⟩ ← resultShift L k p
    let ⟨p'', p'e⟩ ← resultSubsts L k n w' p'
    return ⟨p'', q(shift_substs_of_eq $we $pe $p'e)⟩
  | ~q(Operator.operator (ι := Fin $arity) $o $v)  => do
    let ⟨v', ve⟩ ← resultVectorOfResultFun (u := u) (v := u) (α := q(SyntacticSubTerm $L $n)) (β := q(SyntacticSubTerm $L $n))
      q(Rew.shift) (SubTerm.Meta.resultShift L n) arity v
    return ⟨q(Operator.operator $o $v'), q(rew_finitary_eq_of_eq $o $ve)⟩
  | ~q($p)                           => pure ⟨q(Rew.shiftl $p), q(rfl)⟩

partial def resultFree (L : Q(Language.{u})) (n : Q(ℕ)) : (p : Q(SyntacticSubFormula $L ($n + 1))) →
    MetaM ((res : Q(SyntacticSubFormula $L $n)) × Q(Rew.freel $p = $res))
  | ~q(⊤)                            => pure ⟨q(⊤), q(LogicSymbol.HomClass.map_top _)⟩
  | ~q(⊥)                            => pure ⟨q(⊥), q(LogicSymbol.HomClass.map_bot _)⟩
  | ~q(rel (arity := $arity) $r $v)  => do
    let ⟨v', ve⟩ ← resultVectorOfResultFun (u := u) (v := u)
      (α := q(SyntacticSubTerm $L ($n + 1))) (β := q(SyntacticSubTerm $L $n))
      q(Rew.free) (SubTerm.Meta.resultFree L n) arity v
    return ⟨q(rel $r $v'), q(rew_rel_eq_of_eq $r $ve)⟩
  | ~q(nrel (arity := $arity) $r $v) => do
    let ⟨v', ve⟩ ← resultVectorOfResultFun (u := u) (v := u)
      (α := q(SyntacticSubTerm $L ($n + 1))) (β := q(SyntacticSubTerm $L $n))
      q(Rew.free) (SubTerm.Meta.resultFree L n) arity v
    let e : Q(SyntacticSubFormula $L $n) := q(nrel $r $v')
    return ⟨e, q(rew_nrel_eq_of_eq $r $ve)⟩
  | ~q($p ⋏ $q)                      => do
    let ⟨pn, pe⟩ ← resultFree L n p
    let ⟨qn, qe⟩ ← resultFree L n q
    return ⟨q($pn ⋏ $qn), q(rew_and_eq_of_eq $pe $qe)⟩
  | ~q($p ⋎ $q)                      => do
    let ⟨pn, pe⟩ ← resultFree L n p
    let ⟨qn, qe⟩ ← resultFree L n q
    return ⟨q($pn ⋎ $qn), q(rew_or_eq_of_eq $pe $qe)⟩
  | ~q(∀' $p)                        => do
    let ⟨pn, e⟩ ← resultFree L q($n + 1) p
    return ⟨q(∀' $pn), q(free_all_eq_of_eq $e)⟩
  | ~q(∃' $p)                        => do
    let ⟨pn, e⟩ ← resultFree L q($n + 1) p
    return ⟨q(∃' $pn), q(free_ex_eq_of_eq $e)⟩
  | ~q(~$p)                          => do
    let ⟨pn, pe⟩ ← resultFree L n p
    return ⟨q(~$pn), q(rew_neg_eq_of_eq $pe)⟩
  | ~q($p ⟶ $q)                      => do
    let ⟨pn, pe⟩ ← resultFree L n p
    let ⟨qn, qe⟩ ← resultFree L n q
    return ⟨q($pn ⟶ $qn), q(rew_imply_eq_of_eq $pe $qe)⟩
  | ~q($p ⟷ $q)                      => do
    let ⟨pn, pe⟩ ← resultFree L n p
    let ⟨qn, qe⟩ ← resultFree L n q
    return ⟨q($pn ⟷ $qn), q(rew_iff_eq_of_eq $pe $qe)⟩
  | ~q(∀[$p] $q)                     => do
    let ⟨p', pe⟩ ← resultFree L q($n + 1) p
    let ⟨q', qe⟩ ← resultFree L q($n + 1) q
    return ⟨q(∀[$p'] $q'), q(free_ball_eq_of_eq $pe $qe)⟩
  | ~q(∃' $p)                        => do
    let ⟨pn, e⟩ ← resultFree L q($n + 1) p
    return ⟨q(∃' $pn), q(free_ex_eq_of_eq $e)⟩
  | ~q(Rew.substsl (n := $k) $w $p)       => do
    let ⟨p', pe⟩ ← resultShift (L := L) (n := k) p
    let ⟨w', we⟩ ← resultVectorOfResultFun (u := u) (v := u) (α := q(SyntacticSubTerm $L ($n + 1))) (β := q(SyntacticSubTerm $L $n))
      q(Rew.free) (SubTerm.Meta.resultShift L n) k w
    let ⟨p'', p'e⟩ ← resultSubsts L k n w' p'
    return ⟨p'', q(free_substs_of_eq $we $pe $p'e)⟩
  | ~q(Operator.operator (ι := Fin $arity) $o $v)  => do
    let ⟨v', ve⟩ ← resultVectorOfResultFun (u := u) (v := u)
      (α := q(SyntacticSubTerm $L ($n + 1))) (β := q(SyntacticSubTerm $L $n))
      q(Rew.free) (SubTerm.Meta.resultFree L n) arity v
    return ⟨q(Operator.operator $o $v'), q(rew_finitary_eq_of_eq $o $ve)⟩
  | ~q($p)                           => do
    return ⟨q(Rew.freel $p), q(rfl)⟩

elab "dbgresultFree" : term => do
  let L : Q(Language.{0}) := q(Language.oRing)
  let k : Q(ℕ) := q(2)
  let p : Q(SyntacticSubFormula $L ($k + 1)) := q(“#0 + #1 + #2 + #3 < &0 + &1 + &2 + &3”)
  let ⟨e, eq⟩ ← resultFree L k p
  let dbgr := q(DbgResult.intro _ $e $eq)
  logInfo m! "free {p} \n⟹ \n{e}"
  return dbgr

#eval dbgresultFree

#check fix_substs_of_eq

partial def resultFix (L : Q(Language.{u})) (n : Q(ℕ)) : (p : Q(SyntacticSubFormula $L $n)) →
    MetaM ((res : Q(SyntacticSubFormula $L ($n + 1))) × Q(Rew.fixl $p = $res))
  | ~q(⊤)                            => pure ⟨q(⊤), q(LogicSymbol.HomClass.map_top _)⟩
  | ~q(⊥)                            => pure ⟨q(⊥), q(LogicSymbol.HomClass.map_bot _)⟩
  | ~q(rel (arity := $arity) $r $v)  => do
    let ⟨v', ve⟩ ← resultVectorOfResultFun (u := u) (v := u)
      (α := q(SyntacticSubTerm $L $n)) (β := q(SyntacticSubTerm $L ($n + 1)))
      q(Rew.fix) (SubTerm.Meta.resultFix L n) arity v
    return ⟨q(rel $r $v'), q(rew_rel_eq_of_eq $r $ve)⟩
  | ~q(nrel (arity := $arity) $r $v) => do
    let ⟨v', ve⟩ ← resultVectorOfResultFun (u := u) (v := u)
      (α := q(SyntacticSubTerm $L $n)) (β := q(SyntacticSubTerm $L ($n + 1)))
      q(Rew.fix) (SubTerm.Meta.resultFix L n) arity v
    return ⟨q(nrel $r $v'), q(rew_nrel_eq_of_eq $r $ve)⟩
  | ~q($p ⋏ $q)                      => do
    let ⟨pn, pe⟩ ← resultFix L n p
    let ⟨qn, qe⟩ ← resultFix L n q
    return ⟨q($pn ⋏ $qn), q(rew_and_eq_of_eq $pe $qe)⟩
  | ~q($p ⋎ $q)                      => do
    let ⟨pn, pe⟩ ← resultFix L n p
    let ⟨qn, qe⟩ ← resultFix L n q
    return ⟨q($pn ⋎ $qn), q(rew_or_eq_of_eq $pe $qe)⟩
  | ~q(∀' $p)                        => do
    let ⟨pn, e⟩ ← resultFix L q($n + 1) p
    return ⟨q(∀' $pn), q(fix_all_eq_of_eq $e)⟩
  | ~q(∃' $p)                        => do
    let ⟨pn, e⟩ ← resultFix L q($n + 1) p
    return ⟨q(∃' $pn), q(fix_ex_eq_of_eq $e)⟩
  | ~q(~$p)                          => do
    let ⟨pn, pe⟩ ← resultFix L n p
    return ⟨q(~$pn), q(rew_neg_eq_of_eq $pe)⟩
  | ~q($p ⟶ $q)                      => do
    let ⟨pn, pe⟩ ← resultFix L n p
    let ⟨qn, qe⟩ ← resultFix L n q
    return ⟨q($pn ⟶ $qn), q(rew_imply_eq_of_eq $pe $qe)⟩
  | ~q($p ⟷ $q)                      => do
    let ⟨pn, pe⟩ ← resultFix L n p
    let ⟨qn, qe⟩ ← resultFix L n q
    return ⟨q($pn ⟷ $qn), q(rew_iff_eq_of_eq $pe $qe)⟩
  | ~q(∀[$p] $q)                        => do
    let ⟨p', pe⟩ ← resultFix L q($n + 1) p
    let ⟨q', qe⟩ ← resultFix L q($n + 1) q
    return ⟨q(∀[$p'] $q'), q(fix_ball_eq_of_eq $pe $qe)⟩
  | ~q(∃[$p] $q)                        => do
    let ⟨p', pe⟩ ← resultFix L q($n + 1) p
    let ⟨q', qe⟩ ← resultFix L q($n + 1) q
    return ⟨q(∃[$p'] $q'), q(fix_bex_eq_of_eq $pe $qe)⟩
  | ~q(Rew.substsl (n := $k) $w $p)       => do
    let ⟨p', hp⟩ ← resultFix (L := L) (n := k) p
    let ⟨w', hw⟩ ← resultVectorOfResultFun (u := u) (v := u)
      (α := q(SyntacticSubTerm $L $n)) (β := q(SyntacticSubTerm $L ($n + 1)))
      q(Rew.fix) (SubTerm.Meta.resultFix L n) k w
    let some nval := (←whnf n).natLit? | throwError f!"Fail: natLit: {n}"
    let z : Q(Fin ($n + 1)) ← Lean.Expr.ofNat q(Fin ($n + 1)) nval
    let hz : Q(Fin.last $n = $z) := (q(@rfl (Fin ($n + 1)) $z) : Expr)
    let ⟨w'', hw'⟩ ← vectorAppend k w' q(#$z)
    let ⟨p'', hp'⟩ ← resultSubsts L q($k + 1) q($n + 1) w'' p'
    return ⟨p'', q(fix_substs_of_eq $hp $hw $hz $hw' $hp')⟩
  | ~q(Operator.operator (ι := Fin $arity) $o $v)  => do
    let ⟨v', ve⟩ ← resultVectorOfResultFun (u := u) (v := u)
      (α := q(SyntacticSubTerm $L $n)) (β := q(SyntacticSubTerm $L ($n + 1)))
      q(Rew.fix) (SubTerm.Meta.resultFix L n) arity v
    return ⟨q(Operator.operator $o $v'), q(rew_finitary_eq_of_eq $o $ve)⟩
  | ~q($p)                           => do
    return ⟨q(Rew.fixl $p), q(rfl)⟩
  | e => throwError m! "fail! {e} "

elab "dbgResultFix'" : term => do
  let L : Q(Language.{0}) := q(Language.oRing)
  let n : Q(ℕ) := q(5)
  let p : Q(SyntacticSubFormula $L $n) := q(“#0 + #1 + #2 + #3 < &0 + &1 + &2 + &3 → (#0 = #1)[0, &5] ”)
  logInfo m! "{p}"
  let ⟨e, eq⟩ ← resultFix (L := L) (n := n) p
  let dbgr := q(DbgResult.intro _ $e $eq)
  logInfo m! "free {p} \n⟹ \n{e}"
  return dbgr

#eval dbgResultFix'

partial def resultNeg (L : Q(Language.{u})) (n : Q(ℕ)) : (p : Q(SyntacticSubFormula $L $n)) →
    MetaM ((res : Q(SyntacticSubFormula $L $n)) × Q(~$p = $res))
  | ~q(⊤)                      => pure ⟨q(⊥), q(rfl)⟩
  | ~q(⊥)                      => pure ⟨q(⊤), q(rfl)⟩
  | ~q(rel $r $v)              => pure ⟨q(nrel $r $v), q(neg_rel $r _)⟩
  | ~q(nrel $r $v)             => pure ⟨q(rel $r $v), q(neg_nrel $r _)⟩  
  | ~q($p ⋏ $q)                => do
    let ⟨pn, pe⟩ ← resultNeg L n p
    let ⟨qn, qe⟩ ← resultNeg L n q
    return ⟨q($pn ⋎ $qn), q(neg_and_eq_of_eq $pe $qe)⟩
  | ~q($p ⋎ $q)                => do
    let ⟨pn, pe⟩ ← resultNeg L n p
    let ⟨qn, qe⟩ ← resultNeg L n q
    return ⟨q($pn ⋏ $qn), q(neg_or_eq_of_eq $pe $qe)⟩
  | ~q(∀' $p)                  => do
    let ⟨pn, e⟩ ← resultNeg L q($n + 1) p
    return ⟨q(∃' $pn), q(neg_all_eq_of_eq $e)⟩
  | ~q(∃' $p)                  => do
    let ⟨pn, e⟩ ← resultNeg L q($n + 1) p
    return ⟨q(∀' $pn), q(neg_ex_eq_of_eq $e)⟩
  | ~q(~$p)                    => do
    return ⟨q($p), q(neg_neg' $p)⟩
  | ~q($p ⟶ $q)                => do
    let ⟨qn, e⟩ ← resultNeg L n q
    return ⟨q($p ⋏ $qn), q(neg_imp_eq_of_eq $e)⟩
  | ~q($p ⟷ $q)                => do
    let ⟨pn, pe⟩ ← resultNeg L n p
    let ⟨qn, qe⟩ ← resultNeg L n q
    return ⟨q(($p ⋏ $qn) ⋎ ($q ⋏ $pn)), q(neg_iff_eq_of_eq $pe $qe)⟩
  | ~q(∀[$p] $q)               => do
    let ⟨q', qe⟩ ← resultNeg L q($n + 1) q
    return ⟨q(∃[$p] $q'), q(neg_ball_eq_of_eq $qe)⟩
  | ~q(∃[$p] $q)               => do
    let ⟨q', qe⟩ ← resultNeg L q($n + 1) q
    return ⟨q(∀[$p] $q'), q(neg_bex_eq_of_eq $qe)⟩
  | ~q(Rew.substsl (n := $k) $w $p) => do
    let ⟨p', pe⟩ ← resultNeg L k p
    let ⟨p'', p'e⟩ ← resultSubsts L k n w p'
    return ⟨p'', q(neg_substs_of_eq $pe $p'e)⟩
  | ~q($p)                     => pure ⟨q(~$p), q(rfl)⟩

partial def resultUnivClosure {L : Q(Language.{u})} {n : Q(ℕ)} (p : Q(SyntacticSubFormula $L $n)) :
    MetaM ((res : Q(SyntacticFormula $L)) × Q(univClosure $p = $res)) :=
  match n with
  | ~q(0)      => return ⟨p, q(rfl)⟩
  | ~q($n' + 1) => do
    let ⟨p', hp⟩ ← resultUnivClosure (u := u) (L := L) (n := n') q(∀' $p)
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

partial def result (L : Q(Language.{u})) (n : Q(ℕ)) : (p : Q(SyntacticSubFormula $L $n)) →
    MetaM ((res : Q(SyntacticSubFormula $L $n)) × Q($p = $res))
  | ~q(⊤)                            => pure ⟨q(⊤), q(rfl)⟩
  | ~q(⊥)                            => pure ⟨q(⊥), q(rfl)⟩
  | ~q(rel (arity := $arity) $r $v)  => do
    let ⟨v', ve⟩ ← resultVectorOfResult (u := u) (α := q(SyntacticSubTerm $L $n))
      (SubTerm.Meta.result tp L n) arity v
    return ⟨q(rel $r $v'), q(rel_congr $r $ve)⟩
  | ~q(nrel (arity := $arity) $r $v) => do
    let ⟨v', ve⟩ ← resultVectorOfResult (u := u) (α := q(SyntacticSubTerm $L $n))
      (SubTerm.Meta.result tp L n) arity v
    return ⟨q(nrel $r $v'), q(nrel_congr $r $ve)⟩
  | ~q($p ⋏ $q)                      => do
    let ⟨pn, pe⟩ ← result L n p
    let ⟨qn, qe⟩ ← result L n q
    return ⟨q($pn ⋏ $qn), q(and_congr $pe $qe)⟩
  | ~q($p ⋎ $q)                      => do
    let ⟨pn, pe⟩ ← result L n p
    let ⟨qn, qe⟩ ← result L n q
    return ⟨q($pn ⋎ $qn), q(or_congr $pe $qe)⟩
  | ~q(∀' $p)                        => do
    let ⟨pn, pe⟩ ← result L q($n + 1) p
    return ⟨q(∀' $pn), q(all_congr $pe)⟩
  | ~q(∃' $p)                        => do
    let ⟨pn, pe⟩ ← result L q($n + 1) p
    return ⟨q(∃' $pn), q(ex_congr $pe)⟩
  | ~q(Rew.freel $p)                      => do
    let ⟨pn, e⟩ ← result L q($n + 1) p
    let ⟨pnn, ee⟩ ← resultFree L n pn
    return ⟨q($pnn), q(free_congr_eq $e $ee)⟩
  | ~q(Rew.substsl (n := $k) $w $p)       => do
    let ⟨p', pe⟩ ← result L k p
    let ⟨w', we⟩ ← resultVectorOfResult (u := u) (α := q(SyntacticSubTerm $L $n))
      (SubTerm.Meta.result tp L n) k w
    let ⟨n, e⟩ ← resultSubsts L k n w' p'
    return ⟨q($n), q(substs_congr_eq $we $pe $e)⟩
  | ~q(Rew.shiftl $p)                     => do
    let ⟨pn, e⟩ ← result L n p
    let ⟨pnn, ee⟩ ← resultShift L n pn
    return ⟨q($pnn), q(shift_congr_eq $e $ee)⟩
  | ~q(~$p)                          => do
    let ⟨pn, e⟩ ← result L n p
    if unfoldOpt UnfoldOption.neg then
      let ⟨pnn, ee⟩ ← resultNeg L n pn
      return ⟨q($pnn), q(neg_congr_eq $e $ee)⟩
    else return ⟨q(~$pn), q(neg_congr $e)⟩
  | ~q($p ⟶ $q)                     => do
    let ⟨pn, pe⟩ ← result L n p
    let ⟨qn, qe⟩ ← result L n q    
    if unfoldOpt UnfoldOption.imply then
      if unfoldOpt UnfoldOption.neg then
        let ⟨pnn, pee⟩ ← resultNeg L n pn
        return ⟨q($pnn ⋎ $qn), q(imp_eq_of_eq $pe $qe $pee)⟩
      return ⟨q(~$pn ⋎ $qn), q(imply_congr $pe $qe)⟩
    else return ⟨q($pn ⟶ $qn), q(imply_congr $pe $qe)⟩
  | ~q($p ⟷ $q)                     => do
    let ⟨pn, pe⟩ ← result L n p
    let ⟨qn, qe⟩ ← result L n q
    if unfoldOpt UnfoldOption.iff then
      if unfoldOpt UnfoldOption.imply then
        if unfoldOpt UnfoldOption.neg then
          let ⟨pnn, pee⟩ ← resultNeg L n pn
          let ⟨qnn, qee⟩ ← resultNeg L n qn
          return ⟨q(($pnn ⋎ $qn) ⋏ ($qnn ⋎ $pn)), q(iff_eq_of_eq $pe $qe $pee $qee)⟩
        else return ⟨q((~$pn ⋎ $qn) ⋏ (~$qn ⋎ $pn)), q(iff_congr $pe $qe)⟩
      else
        return ⟨q(($pn ⟶ $qn) ⋏ ($qn ⟶ $pn)), q(iff_congr $pe $qe)⟩
    else return ⟨q($pn ⟷ $qn), q(iff_congr $pe $qe)⟩
  | ~q(∀[$p] $q)                     => do
    let ⟨p', pe⟩ ← result L q($n + 1) p
    let ⟨q', qe⟩ ← result L q($n + 1) q
    if unfoldOpt UnfoldOption.ball then
      return ⟨q(∀'($p' ⟶ $q')), q(ball_congr $pe $qe)⟩
    else return ⟨q(∀[$p'] $q'), q(ball_congr $pe $qe)⟩
  | ~q(∃[$p] $q)                     => do
    let ⟨p', pe⟩ ← result L q($n + 1) p
    let ⟨q', qe⟩ ← result L q($n + 1) q
    if unfoldOpt UnfoldOption.bex then
      return ⟨q(∃'($p' ⋏ $q')), q(bex_congr $pe $qe)⟩
    else return ⟨q(∃[$p'] $q'), q(bex_congr $pe $qe)⟩
  | ~q(Operator.operator (ι := Fin $arity) $o $v)  => do
    let ⟨v', ve⟩ ← resultVectorOfResult (u := u) (α := q(SyntacticSubTerm $L $n))
      (SubTerm.Meta.result tp L n) arity v
    return ⟨q(Operator.operator $o $v'), q(finitary_congr $o $ve)⟩
  | ~q($p)                           => do
    -- logInfo m!"match fail: {p}"
    return ⟨q($p), q(rfl)⟩

partial def result₀ {L : Q(Language.{u})} (p : Q(SyntacticFormula $L)) :
    MetaM ((res : Q(SyntacticFormula $L)) × Q($p = $res)) :=
  result tp unfoldOpt L q(0) p

partial def result₀_res {L : Q(Language.{u})} (p : Q(SyntacticFormula $L)) :
    MetaM Q(SyntacticFormula $L) := do
  let ⟨res, _⟩ ← result₀ tp unfoldOpt (L := L) p
  return res

partial def result₀List {L : Q(Language.{u})} (l : List Q(SyntacticFormula $L)) :
    MetaM $ (res : List Q(SyntacticFormula $L)) × Q($(toQList (u := u) l) = $(toQList (u := u) res)) :=
  resultList (result₀ tp unfoldOpt) l

partial def resultShift₀ {L : Q(Language.{u})} (p : Q(SyntacticFormula $L)) :
    MetaM $ (res : Q(SyntacticFormula $L)) × Q(Rew.shiftl $p = $res) :=
  resultShift L q(0) p

partial def resultShift₀List {L : Q(Language.{u})} (l : List Q(SyntacticFormula $L)) :
    MetaM $ (res : List Q(SyntacticFormula $L)) × Q(List.map Rew.shiftl $(toQList (u := u) l) = $(toQList (u := u) res)) :=
  funResultList (u := u) (α := q(SyntacticFormula $L)) q(Rew.shiftl) resultShift₀ l

partial def resultSubst₀ {L : Q(Language.{u})} (p : Q(SyntacticSubFormula $L 1)) (s : Q(SyntacticTerm $L)) :
    MetaM $ (res : Q(SyntacticFormula $L)) × Q(Rew.substsl ![$s] $p = $res) :=
  resultSubsts L q(1) q(0) q(![$s]) p

partial def resultSubst₀List {L : Q(Language.{u})} (v : List Q(SyntacticTerm $L)) (p : Q(SyntacticSubFormula $L 1)) :
    MetaM $ (res : List Q(SyntacticFormula $L)) × Q(List.map (Rew.substsl ![·] $p) $(toQList (u := u) v) = $(toQList (u := u) res)) :=
  funResultList (u := u) (α := q(SyntacticTerm $L)) q((Rew.substsl ![·] $p)) (resultSubst₀ p) v

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

example {t : SyntacticSubTerm Language.oRing 3} : DbgResult (SyntacticSubFormula Language.oRing 12)
    $ Rew.shiftl “3 < #4 ↔ ∀ !(Rew.shift.hom $ Rew.substsl ![&99, &6] “∀ (ᵀ!t) + (#0 * 8) < &7 + #1 + (#3 + 6)”)” :=
  by dbgResult

example : DbgResult (SyntacticSubFormula Language.oRing 3)
    $ Rew.freel “3 * 4 = &6” :=
  by dbgResult

end Meta

end SubFormula

end FirstOrder

end LO