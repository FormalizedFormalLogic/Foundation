import Logic.Predicate.FirstOrder.Meta
open Qq Lean Elab Meta Tactic

namespace FirstOrder
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