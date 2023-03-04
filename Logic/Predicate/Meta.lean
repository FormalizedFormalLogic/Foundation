import Logic.Predicate.Coding
import Logic.Vorspiel.Meta
open Qq Lean Elab Meta Tactic

-- SubTerm normalization
namespace SubTerm
namespace Meta

section lemmata
variable {L : Language.{u}} {μ : Type v} {n}

lemma free_fixedVar_last (n : ℕ) : free (#⟨n, Nat.lt.base n⟩ : SyntacticSubTerm L (n + 1)) = &0 :=
  SubTerm.free_fixedVar_last

lemma free_fixedVar_of_lt (x : Fin (n + 1)) (h : x.val < n) : free (#x : SyntacticSubTerm L (n + 1)) = #⟨x, h⟩ :=
  free_fixedVar_castSucc (L := L) ⟨x, h⟩

lemma free_func0 (f : L.func 0) :
    SubTerm.free (SubTerm.func (L := L) (n := n + 1) f ![]) = SubTerm.func f ![] := by simp

lemma free_func1 (f : L.func 1) {t : SyntacticSubTerm L (n + 1)} {t'} (h : free t = t'):
    SubTerm.free (SubTerm.func f ![t]) = SubTerm.func f ![t'] := by simp[←h]; funext x; simp

lemma free_func2 (f : L.func 2) {t₁ t₂ : SyntacticSubTerm L (n + 1)} {t₁' t₂'}
  (h₁ : free t₁ = t₁') (h₂ : free t₂ = t₂') :
    SubTerm.free (SubTerm.func f ![t₁, t₂]) = SubTerm.func f ![t₁', t₂'] :=
  by simp[←h₁, ←h₂]; funext x; cases x using Fin.cases <;> simp

lemma free_func3 (f : L.func 3) {t₁ t₂ t₃ : SyntacticSubTerm L (n + 1)} {t₁' t₂' t₃'}
  (h₁ : free t₁ = t₁') (h₂ : free t₂ = t₂') (h₃ : free t₃ = t₃') :
    SubTerm.free (SubTerm.func f ![t₁, t₂, t₃]) = SubTerm.func f ![t₁', t₂', t₃'] := by
  simp[←h₁, ←h₂, ←h₃]; funext x;
  cases' x using Fin.cases with x <;> simp;
  cases' x using Fin.cases with x <;> simp

lemma subst_fixedVar_last (n : ℕ) (s : SubTerm L μ n) :
    subst s (#⟨n, Nat.lt.base n⟩ : SubTerm L μ (n + 1)) = s :=
  SubTerm.subst_fixedVar_last _

lemma subst_fixedVar_of_lt {s : SubTerm L μ n} (x : Fin (n + 1)) (h : x.val < n) : 
    subst s (#x : SubTerm L μ (n + 1)) = #⟨x, h⟩ :=
  subst_fixedVar_castSucc s ⟨x, h⟩

lemma subst_func0 {s : SubTerm L μ n} (f : L.func 0) :
    subst s (SubTerm.func (L := L) (n := n + 1) f ![]) = SubTerm.func f ![] := by simp

lemma subst_func1 {s : SubTerm L μ n} (f : L.func 1) {t : SubTerm L μ (n + 1)} {t'} (h : subst s t = t'):
    subst s (SubTerm.func f ![t]) = SubTerm.func f ![t'] := by simp[←h]; funext x; simp

lemma subst_func2 {s : SubTerm L μ n} (f : L.func 2) {t₁ t₂ : SubTerm L μ (n + 1)} {t₁' t₂'}
  (h₁ : subst s t₁ = t₁') (h₂ : subst s t₂ = t₂') :
    subst s (SubTerm.func f ![t₁, t₂]) = SubTerm.func f ![t₁', t₂'] :=
  by simp[←h₁, ←h₂]; funext x; cases x using Fin.cases <;> simp

lemma subst_func3 {s : SubTerm L μ n} (f : L.func 3) {t₁ t₂ t₃ : SubTerm L μ (n + 1)} {t₁' t₂' t₃'}
  (h₁ : subst s t₁ = t₁') (h₂ : subst s t₂ = t₂') (h₃ : subst s t₃ = t₃') :
    subst s (SubTerm.func f ![t₁, t₂, t₃]) = SubTerm.func f ![t₁', t₂', t₃'] := by
  simp[←h₁, ←h₂, ←h₃]; funext x;
  cases' x using Fin.cases with x <;> simp;
  cases' x using Fin.cases with x <;> simp

lemma shift_func0 (f : L.func 0) :
    shift (SubTerm.func (L := L) (n := n) f ![]) = SubTerm.func f ![] := by simp

lemma shift_func1 (f : L.func 1) {t t' : SyntacticSubTerm L n} (h : shift t = t'):
    shift (SubTerm.func f ![t]) = SubTerm.func f ![t'] := by simp[←h]; funext x; simp

lemma shift_func2 (f : L.func 2) {t₁ t₂ t₁' t₂' : SyntacticSubTerm L n}
  (h₁ : shift t₁ = t₁') (h₂ : shift t₂ = t₂') :
    shift (SubTerm.func f ![t₁, t₂]) = SubTerm.func f ![t₁', t₂'] :=
  by simp[←h₁, ←h₂]; funext x; cases x using Fin.cases <;> simp

lemma shift_func3 (f : L.func 3) {t₁ t₂ t₃ t₁' t₂' t₃' : SyntacticSubTerm L n}
  (h₁ : shift t₁ = t₁') (h₂ : shift t₂ = t₂') (h₃ : shift t₃ = t₃') :
    shift (SubTerm.func f ![t₁, t₂, t₃]) = SubTerm.func f ![t₁', t₂', t₃'] := by
  simp[←h₁, ←h₂, ←h₃]; funext x;
  cases' x using Fin.cases with x <;> simp;
  cases' x using Fin.cases with x <;> simp

lemma shift_subst {t : SyntacticSubTerm L (n + 1)} {u t' u'}
  (ht : shift t = t') (hu : shift u = u') :
    shift (subst u t) = subst u' t' := by
  simp[←ht, ←hu, shift, SubTerm.subst, map, bind_bind]; congr; funext x
  cases' x using Fin.lastCases with x <;> simp

lemma bShift_func0 (f : L.func 0) :
    bShift (SubTerm.func (L := L) (μ:= μ) (n := n) f ![]) = SubTerm.func f ![] := by simp

lemma bShift_func1 (f : L.func 1) {t : SubTerm L μ n} {t'} (h : bShift t = t'):
    bShift (SubTerm.func f ![t]) = SubTerm.func f ![t'] := by simp[←h]; funext x; simp

lemma bShift_func2 (f : L.func 2) {t₁ t₂ : SubTerm L μ n} {t₁' t₂'}
  (h₁ : bShift t₁ = t₁') (h₂ : bShift t₂ = t₂') :
    bShift (SubTerm.func f ![t₁, t₂]) = SubTerm.func f ![t₁', t₂'] :=
  by simp[←h₁, ←h₂]; funext x; cases x using Fin.cases <;> simp

lemma bShift_func3 (f : L.func 3) {t₁ t₂ t₃ : SyntacticSubTerm L n} {t₁' t₂' t₃'}
  (h₁ : bShift t₁ = t₁') (h₂ : bShift t₂ = t₂') (h₃ : bShift t₃ = t₃') :
    bShift (SubTerm.func f ![t₁, t₂, t₃]) = SubTerm.func f ![t₁', t₂', t₃'] := by
  simp[←h₁, ←h₂, ←h₃]; funext x;
  cases' x using Fin.cases with x <;> simp;
  cases' x using Fin.cases with x <;> simp

lemma bShift_subst {t : SyntacticSubTerm L (n + 1)} {u t' u'}
  (ht : bShift t = t') (hu : bShift u = u') :
    bShift (subst u t) = subst u' t' := by
  simp[←ht, ←hu, bShift, SubTerm.subst, map, bind_bind]; congr; funext x
  cases' x using Fin.lastCases with x <;> simp[Fin.succ_castSucc]

lemma func1_congr (f : L.func 1) {t t' : SyntacticSubTerm L n} (h : t = t'):
    SubTerm.func f ![t] = SubTerm.func f ![t'] := by simp[←h]

lemma func2_congr (f : L.func 2) {t₁ t₂ t₁' t₂' : SyntacticSubTerm L n}
  (h₁ : t₁ = t₁') (h₂ : t₂ = t₂') :
    SubTerm.func f ![t₁, t₂] = SubTerm.func f ![t₁', t₂'] :=
  by simp[←h₁, ←h₂]

lemma func3_congr (f : L.func 3) {t₁ t₂ t₃ t₁' t₂' t₃' : SyntacticSubTerm L n}
  (h₁ : t₁ = t₁') (h₂ : t₂ = t₂') (h₃ : t₃ = t₃') :
    SubTerm.func f ![t₁, t₂, t₃] = SubTerm.func f ![t₁', t₂', t₃'] := by
  simp[←h₁, ←h₂, ←h₃]

lemma free_congr_eq {t t' : SyntacticSubTerm L (n + 1)} {s} (e : t = t') (h : free t' = s) :
  free t = s := Eq.trans (congr_arg _ e) h

lemma subst_congr_eq {s s' : SubTerm L μ n} {t t' u} (es : s = s') (et : t = t') (h : subst s' t' = u) :
  subst s t = u := Eq.trans (congr_arg₂ SubTerm.subst es et) h

lemma shift_congr_eq {t t' : SyntacticSubTerm L n} {u} (e : t = t') (h : shift t' = u) :
  shift t = u := Eq.trans (congr_arg _ e) h

lemma bShift_congr_eq {t t' : SubTerm L μ n} {u} (e : t = t') (h : bShift t' = u) :
  bShift t = u := Eq.trans (congr_arg _ e) h

section
variable [hz : L.HasZero] [ho : L.HasOne] [ha : L.HasAdd]

@[simp] lemma free_natLit (z : ℕ) :
    free (natLit z : SyntacticSubTerm L (n + 1)) = natLit z :=
  SubTerm.bind_natLit _ _ _

@[simp] lemma subst_natLit {s} (z : ℕ) :
    subst s (natLit z : SubTerm L μ (n + 1)) = natLit z :=
  SubTerm.bind_natLit _ _ _

@[simp] lemma shift_natLit (z : ℕ) :
    shift (natLit z : SyntacticSubTerm L n) = natLit z :=
  SubTerm.bind_natLit _ _ _

@[simp] lemma bShift_natLit (z : ℕ) :
    bShift (natLit z : SubTerm L μ n) = natLit z :=
  SubTerm.bind_natLit _ _ _

end
end lemmata

partial def resultFree {L : Q(Language.{u})} {n : Q(ℕ)} : (t : Q(SyntacticSubTerm $L ($n + 1))) →
    MetaM ((res : Q(SyntacticSubTerm $L $n)) × Q(SubTerm.free $t = $res))
  | ~q(#$x)                              => do
    let n ←whnf n 
    let some nnat := n.natLit? | throwError f!"Fail: natLit: {n}"
    let some xval := (← finQVal (n := q(.succ $n)) x) | throwError f!"Fail: FinQVal {x}"
    if xval = nnat then
      let e := q(free_fixedVar_last (L := $L) $n)
      return ⟨q(&0), e⟩
    else
      let lt ← decideTQ q(($x).val < $n)
      let e := q(free_fixedVar_of_lt (L := $L) $x $lt)
      let z : Q(Fin $n) ← Lean.Expr.ofNat q(Fin $n) xval
      return ⟨q(#$z), e⟩
  | ~q(&$x)                              => do
    let z ← natAppFunQ Nat.succ x
    let e : Expr := q(SubTerm.free_freeVar (L := $L) (n := $n) $x)
    return ⟨q(&$z), e⟩
  | ~q(SubTerm.func $f ![])              => pure ⟨q(SubTerm.func $f ![]), q(free_func0 $f)⟩
  | ~q(SubTerm.func $f ![$t])            => do
    let ⟨tn, e⟩ ← resultFree (L := L) (n := n) t
    return ⟨q(SubTerm.func $f ![$tn]), q(free_func1 $f $e)⟩
  | ~q(SubTerm.func $f ![$t₁, $t₂])      => do
    let ⟨tn₁, e₁⟩ ← resultFree (L := L) (n := n) t₁
    let ⟨tn₂, e₂⟩ ← resultFree (L := L) (n := n) t₂
    return ⟨q(SubTerm.func $f ![$tn₁, $tn₂]), q(free_func2 $f $e₁ $e₂)⟩
  | ~q(SubTerm.func $f ![$t₁, $t₂, $t₃]) => do
    let ⟨tn₁, e₁⟩ ← resultFree (L := L) (n := n) t₁
    let ⟨tn₂, e₂⟩ ← resultFree (L := L) (n := n) t₂
    let ⟨tn₃, e₃⟩ ← resultFree (L := L) (n := n) t₃
    return ⟨q(SubTerm.func $f ![$tn₁, $tn₂, $tn₃]), q(free_func3 $f $e₁ $e₂ $e₃)⟩
  | ~q(natLit (hz := $hz) (ho := $ho) (ha := $ha) $z) => pure ⟨q(natLit $z), q(free_natLit $z)⟩
  | ~q($t)                               => do
    logInfo m!"match fail: {t}"
    return ⟨q(SubTerm.free $t), q(rfl)⟩

partial def resultSubst {L : Q(Language.{u})} {n : Q(ℕ)} (s : Q(SyntacticSubTerm $L $n)) :
   (t : Q(SyntacticSubTerm $L ($n + 1))) →
    MetaM ((res : Q(SyntacticSubTerm $L $n)) × Q(SubTerm.subst $s $t = $res))
  | ~q(#$x)                              => do
    let n ←whnf n 
    let some nnat := n.natLit? | throwError f!"Fail: natLit: {n}"
    let some xval := (← finQVal (n := q(.succ $n)) x) | throwError f!"Fail: FinQVal {x}"
    if xval = nnat then
      return ⟨q($s), (q(subst_fixedVar_last $n $s) : Expr)⟩
    else
      let lt ← decideTQ q(($x).val < $n)
      let e := q(free_fixedVar_of_lt (L := $L) $x $lt)
      let z : Q(Fin $n) ← Lean.Expr.ofNat q(Fin $n) xval
      return ⟨q(#$z), e⟩
  | ~q(&$x)                              => pure ⟨q(&$x), q(SubTerm.subst_freeVar _ _)⟩
  | ~q(SubTerm.func $f ![])              => pure ⟨q(SubTerm.func $f ![]), q(subst_func0 $f)⟩
  | ~q(SubTerm.func $f ![$t])            => do
    let ⟨tn, e⟩ ← resultSubst (L := L) (n := n) s t
    return ⟨q(SubTerm.func $f ![$tn]), q(subst_func1 $f $e)⟩
  | ~q(SubTerm.func $f ![$t₁, $t₂])      => do
    let ⟨tn₁, e₁⟩ ← resultSubst (L := L) (n := n) s t₁
    let ⟨tn₂, e₂⟩ ← resultSubst (L := L) (n := n) s t₂
    return ⟨q(SubTerm.func $f ![$tn₁, $tn₂]), q(subst_func2 $f $e₁ $e₂)⟩
  | ~q(SubTerm.func $f ![$t₁, $t₂, $t₃]) => do
    let ⟨tn₁, e₁⟩ ← resultSubst (L := L) (n := n) s t₁
    let ⟨tn₂, e₂⟩ ← resultSubst (L := L) (n := n) s t₂
    let ⟨tn₃, e₃⟩ ← resultSubst (L := L) (n := n) s t₃
    return ⟨q(SubTerm.func $f ![$tn₁, $tn₂, $tn₃]), q(subst_func3 $f $e₁ $e₂ $e₃)⟩
  | ~q(natLit (hz := $hz) (ho := $ho) (ha := $ha) $z) => pure ⟨q(natLit $z), q(subst_natLit $z)⟩
  | ~q($t)                               => do
    logInfo m!"match fail: {t}"
    return ⟨q(SubTerm.subst $s $t), q(rfl)⟩

partial def resultShift {L : Q(Language.{u})} {n : Q(ℕ)} : (t : Q(SyntacticSubTerm $L $n)) →
    MetaM ((res : Q(SyntacticSubTerm $L $n)) × Q(SubTerm.shift $t = $res))
  | ~q(#$x)                              => pure ⟨q(#$x), q(SubTerm.shift_fixedVar $x)⟩
  | ~q(&$x)                              =>  do
    let z ← natAppFunQ Nat.succ x
    let e := q(SubTerm.shift_freeVar (L := $L) (n := $n) $x)
    return ⟨q(&$z), e⟩
  | ~q(SubTerm.func $f ![])              => pure ⟨q(SubTerm.func $f ![]), q(shift_func0 $f)⟩
  | ~q(SubTerm.func $f ![$t])            => do
    let ⟨tn, e⟩ ← resultShift (L := L) (n := n) t
    return ⟨q(SubTerm.func $f ![$tn]), q(shift_func1 $f $e)⟩
  | ~q(SubTerm.func $f ![$t₁, $t₂])      => do
    let ⟨tn₁, e₁⟩ ← resultShift (L := L) (n := n) t₁
    let ⟨tn₂, e₂⟩ ← resultShift (L := L) (n := n) t₂
    return ⟨q(SubTerm.func $f ![$tn₁, $tn₂]), q(shift_func2 $f $e₁ $e₂)⟩
  | ~q(SubTerm.func $f ![$t₁, $t₂, $t₃]) => do
    let ⟨tn₁, e₁⟩ ← resultShift (L := L) (n := n) t₁
    let ⟨tn₂, e₂⟩ ← resultShift (L := L) (n := n) t₂
    let ⟨tn₃, e₃⟩ ← resultShift (L := L) (n := n) t₃
    return ⟨q(SubTerm.func $f ![$tn₁, $tn₂, $tn₃]), q(shift_func3 $f $e₁ $e₂ $e₃)⟩
  | ~q(SubTerm.subst $t₁ $t₂)            => do
    let ⟨tn₁, e₁⟩ ← resultShift (L := L) (n := n) t₁
    let ⟨tn₂, e₂⟩ ← resultShift (L := L) (n := q(.succ $n)) t₂
    return ⟨q(SubTerm.subst $tn₁ $tn₂), q(shift_subst $e₂ $e₁)⟩
  | ~q(natLit (hz := $hz) (ho := $ho) (ha := $ha) $z) => pure ⟨q(natLit $z), q(shift_natLit $z)⟩
  | ~q($t)                               => do
    logInfo m!"match fail: {t}"
    return ⟨q(shift $t), q(rfl)⟩

partial def resultBShift {L : Q(Language.{u})} {n : Q(ℕ)} : (t : Q(SyntacticSubTerm $L $n)) →
    MetaM ((res : Q(SyntacticSubTerm $L ($n + 1))) × Q(bShift $t = $res))
  | ~q(#$x)                              => do
    let z ← natAppFunQ Nat.succ x
    let e := q(SubTerm.fixedSucc_fixedVar (L := $L) (μ := ℕ) (n := $n) $x)
    return ⟨q(&$z), e⟩
  | ~q(&$x)                              => pure ⟨q(&$x), q(SubTerm.fixedSucc_freeVar $x)⟩
  | ~q(SubTerm.func $f ![])              => pure ⟨q(SubTerm.func $f ![]), q(bShift_func0 $f)⟩
  | ~q(SubTerm.func $f ![$t])            => do
    let ⟨tn, e⟩ ← resultBShift (L := L) (n := n) t
    return ⟨q(SubTerm.func $f ![$tn]), q(bShift_func1 $f $e)⟩
  | ~q(SubTerm.func $f ![$t₁, $t₂])      => do
    let ⟨tn₁, e₁⟩ ← resultBShift (L := L) (n := n) t₁
    let ⟨tn₂, e₂⟩ ← resultBShift (L := L) (n := n) t₂
    return ⟨q(SubTerm.func $f ![$tn₁, $tn₂]), q(bShift_func2 $f $e₁ $e₂)⟩
  | ~q(SubTerm.func $f ![$t₁, $t₂, $t₃]) => do
    let ⟨tn₁, e₁⟩ ← resultBShift (L := L) (n := n) t₁
    let ⟨tn₂, e₂⟩ ← resultBShift (L := L) (n := n) t₂
    let ⟨tn₃, e₃⟩ ← resultBShift (L := L) (n := n) t₃
    return ⟨q(SubTerm.func $f ![$tn₁, $tn₂, $tn₃]), q(bShift_func3 $f $e₁ $e₂ $e₃)⟩
  | ~q(SubTerm.subst $t₁ $t₂)            => do
    let ⟨tn₁, e₁⟩ ← resultBShift (L := L) (n := n) t₁
    let ⟨tn₂, e₂⟩ ← resultBShift (L := L) (n := q(.succ $n)) t₂
    return ⟨q(SubTerm.subst $tn₁ $tn₂), q(bShift_subst $e₂ $e₁)⟩
  | ~q(natLit (hz := $hz) (ho := $ho) (ha := $ha) $z) => pure ⟨q(natLit $z), q(bShift_natLit $z)⟩
  | ~q($t)                               => do
    logInfo m!"match fail: {t}"
    return ⟨q(bShift $t), q(rfl)⟩

partial def result {L : Q(Language.{u})} {n : Q(ℕ)} : (t : Q(SyntacticSubTerm $L $n)) →
    MetaM ((res : Q(SyntacticSubTerm $L $n)) × Q($t = $res))
  | ~q(#$x)                              => pure ⟨q(#$x), q(rfl)⟩
  | ~q(&$x)                              => pure ⟨q(&$x), q(rfl)⟩
  | ~q(SubTerm.func $f ![])              => pure ⟨q(SubTerm.func $f ![]), q(rfl)⟩
  | ~q(SubTerm.func $f ![$t])            => do
    let ⟨tn, e⟩ ← result (L := L) (n := n) t
    return ⟨q(SubTerm.func $f ![$tn]), q(func1_congr $f $e)⟩
  | ~q(SubTerm.func $f ![$t₁, $t₂])      => do
    let ⟨tn₁, e₁⟩ ← result (L := L) (n := n) t₁
    let ⟨tn₂, e₂⟩ ← result (L := L) (n := n) t₂
    return ⟨q(SubTerm.func $f ![$tn₁, $tn₂]), q(func2_congr $f $e₁ $e₂)⟩
  | ~q(SubTerm.func $f ![$t₁, $t₂, $t₃]) => do
    let ⟨tn₁, e₁⟩ ← result (L := L) (n := n) t₁
    let ⟨tn₂, e₂⟩ ← result (L := L) (n := n) t₂
    let ⟨tn₃, e₃⟩ ← result (L := L) (n := n) t₃
    return ⟨q(SubTerm.func $f ![$tn₁, $tn₂, $tn₃]), q(func3_congr $f $e₁ $e₂ $e₃)⟩
  | ~q(free $t)                          => do
    let ⟨tn, e⟩ ← result (L := L) (n := q(.succ $n)) t
    let ⟨tnn, ee⟩ ← resultFree (L := L) (n := n) tn
    return ⟨q($tnn), q(free_congr_eq $e $ee)⟩
  | ~q(subst $s $t)                      => do
    let ⟨tn, te⟩ ← result (L := L) (n := q(.succ $n)) t
    let ⟨sn, se⟩ ← result (L := L) (n := q($n)) s
    let ⟨tnn, ee⟩ ← resultSubst (L := L) (n := n) sn tn
    return ⟨q($tnn), q(subst_congr_eq $se $te $ee)⟩
  | ~q(shift $t)                         => do
    let ⟨tn, e⟩ ← result (L := L) (n := q($n)) t
    let ⟨tnn, ee⟩ ← resultShift (L := L) (n := n) tn
    return ⟨q($tnn), q(shift_congr_eq $e $ee)⟩
  | ~q(natLit (hz := $hz) (ho := $ho) (ha := $ha) $z) => pure ⟨q(natLit $z), q(rfl)⟩
  | ~q($t)                               => do
    logInfo m!"match fail: {t}"
    return ⟨q($t), q(rfl)⟩

partial def result' {L : Q(Language.{u})} {n : Q(ℕ)} (t : Q(SyntacticSubTerm $L $n)) :
    MetaM (Result (u := u) q(SyntacticSubTerm $L $n) t) := do
    let ⟨res, e⟩ ← result t 
    return ⟨res, e⟩

private inductive ResultTest (α : Type u) : (a : α) → Type u
  | result : (a b : α) → a = b → ResultTest α a

elab "dbg" : tactic => do
  let goalType ← Elab.Tactic.getMainTarget
  let some ⟨.succ u, ty⟩ ← checkSortQ' goalType | throwError "error: not a type"
  let ~q(ResultTest (SyntacticSubTerm $L $n) $t) := ty | throwError "error: not a type"
  logInfo m!"t = {t} : SyntacticSubTerm {L} {n}"
  let t : Q(SyntacticSubTerm $L $n) ← withReducible <| whnf t

  let ⟨tn, e⟩ ← result (L := L) (n := n) t
  logInfo m!"tn = {tn}"
  logInfo m!"e = {e}"
  let c : Q(ResultTest (SyntacticSubTerm $L $n) $t) := (q(ResultTest.result ($t) $tn $e) : Expr)
  Lean.Elab.Tactic.closeMainGoal c

example {t : SyntacticSubTerm Language.oring 13} : ResultTest (SyntacticSubTerm Language.oring 12)
    (shift $ subst &99 T“(!t) + (#6 * !(bShift T“#2 + 9”)) + &7”) :=
  by dbg

example : 1 ≠ 2 := of_decide_eq_true rfl

end Meta

end SubTerm