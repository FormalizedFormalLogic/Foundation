import Logic.Predicate.FirstOrder.Basic

namespace LO

-- First-Order Logic + epsilon Calculus
namespace FirstOrder

namespace Language

variable (L : Language)

def epsilonExtend (L : Language) : Language := L + ofFunc fun k => Subsentence L (k + 1)

def epsilonNth (L : Language) : ℕ → Language
  | 0     => L
  | s + 1 => epsilonExtend (L.epsilonNth s)

def epsilon (L : Language) : Language := Language.sigma L.epsilonNth

def homEpsilon (s : ℕ) : L.epsilonNth s →ᵥ L.epsilon := Hom.sigma L.epsilonNth s

def homepsilonNthSucc (s : ℕ) : L.epsilonNth s →ᵥ L.epsilonNth (s + 1) := Hom.add₁ (L.epsilonNth s) _

def homepsilonNthOfLe {s₁ s₂ : ℕ} (h : s₁ ≤ s₂) : L.epsilonNth s₁ →ᵥ L.epsilonNth s₂ :=
  Nat.ofLeOfReflOfTrans (r := fun s₁ s₂ => L.epsilonNth s₁ →ᵥ L.epsilonNth s₂)
    (fun s => Hom.id (L.epsilonNth s)) (fun h₁ h₂ => h₂.comp h₁) (homepsilonNthSucc L) h

def epsilonRelAux₁ {k} : {s : ℕ} → (L.epsilonNth s).rel k → L.rel k
  | 0,     r         => r
  | _ + 1, Sum.inl r => epsilonRelAux₁ r

def epsilonRelSucc (k s : ℕ) : (L.epsilonNth s).rel k ≃ (L.epsilonNth (s + 1)).rel k where
  toFun := fun r => Sum.inl r
  invFun := fun r => match r with | Sum.inl r => r
  left_inv := fun r => by simp
  right_inv := fun r => match r with | Sum.inl r => by simp

def epsilonRel (k) : (s : ℕ) → (L.epsilonNth s).rel k ≃ L.rel k
  | 0     => Equiv.refl _
  | s + 1 => (L.epsilonRelSucc k s).symm.trans (epsilonRel k s)

def epsilonNthRel (k) (s₁ s₂: ℕ) : (L.epsilonNth s₁).rel k ≃ (L.epsilonNth s₂).rel k :=
  (L.epsilonRel k s₁).trans (L.epsilonRel k s₂).symm

end Language

variable {L : Language.{u}}

namespace Subterm

def epsilonIndex : Subterm L.epsilon Empty n → ℕ
  | #_            => 0
  | func ⟨s, _⟩ v => max s (Fintype.sup fun i => (v i).epsilonIndex)

def toepsilonNth : (t : Subterm L.epsilon Empty n) → Subterm (L.epsilonNth t.epsilonIndex) Empty n
  | #x            => #x
  | func ⟨s, f⟩ v =>
    let s₀ := max s (Fintype.sup fun i => (v i).epsilonIndex)
    have hs : s ≤ s₀ := by simp
    have hi : ∀ i, (v i).epsilonIndex ≤ s₀ := fun i => by
      simp; right; exact Fintype.elem_le_sup (fun i => (v i).epsilonIndex) _
    func ((L.homepsilonNthOfLe hs).func f) fun i => (v i).toepsilonNth.lMap (L.homepsilonNthOfLe (hi i))

end Subterm

namespace Subformula

def epsilonIndex : {n : ℕ} → Subsentence L.epsilon n → ℕ
  | _, ⊤        => 0
  | _, ⊥        => 0
  | _, rel _ v  => Fintype.sup fun i => (v i).epsilonIndex
  | _, nrel _ v => Fintype.sup fun i => (v i).epsilonIndex
  | _, p ⋏ q    => max p.epsilonIndex q.epsilonIndex
  | _, p ⋎ q    => max p.epsilonIndex q.epsilonIndex
  | _, ∀' p     => p.epsilonIndex
  | _, ∃' p     => p.epsilonIndex

def toepsilonNth : {n : ℕ} → (p : Subsentence L.epsilon n) → Subsentence (L.epsilonNth p.epsilonIndex) n
  | _, ⊤                              => ⊤
  | _, ⊥                              => ⊥
  | _, rel (arity := arity) ⟨s, r⟩ v  =>
    let s₀ := Fintype.sup fun i => (v i).epsilonIndex
    have hi : ∀ i, (v i).epsilonIndex ≤ s₀ := Fintype.elem_le_sup (fun i => (v i).epsilonIndex)
    rel ((L.epsilonNthRel arity s _) r) fun i => (v i).toepsilonNth.lMap (L.homepsilonNthOfLe (hi i))
  | _, nrel (arity := arity) ⟨s, r⟩ v =>
    let s₀ := Fintype.sup fun i => (v i).epsilonIndex
    have hi : ∀ i, (v i).epsilonIndex ≤ s₀ := Fintype.elem_le_sup (fun i => (v i).epsilonIndex)
    nrel ((L.epsilonNthRel arity s _) r) fun i => (v i).toepsilonNth.lMap (L.homepsilonNthOfLe (hi i))
  | _, p ⋏ q                          =>
    lMap (L.homepsilonNthOfLe $ Nat.le_max_left _ _) p.toepsilonNth ⋏ lMap (L.homepsilonNthOfLe $ Nat.le_max_right _ _) q.toepsilonNth
  | _, p ⋎ q                          =>
    lMap (L.homepsilonNthOfLe $ Nat.le_max_left _ _) p.toepsilonNth ⋎ lMap (L.homepsilonNthOfLe $ Nat.le_max_right _ _) q.toepsilonNth
  | _, ∀' p                           => ∀' p.toepsilonNth
  | _, ∃' p                           => ∃' p.toepsilonNth

def epsilon {n : ℕ} (p : Subsentence L.epsilon (n + 1)) : L.epsilon.func n := ⟨p.epsilonIndex + 1, Sum.inr p.toepsilonNth⟩

end Subformula

def Theory.epsilonAxiom {k : ℕ} (p : Subsentence L.epsilon (k + 1)) : Sentence L.epsilon :=
  “∀* (∃ !p → !((Rew.substs (Subterm.func p.epsilon (#·) :> (#·))).hom p))”

def Theory.epsilonSharp (T : Theory L) : Theory L.epsilon :=
   T.lMap (L.homEpsilon 0) ∪ ⋃ k, Set.range fun p : Subsentence L.epsilon (k + 1) => Theory.epsilonAxiom p

local postfix:max "♯" => Theory.epsilonSharp

namespace Epsilon

variable {T : Theory L} {M : Type u} [Inhabited M] (str : Structure L M)

noncomputable def ofFunc : Structure (Language.ofFunc fun k => Subsentence L (k + 1)) M :=
  Structure.ofFunc _ (fun f v => Classical.epsilon fun x => Subformula.Eval str (x :> v) Empty.elim f)

noncomputable def modelExtend : Structure L.epsilonExtend M :=
  @Structure.add L (Language.ofFunc fun k => Subsentence L (k + 1)) M str (ofFunc str)

noncomputable def modelAux : (s : ℕ) → Structure (L.epsilonNth s) M
  | 0     => str
  | s + 1 => modelExtend (modelAux s)

noncomputable def model : Structure L.epsilon M := @Structure.sigma _ _ M (modelAux str)



end Epsilon

end FirstOrder

end LO
