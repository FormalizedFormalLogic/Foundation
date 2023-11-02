import Logic.Predicate.FirstOrder.Basic

namespace LO

-- First-Order Logic + Epsilon Calculus
namespace FirstOrder

namespace Language

variable (L : Language)

def EpsilonExtend (L : Language) : Language := L + ofFunc fun k => Subsentence L (k + 1)

def EpsilonNth (L : Language) : ℕ → Language
  | 0     => L
  | s + 1 => EpsilonExtend (L.EpsilonNth s)

def Epsilon (L : Language) : Language := Language.sigma L.EpsilonNth

def homEpsilon (s : ℕ) : L.EpsilonNth s →ᵥ L.Epsilon := Hom.sigma L.EpsilonNth s

def homEpsilonNthSucc (s : ℕ) : L.EpsilonNth s →ᵥ L.EpsilonNth (s + 1) := Hom.add₁ (L.EpsilonNth s) _

def homEpsilonNthOfLe {s₁ s₂ : ℕ} (h : s₁ ≤ s₂) : L.EpsilonNth s₁ →ᵥ L.EpsilonNth s₂ :=
  Nat.ofLeOfReflOfTrans (r := fun s₁ s₂ => L.EpsilonNth s₁ →ᵥ L.EpsilonNth s₂)
    (fun s => Hom.id (L.EpsilonNth s)) (fun h₁ h₂ => h₂.comp h₁) (homEpsilonNthSucc L) h

def epsilonRelAux₁ {k} : {s : ℕ} → (L.EpsilonNth s).rel k → L.rel k
  | 0,     r         => r
  | _ + 1, Sum.inl r => epsilonRelAux₁ r

def epsilonRelSucc (k s : ℕ) : (L.EpsilonNth s).rel k ≃ (L.EpsilonNth (s + 1)).rel k where
  toFun := fun r => Sum.inl r
  invFun := fun r => match r with | Sum.inl r => r
  left_inv := fun r => by simp
  right_inv := fun r => match r with | Sum.inl r => by simp

def epsilonRel (k) : (s : ℕ) → (L.EpsilonNth s).rel k ≃ L.rel k
  | 0     => Equiv.refl _
  | s + 1 => (L.epsilonRelSucc k s).symm.trans (epsilonRel k s)

def epsilonNthRel (k) (s₁ s₂: ℕ) : (L.EpsilonNth s₁).rel k ≃ (L.EpsilonNth s₂).rel k :=
  (L.epsilonRel k s₁).trans (L.epsilonRel k s₂).symm

end Language

variable {L : Language.{u}}

namespace Subterm

def epsilonIndex : Subterm L.Epsilon Empty n → ℕ
  | #_            => 0
  | func ⟨s, _⟩ v => max s (Fintype.sup fun i => (v i).epsilonIndex)

def toEpsilonNth : (t : Subterm L.Epsilon Empty n) → Subterm (L.EpsilonNth t.epsilonIndex) Empty n
  | #x            => #x
  | func ⟨s, f⟩ v =>
    let s₀ := max s (Fintype.sup fun i => (v i).epsilonIndex)
    have hs : s ≤ s₀ := by simp
    have hi : ∀ i, (v i).epsilonIndex ≤ s₀ := fun i => by
      simp; right; exact Fintype.elem_le_sup (fun i => (v i).epsilonIndex) _
    func ((L.homEpsilonNthOfLe hs).func f) fun i => (v i).toEpsilonNth.lMap (L.homEpsilonNthOfLe (hi i))

end Subterm

namespace Subformula

def epsilonIndex : {n : ℕ} → Subsentence L.Epsilon n → ℕ
  | _, ⊤        => 0
  | _, ⊥        => 0
  | _, rel _ v  => Fintype.sup fun i => (v i).epsilonIndex
  | _, nrel _ v => Fintype.sup fun i => (v i).epsilonIndex
  | _, p ⋏ q    => max p.epsilonIndex q.epsilonIndex
  | _, p ⋎ q    => max p.epsilonIndex q.epsilonIndex
  | _, ∀' p     => p.epsilonIndex
  | _, ∃' p     => p.epsilonIndex

def toEpsilonNth : {n : ℕ} → (p : Subsentence L.Epsilon n) → Subsentence (L.EpsilonNth p.epsilonIndex) n
  | _, ⊤                              => ⊤
  | _, ⊥                              => ⊥
  | _, rel (arity := arity) ⟨s, r⟩ v  =>
    let s₀ := Fintype.sup fun i => (v i).epsilonIndex
    have hi : ∀ i, (v i).epsilonIndex ≤ s₀ := Fintype.elem_le_sup (fun i => (v i).epsilonIndex)
    rel ((L.epsilonNthRel arity s _) r) fun i => (v i).toEpsilonNth.lMap (L.homEpsilonNthOfLe (hi i))
  | _, nrel (arity := arity) ⟨s, r⟩ v =>
    let s₀ := Fintype.sup fun i => (v i).epsilonIndex
    have hi : ∀ i, (v i).epsilonIndex ≤ s₀ := Fintype.elem_le_sup (fun i => (v i).epsilonIndex)
    nrel ((L.epsilonNthRel arity s _) r) fun i => (v i).toEpsilonNth.lMap (L.homEpsilonNthOfLe (hi i))
  | _, p ⋏ q                          =>
    lMap (L.homEpsilonNthOfLe $ Nat.le_max_left _ _) p.toEpsilonNth ⋏ lMap (L.homEpsilonNthOfLe $ Nat.le_max_right _ _) q.toEpsilonNth
  | _, p ⋎ q                          =>
    lMap (L.homEpsilonNthOfLe $ Nat.le_max_left _ _) p.toEpsilonNth ⋎ lMap (L.homEpsilonNthOfLe $ Nat.le_max_right _ _) q.toEpsilonNth
  | _, ∀' p                           => ∀' p.toEpsilonNth
  | _, ∃' p                           => ∃' p.toEpsilonNth

def epsilon {n : ℕ} (p : Subsentence L.Epsilon (n + 1)) : L.Epsilon.func n := ⟨p.epsilonIndex + 1, Sum.inr p.toEpsilonNth⟩

end Subformula

def Theory.epsilonAxiom {k : ℕ} (p : Subsentence L.Epsilon (k + 1)) : Sentence L.Epsilon :=
  “∀* (∃ !p → !(Rew.substsl (Subterm.func p.epsilon (#·) :> (#·)) p))”

def Theory.epsilonSharp (T : Theory L) : Theory L.Epsilon :=
   T.lMap (L.homEpsilon 0) ∪ ⋃ k, Set.range fun p : Subsentence L.Epsilon (k + 1) => Theory.epsilonAxiom p

end FirstOrder

end LO
