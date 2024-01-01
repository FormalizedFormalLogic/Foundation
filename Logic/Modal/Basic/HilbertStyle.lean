import Logic.Logic.HilbertStyle2
import Logic.Modal.Basic.Formula

namespace LO

namespace Modal

instance : NegEquiv (Formula α) where
  neg_equiv := rfl

namespace Hilbert

section Axioms

variable (F : Type u) [ModalLogicSymbol F] [System F]

class HasNecessitation where
  necessitation {Γ : Set F} {p : F} : (Γ ⊢! p) → (Γ ⊢! (□p))

class HasAxiomK where
  K (Γ : Set F) (p q : F) : Γ ⊢! □(p ⟶ q) ⟶ □p ⟶ □q

class HasAxiomT where
  T (Γ : Set F) (p : F) : Γ ⊢! □p ⟶ p

class HasAxiomD where
  D (Γ : Set F) (p : F) : Γ ⊢! □p ⟶ ◇p

class HasAxiomB where
  B (Γ : Set F) (p q : F) : Γ ⊢! p ⟶ □◇p

class HasAxiom4 where
  A4 (Γ : Set F) (p : F) : Γ ⊢! □p ⟶ □□p

class HasAxiom5 where
  A5 (Γ : Set F) (p : F) : Γ ⊢! ◇p ⟶ □◇p

class HasAxiomL where
  L (Γ : Set F) (p : F) : Γ ⊢! □(□p ⟶ p) ⟶ □p

class HasAxiomDot2 where
  Dot2 (Γ : Set F) (p : F) : Γ ⊢! ◇□p ⟶ □◇p

class HasAxiomDot3 where
  Dot3 (Γ : Set F) (p q : F) : Γ ⊢! □(□p ⟶ □q) ⋎ □(□q ⟶ □p)

class HasAxiomGrz where
  Grz (Γ : Set F) (p : F) : Γ ⊢! □(□(p ⟶ □p) ⟶ p) ⟶ p

/-- McKinsey Axiom -/
class HasAxiomM where
  M (Γ : Set F) (p : F) : Γ ⊢! □◇p ⟶ ◇□p

class HasAxiomCD where
  CD (Γ : Set F) (p : F) : Γ ⊢! ◇p ⟶ □p

class HasAxiomC4 where
  C4 (Γ : Set F) (p : F) : Γ ⊢! □□p ⟶ □p

class LogicK [Hilbert.Classical F] [HasNecessitation F] [HasAxiomK F]

variable [Hilbert.Classical F] [HasNecessitation F] [HasAxiomK F]

class LogicKD [LogicK F] [HasAxiomD F]

class LogicKT [LogicK F] [HasAxiomT F]

class LogicGL [LogicK F] [HasAxiomL F]

class LogicS4 extends LogicK F, HasAxiomT F, HasAxiom4 F

variable [LogicK F] [HasAxiomT F] [HasAxiom4 F]

class LogicS4Dot2 [LogicS4 F] [HasAxiomDot2 F]

class LogicS4Dot3 [LogicS4 F] [HasAxiomDot3 F]

class LogicS4Grz [LogicS4 F] [HasAxiomGrz F]

class LogicS5 [LogicK F] [HasAxiomT F] [HasAxiom5 F]

end Axioms

variable {α : Type u}

inductive Deduction (Λ : Set (Formula α)) : Set (Formula α) → (Formula α) → Type _
  | axm {Γ p}            : p ∈ Γ → Deduction Λ Γ p
  | maxm {Γ p}           : p ∈ Λ → Deduction Λ Γ p
  | wk {Γ Δ p}           : Γ ⊆ Δ → Deduction Λ Γ p → Deduction Λ Δ p
  | modus_ponens {Γ p q} : Deduction Λ Γ (p ⟶ q) → Deduction Λ Γ p → Deduction Λ Γ q
  | necessitation {Γ p}  : Deduction Λ Γ p → Deduction Λ Γ (□p)
  | verum (Γ)            : Deduction Λ Γ ⊤
  | imply₁ (Γ) (p q)     : Deduction Λ Γ (p ⟶ q ⟶ p)
  | imply₂ (Γ) (p q r)   : Deduction Λ Γ ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r)
  | conj₁ (Γ) (p q)      : Deduction Λ Γ (p ⋏ q ⟶ p)
  | conj₂ (Γ) (p q)      : Deduction Λ Γ (p ⋏ q ⟶ q)
  | conj₃ (Γ) (p q)      : Deduction Λ Γ (p ⟶ q ⟶ p ⋏ q)
  | disj₁ (Γ) (p q)      : Deduction Λ Γ (p ⟶ p ⋎ q)
  | disj₂ (Γ) (p q)      : Deduction Λ Γ (q ⟶ p ⋎ q)
  | disj₃ (Γ) (p q r)    : Deduction Λ Γ ((p ⟶ r) ⟶ (q ⟶ r) ⟶ (p ⋎ q ⟶ r))
  | explode (Γ p)        : Deduction Λ Γ (⊥ ⟶ p)
  | dne (Γ p)            : Deduction Λ Γ (~~p ⟶ p)

notation:45 Γ " ⊢ᴹ(" Λ ") " p => Deduction Λ Γ p

variable (Λ : Set (Formula α)) (Γ : Set (Formula α)) (p : Formula α)

abbrev Deducible := Nonempty (Γ ⊢ᴹ(Λ) p)
notation:45 Γ " ⊢ᴹ(" Λ ")! " p => Deducible Λ Γ p

abbrev Undeducible := IsEmpty (Γ ⊢ᴹ(Λ) p)
notation:45 Γ " ⊬ᴴ(" Λ ")! " p => Undeducible Λ Γ p

abbrev Proof := ∅ ⊢ᴹ(Λ) p
notation:45 "⊢ᴹ(" Λ ") " p => Proof Λ p

abbrev Provable := Nonempty (⊢ᴹ(Λ) p)
notation:45 "⊢ᴹ(" Λ ")! " p => Provable Λ p

abbrev Unprovable := IsEmpty (⊢ᴹ(Λ) p)
notation:45 "⊬ᴴ(" Λ ")!" p => Unprovable Λ p

namespace Deduction

instance instSystem : System (Formula α) where
  Bew := @Hilbert.Deduction α Λ
  axm := axm
  weakening' := wk

def length {Γ : Set (Formula α)} {p : Formula α} : (Γ ⊢ᴹ(Λ) p) → ℕ
  | modus_ponens d₁ d₂ => d₁.length + d₂.length + 1
  | necessitation d₁ => d₁.length + 1
  | _ => 0

variable {Λ : Set (Formula α)} {Γ : Set (Formula α)} {p q : Formula α}

protected def cast (d : Γ ⊢ᴹ(Λ) p) (e₁ : Γ = Δ) (e₂ : p = q) : Δ ⊢ᴹ(Λ) q := cast (by simp [e₁,e₂]) d

@[simp] lemma length_cast (d : Γ ⊢ᴹ(Λ) p) (e₁ : Γ = Δ) (e₂ : p = q) : (d.cast e₁ e₂).length = d.length := by
  rcases e₁ with rfl; rcases e₂ with rfl; simp [Deduction.cast]

def castL (d : Γ ⊢ᴹ(Λ) p) (e₁ : Γ = Δ) : Δ ⊢ᴹ(Λ) p := d.cast e₁ rfl

@[simp] lemma length_castL (d : Γ ⊢ᴹ(Λ) p) (e₁ : Γ = Δ) : (d.castL e₁).length = d.length := length_cast d e₁ rfl

def castR (d : Γ ⊢ᴹ(Λ) p) (e₂ : p = q) : Γ ⊢ᴹ(Λ) q := d.cast rfl e₂

@[simp] lemma length_castR (d : Γ ⊢ᴹ(Λ) p) (e₂ : p = q) : (d.castR e₂).length = d.length := length_cast d rfl e₂

lemma maxm_strengthen {Λ Λ'} (dΛ : Γ ⊢ᴹ(Λ) p) : (Λ ⊆ Λ') → (Γ ⊢ᴹ(Λ') p) := by
  intro hΛ;
  induction dΛ with
  | axm ih => exact axm ih
  | maxm ih => exact maxm (hΛ ih)
  | wk ss _ ih => exact wk ss ih;
  | modus_ponens _ _ ih₁ ih₂ => exact modus_ponens ih₁ ih₂
  | necessitation _ ih => exact necessitation ih
  | verum => apply verum
  | imply₁ => apply imply₁
  | imply₂ => apply imply₂
  | conj₁ => apply conj₁
  | conj₂ => apply conj₂
  | conj₃ => apply conj₃
  | disj₁ => apply disj₁
  | disj₂ => apply disj₂
  | disj₃ => apply disj₃
  | explode => apply explode
  | dne => apply dne

end Deduction

def Proof.length (d : ⊢ᴹ(Λ) p) : ℕ := Deduction.length Λ (by simpa using d)

lemma Provable.dne : (⊢ᴹ(Λ)! ~~p) → (⊢ᴹ(Λ)! p) := by
  intro d;
  have h₁ := @Deduction.dne _ Λ ∅ p;
  have h₂ := d.some; simp [Proof, Deduction] at h₂;
  simp_all [Provable, Proof, Deduction];
  exact ⟨(Deduction.modus_ponens h₁ h₂)⟩

-- TODO: 直接有限モデルを構成する方法（鹿島『コンピュータサイエンスにおける様相論理』2.8参照）で必要になる筈の定義だが，使わないかも知れない．
section

variable [IsCommutative _ (λ (p q : Formula α) => p ⋏ q)]
         [IsCommutative _ (λ (p q : Formula α) => p ⋎ q)]
         [IsAssociative _ (λ (p q : Formula α) => p ⋏ q)]
         [IsAssociative _ (λ (p q : Formula α) => p ⋎ q)]

def Sequent (Γ Δ : Finset (Formula α)) : Formula α := ((Γ.fold (· ⋏ ·) ⊤ id) ⟶ (Δ.fold (· ⋎ ·) ⊥ id))

notation "⟪" Γ "⟹" Δ "⟫" => Sequent Γ Δ

notation "⟪" "⟹" Δ "⟫" => Sequent ∅ Δ

notation "⟪" Γ "⟹" "⟫" => Sequent Γ ∅

def ProofS (Γ Δ : Finset (Formula α)) := ⊢ᴹ(Λ) ⟪Γ ⟹ Δ⟫

#check ⟪ {(⊤ : Formula α)} ⟹ {(⊤ : Formula α)} ⟫

variable [Union (Finset (Formula α))] [Inter (Finset (Formula α))]
variable (Γ₁ Γ₂ Δ : Finset (Formula α))

structure Partial where
  union : (Γ₁ ∪ Γ₂) = Δ
  inter : (Γ₁ ∩ Γ₂) = ∅

structure UnprovablePartial extends Partial Γ₁ Γ₂ Δ where
  unprovable := ⊬ᴴ(Λ)! ⟪Γ₁ ⟹ Γ₂⟫

end

open Deduction

namespace LogicK

instance : System (Formula α) := instSystem 𝐊

instance : Hilbert.Classical (Formula α) where
  modus_ponens hpq hp := ⟨modus_ponens (hpq.some) (hp.some)⟩
  verum Γ        := ⟨verum Γ⟩
  imply₁ Γ p q   := ⟨imply₁ Γ p q⟩
  imply₂ Γ p q r := ⟨imply₂ Γ p q r⟩
  conj₁ Γ p q    := ⟨conj₁ Γ p q⟩
  conj₂ Γ p q    := ⟨conj₂ Γ p q⟩
  conj₃ Γ p q    := ⟨conj₃ Γ p q⟩
  disj₁ Γ p q    := ⟨disj₁ Γ p q⟩
  disj₂ Γ p q    := ⟨disj₂ Γ p q⟩
  disj₃ Γ p q r  := ⟨disj₃ Γ p q r⟩
  explode Γ p    := ⟨explode Γ p⟩
  dne Γ p        := ⟨dne Γ p⟩

instance : HasAxiomK (Formula α) where
  K _ _ _ := ⟨Deduction.maxm (by simp)⟩;

instance : HasNecessitation (Formula α) where
  necessitation h := ⟨Deduction.necessitation h.some⟩

instance : LogicK (Formula α) where

end LogicK


namespace LogicGL

instance : System (Formula α) := instSystem 𝐆𝐋

instance : HasAxiomL (Formula α) where
  L Γ p := ⟨Deduction.maxm (by simp)⟩;

lemma iK (d : Γ ⊢ᴹ(𝐊) p) : (Γ ⊢ᴹ(𝐆𝐋) p) := d.maxm_strengthen (by simp [axiomsGL.ctx];)

lemma iL (d : Γ ⊢ᴹ(𝐋) p) : (Γ ⊢ᴹ(𝐆𝐋) p) := d.maxm_strengthen (by simp [axiomsGL.ctx];)

end LogicGL


namespace LogicS4

lemma stronger_K (d : Γ ⊢ᴹ(𝐊) p) : (Γ ⊢ᴹ(𝐒𝟒) p) := d.maxm_strengthen (by simp only [axiomsS4.ctx.includeK];)

instance : System (Formula α) := instSystem 𝐒𝟒

instance : Hilbert.Classical (Formula α) where
  modus_ponens hpq hp := ⟨modus_ponens (hpq.some) (hp.some)⟩
  verum Γ        := ⟨verum Γ⟩
  imply₁ Γ p q   := ⟨imply₁ Γ p q⟩
  imply₂ Γ p q r := ⟨imply₂ Γ p q r⟩
  conj₁ Γ p q    := ⟨conj₁ Γ p q⟩
  conj₂ Γ p q    := ⟨conj₂ Γ p q⟩
  conj₃ Γ p q    := ⟨conj₃ Γ p q⟩
  disj₁ Γ p q    := ⟨disj₁ Γ p q⟩
  disj₂ Γ p q    := ⟨disj₂ Γ p q⟩
  disj₃ Γ p q r  := ⟨disj₃ Γ p q r⟩
  explode Γ p    := ⟨explode Γ p⟩
  dne Γ p        := ⟨dne Γ p⟩

instance : HasAxiomK (Formula α) where
  K _ _ _ := ⟨Deduction.maxm (by simp)⟩;

instance : HasNecessitation (Formula α) where
  necessitation h := ⟨Deduction.necessitation h.some⟩

instance : HasAxiomT (Formula α) where
  T _ _ := ⟨Deduction.maxm (by simp)⟩;

instance : HasAxiom4 (Formula α) where
  A4 _ _ := ⟨Deduction.maxm (by simp)⟩

instance : LogicS4 (Formula α) where

end LogicS4


namespace LogicS4Dot2

instance : System (Formula α) := instSystem 𝐒𝟒.𝟐

instance : HasAxiomDot2 (Formula α) where
  Dot2 _ _ := ⟨Deduction.maxm (by simp)⟩;

lemma stronger_S4 (d : Γ ⊢ᴹ(𝐒𝟒) p) : (Γ ⊢ᴹ(𝐒𝟒.𝟐) p) := d.maxm_strengthen (by simp [axiomsS4Dot2.ctx];)

end LogicS4Dot2


namespace LogicS4Dot3

instance : System (Formula α) := instSystem 𝐒𝟒.𝟑

instance : HasAxiomDot3 (Formula α) where
  Dot3 _ p q := ⟨Deduction.maxm (by apply Set.mem_union_right; existsi p, q; simp;)⟩

lemma stronger_S4 (d : Γ ⊢ᴹ(𝐒𝟒) p) : (Γ ⊢ᴹ(𝐒𝟒.𝟑) p) := d.maxm_strengthen (by simp [axiomsS4Dot2.ctx];)

end LogicS4Dot3


namespace LogicS4Grz

instance : System (Formula α) := instSystem 𝐒𝟒𝐆𝐫𝐳

instance : HasAxiomGrz (Formula α) where
  Grz _ _ := ⟨Deduction.maxm (by simp)⟩

lemma stronger_S4 (d : Γ ⊢ᴹ(𝐒𝟒) p) : (Γ ⊢ᴹ(𝐒𝟒𝐆𝐫𝐳) p) := d.maxm_strengthen (by simp [axiomsS4Dot2.ctx];)

end LogicS4Grz


namespace LogicS5

instance : System (Formula α) := instSystem 𝐒𝟓

instance : HasAxiomT (Formula α) where
  T _ _ := ⟨Deduction.maxm (by simp)⟩

instance : HasAxiom5 (Formula α) where
  A5 _ _ := ⟨Deduction.maxm (by simp)⟩

lemma stronger_K (d : Γ ⊢ᴹ(𝐊) p) : (Γ ⊢ᴹ(𝐒𝟓) p) := d.maxm_strengthen (by simp only [axiomsS5.ctx.includeK];)

end LogicS5


end Hilbert

end Modal

end LO
