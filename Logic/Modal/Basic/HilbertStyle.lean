import Logic.Logic.HilbertStyle2
import Logic.Modal.Basic.Formula

namespace LO

namespace Modal

namespace Hilbert

section Axioms

variable (F : Type u) [ModalLogicSymbol F]

class HasNecessitation extends System F where
  necessitation {Γ : Set F} {p : F} : (Γ ⊢! p) → (Γ ⊢! (□p))

class HasAxiomK extends System F where
  K (Γ : Set F) (p q : F) : Γ ⊢! □(p ⟶ q) ⟶ □p ⟶ □q

class HasAxiomT extends System F where
  T (Γ : Set F) (p : F) : Γ ⊢! □p ⟶ p

class HasAxiomD extends System F where
  D (Γ : Set F) (p : F) : Γ ⊢! □p ⟶ ◇p

class HasAxiomB extends System F where
  B (Γ : Set F) (p q : F) : Γ ⊢! p ⟶ □◇p

class HasAxiom4 extends System F where
  A4 (Γ : Set F) (p : F) : Γ ⊢! □p ⟶ □□p

class HasAxiom5 extends System F where
  A5 (Γ : Set F) (p q : F) : Γ ⊢! ◇p ⟶ □◇p

class HasAxiomL extends System F where
  L (Γ : Set F) (p : F) : Γ ⊢! □(□p ⟶ p) ⟶ □p

class HasAxiomDot2 extends System F where
  Dot2 (Γ : Set F) (p : F) : Γ ⊢! ◇□p ⟶ □◇p

class HasAxiomDot3 extends System F where
  Dot3 (Γ : Set F) (p : F) : Γ ⊢! □(□p ⟶ □q) ⋎ □(□q ⟶ □p)

class HasAxiomGrz extends System F where
  Grz (Γ : Set F) (p : F) : Γ ⊢! □(□(p ⟶ □p) ⟶ p) ⟶ p

/-- McKinsey Axiom -/
class HasAxiomM extends System F where
  M (Γ : Set F) (p : F) : Γ ⊢! □◇p ⟶ ◇□p

class HasAxiomCD extends System F where
  CD (Γ : Set F) (p : F) : Γ ⊢! ◇p ⟶ □p

class HasAxiomC4 extends System F where
  C4 (Γ : Set F) (p : F) : Γ ⊢! □□p ⟶ □p

class LogicK extends Hilbert.Classical F, HasNecessitation F, HasAxiomK F

class LogicKD extends LogicK F, HasAxiomD F

class LogicKT extends LogicK F, HasAxiomT F

class LogicS4 extends LogicK F, HasAxiomT F, HasAxiom4 F

class LogicS5 extends LogicK F, HasAxiomT F, HasAxiom5 F

class LogicGL extends LogicK F, HasAxiomL F

class LogicS4Dot2 extends LogicS4 F, HasAxiomDot2 F

class LogicS4Dot3 extends LogicS4 F, HasAxiomDot3 F

class LogicS4Grz extends LogicS4 F, HasAxiomGrz F

end Axioms

variable {α : Type u}

inductive DerivationH (Λ : Set (Formula α)) : Set (Formula α) → (Formula α) → Type _
  | axm {Γ p}            : p ∈ Γ → DerivationH Λ Γ p
  | maxm {Γ p}           : p ∈ Λ → DerivationH Λ Γ p
  | wk {Γ Δ p}           : Γ ⊆ Δ → DerivationH Λ Γ p → DerivationH Λ Δ p
  | modus_ponens {Γ p q} : DerivationH Λ Γ (p ⟶ q) → DerivationH Λ Γ p → DerivationH Λ Γ q
  | necessitation {Γ p}  : DerivationH Λ Γ p → DerivationH Λ Γ (□p)
  | verum (Γ)            : DerivationH Λ Γ ⊤
  | imply₁ (Γ) (p q)     : DerivationH Λ Γ (p ⟶ q ⟶ p)
  | imply₂ (Γ) (p q r)   : DerivationH Λ Γ ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r)
  | conj₁ (Γ) (p q)      : DerivationH Λ Γ (p ⋏ q ⟶ p)
  | conj₂ (Γ) (p q)      : DerivationH Λ Γ (p ⋏ q ⟶ q)
  | conj₃ (Γ) (p q)      : DerivationH Λ Γ (p ⟶ q ⟶ p ⋏ q)
  | disj₁ (Γ) (p q)      : DerivationH Λ Γ (p ⟶ p ⋎ q)
  | disj₂ (Γ) (p q)      : DerivationH Λ Γ (q ⟶ p ⋎ q)
  | disj₃ (Γ) (p q r)    : DerivationH Λ Γ ((p ⟶ r) ⟶ (q ⟶ r) ⟶ (p ⋎ q ⟶ r))
  | explode (Γ p)        : DerivationH Λ Γ (⊥ ⟶ p)
  | dne (Γ p)            : DerivationH Λ Γ (~~p ⟶ p)

notation:45 Γ " ⊢ᴴ(" Λ ") " p => DerivationH Λ Γ p

variable (Λ : Set (Formula α)) (Γ : Set (Formula α)) (p : Formula α)

abbrev DerivableH := Nonempty (Γ ⊢ᴴ(Λ) p)

notation:45 Γ " ⊢ᴴ(" Λ ")! " p => DerivableH Λ Γ p

abbrev Underivable := IsEmpty (Γ ⊢ᴴ(Λ) p)

notation:45 Γ " ⊬ᴴ(" Λ ")! " p => Underivable Λ Γ p


abbrev ProofH := ∅ ⊢ᴴ(Λ) p

notation:45 "⊢ᴴ(" Λ ") " p => ProofH Λ p


abbrev ProvableH := Nonempty (⊢ᴴ(Λ) p)

notation:45 "⊢ᴴ(" Λ ")! " p => ProvableH Λ p


abbrev UnprovableH := IsEmpty (⊢ᴴ(Λ) p)

notation:45 "⊬ᴴ(" Λ ")!" p => UnprovableH Λ p

namespace DerivationH

def length {Γ : Set (Formula α)} {p : Formula α} : (Γ ⊢ᴴ(Λ) p) → ℕ
  | modus_ponens d₁ d₂ => d₁.length + d₂.length + 1
  | necessitation d₁ => d₁.length + 1
  | _ => 0

variable {Λ : Set (Formula α)} {Γ : Set (Formula α)} {p q : Formula α}

protected def cast (d : Γ ⊢ᴴ(Λ) p) (e₁ : Γ = Δ) (e₂ : p = q) : Δ ⊢ᴴ(Λ) q := cast (by simp [e₁,e₂]) d

@[simp] lemma length_cast (d : Γ ⊢ᴴ(Λ) p) (e₁ : Γ = Δ) (e₂ : p = q) : (d.cast e₁ e₂).length = d.length := by
  rcases e₁ with rfl; rcases e₂ with rfl; simp [DerivationH.cast]

def castL (d : Γ ⊢ᴴ(Λ) p) (e₁ : Γ = Δ) : Δ ⊢ᴴ(Λ) p := d.cast e₁ rfl

@[simp] lemma length_castL (d : Γ ⊢ᴴ(Λ) p) (e₁ : Γ = Δ) : (d.castL e₁).length = d.length := length_cast d e₁ rfl

def castR (d : Γ ⊢ᴴ(Λ) p) (e₂ : p = q) : Γ ⊢ᴴ(Λ) q := d.cast rfl e₂

@[simp] lemma length_castR (d : Γ ⊢ᴴ(Λ) p) (e₂ : p = q) : (d.castR e₂).length = d.length := length_cast d rfl e₂

end DerivationH

def ProofH.length (d : ⊢ᴴ(Λ) p) : ℕ := DerivationH.length Λ (by simpa using d)

lemma ProvableH.dne : (⊢ᴴ(Λ)! ~~p) → (⊢ᴴ(Λ)! p) := by
  intro d;
  have h₁ := @DerivationH.dne _ Λ ∅ p;
  have h₂ := d.some; simp [ProofH, DerivationH] at h₂;
  simp_all [ProvableH, ProofH, DerivationH];
  exact ⟨(DerivationH.modus_ponens h₁ h₂)⟩


namespace LogicK

abbrev DerivationH := @Hilbert.DerivationH α 𝐊

instance : LogicK (Formula α) where
  Bew            := DerivationH
  axm            := DerivationH.axm;
  weakening'     := DerivationH.wk;
  neg            := rfl;
  modus_ponens   := by intro Γ p q hpq hp; exact ⟨@DerivationH.modus_ponens _ _ Γ p q hpq.some hp.some⟩;
  necessitation  := by intro Γ p hp; exact ⟨@DerivationH.necessitation _ _ Γ p hp.some⟩
  verum Γ        := ⟨DerivationH.verum Γ⟩
  imply₁ Γ p q   := ⟨DerivationH.imply₁ Γ p q⟩
  imply₂ Γ p q r := ⟨DerivationH.imply₂ Γ p q r⟩
  conj₁ Γ p q    := ⟨DerivationH.conj₁ Γ p q⟩
  conj₂ Γ p q    := ⟨DerivationH.conj₂ Γ p q⟩
  conj₃ Γ p q    := ⟨DerivationH.conj₃ Γ p q⟩
  disj₁ Γ p q    := ⟨DerivationH.disj₁ Γ p q⟩
  disj₂ Γ p q    := ⟨DerivationH.disj₂ Γ p q⟩
  disj₃ Γ p q r  := ⟨DerivationH.disj₃ Γ p q r⟩
  explode Γ p    := ⟨DerivationH.explode Γ p⟩
  dne Γ p        := ⟨DerivationH.dne Γ p⟩
  K Γ p q        := ⟨DerivationH.maxm (by simp)⟩

end LogicK


namespace LogicS4

abbrev DerivationH := @Hilbert.DerivationH α 𝐒𝟒

/--
  TODO: S5なども同様にやればよいが，もっと省略出来ないのだろうか？
-/
instance : LogicS4 (Formula α) where
  Bew            := DerivationH
  axm            := DerivationH.axm;
  weakening'     := DerivationH.wk;
  neg            := rfl;
  modus_ponens   := by intro Γ p q hpq hp; exact ⟨@DerivationH.modus_ponens _ _ Γ p q hpq.some hp.some⟩;
  necessitation  := by intro Γ p hp; exact ⟨@DerivationH.necessitation _ _ Γ p hp.some⟩
  verum Γ        := ⟨DerivationH.verum Γ⟩
  imply₁ Γ p q   := ⟨DerivationH.imply₁ Γ p q⟩
  imply₂ Γ p q r := ⟨DerivationH.imply₂ Γ p q r⟩
  conj₁ Γ p q    := ⟨DerivationH.conj₁ Γ p q⟩
  conj₂ Γ p q    := ⟨DerivationH.conj₂ Γ p q⟩
  conj₃ Γ p q    := ⟨DerivationH.conj₃ Γ p q⟩
  disj₁ Γ p q    := ⟨DerivationH.disj₁ Γ p q⟩
  disj₂ Γ p q    := ⟨DerivationH.disj₂ Γ p q⟩
  disj₃ Γ p q r  := ⟨DerivationH.disj₃ Γ p q r⟩
  explode Γ p    := ⟨DerivationH.explode Γ p⟩
  dne Γ p        := ⟨DerivationH.dne Γ p⟩
  K Γ p q        := ⟨DerivationH.maxm (by simp)⟩
  T Γ p          := ⟨DerivationH.maxm (by simp)⟩
  A4 Γ p         := ⟨DerivationH.maxm (by simp)⟩

end LogicS4


namespace LogicS5

abbrev DerivationH := @Hilbert.DerivationH α 𝐒𝟓

end LogicS5


namespace LogicGL

abbrev DerivationH := @Hilbert.DerivationH α 𝐆𝐋

end LogicGL


namespace LogicS4Dot2

abbrev DerivationH := @Hilbert.DerivationH α 𝐒𝟒.𝟐

end LogicS4Dot2


namespace LogicS4Dot3

abbrev DerivationH := @Hilbert.DerivationH α 𝐒𝟒.𝟑

end LogicS4Dot3


namespace LogicS4Grz

abbrev DerivationH := @Hilbert.DerivationH α 𝐒𝟒𝐆𝐫𝐳

end LogicS4Grz

end Hilbert

end Modal

end LO
