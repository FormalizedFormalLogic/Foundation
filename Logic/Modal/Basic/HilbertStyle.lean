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

@[elab_as_elim]
def rec'
  {C : (Γ : Set (Formula α)) → (p : Formula α) → Sort _}
  (haxm : ∀ {Γ p}, (h : p ∈ Γ) → C Γ p)
  (hmaxm : ∀ {Γ p}, (h : p ∈ Λ) → C Γ p)
  (hwk : ∀ {Γ Δ p} (_ : Γ ⊆ Δ) (_ : Γ ⊢ᴴ(Λ) p), C Γ p → C Δ p)
  (hmodus_ponens : ∀ {Γ p q} (_ : Γ ⊢ᴴ(Λ) (p ⟶ q)) (_ : Γ ⊢ᴴ(Λ) p), C Γ (p ⟶ q) → C Γ p → C Γ q)
  (hnecessitation : ∀ {Γ p} (_ : Γ ⊢ᴴ(Λ) p), C Γ p → C Γ (□p))
  (hverum : ∀ (Γ), C Γ ⊤)
  (himply₁ : ∀ (Γ p q), C Γ (p ⟶ q ⟶ p))
  (himply₂ : ∀ (Γ p q r), C Γ ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r))
  (hconj₁ : ∀ (Γ p q), C Γ (p ⋏ q ⟶ p))
  (hconj₂ : ∀ (Γ p q), C Γ (p ⋏ q ⟶ q))
  (hconj₃ : ∀ (Γ p q), C Γ (p ⟶ q ⟶ p ⋏ q))
  (hdisj₁ : ∀ (Γ p q), C Γ (p ⟶ p ⋎ q))
  (hdisj₂ : ∀ (Γ p q), C Γ (q ⟶ p ⋎ q))
  (hdisj₃ : ∀ (Γ p q r), C Γ ((p ⟶ r) ⟶ (q ⟶ r) ⟶ (p ⋎ q ⟶ r)))
  (hexplode : ∀ (Γ p), C Γ (⊥ ⟶ p))
  (hdne : ∀ (Γ p), C Γ (~~p ⟶ p))
  : ∀ {Γ p}, (d : Γ ⊢ᴴ(Λ) p) → (C Γ p)
  | _, _, axm h => haxm h
  | _, _, maxm h => hmaxm h
  | _, _, wk h d => hwk h d
    (rec' haxm hmaxm hwk hmodus_ponens hnecessitation hverum himply₁ himply₂ hconj₁ hconj₂ hconj₃ hdisj₁ hdisj₂ hdisj₃ hexplode hdne d)
  | _, _, modus_ponens d₁ d₂ =>
    hmodus_ponens d₁ d₂
    (rec' haxm hmaxm hwk hmodus_ponens hnecessitation hverum himply₁ himply₂ hconj₁ hconj₂ hconj₃ hdisj₁ hdisj₂ hdisj₃ hexplode hdne d₁)
    (rec' haxm hmaxm hwk hmodus_ponens hnecessitation hverum himply₁ himply₂ hconj₁ hconj₂ hconj₃ hdisj₁ hdisj₂ hdisj₃ hexplode hdne d₂)
  | _, _, necessitation d =>
    hnecessitation d
    (rec' haxm hmaxm hwk hmodus_ponens hnecessitation hverum himply₁ himply₂ hconj₁ hconj₂ hconj₃ hdisj₁ hdisj₂ hdisj₃ hexplode hdne d)
  | _, _, (verum Γ) => hverum Γ
  | _, _, (imply₁ Γ p q) => himply₁ Γ p q
  | _, _, (imply₂ Γ p q r) => himply₂ Γ p q r
  | _, _, (conj₁ Γ p q) => hconj₁ Γ p q
  | _, _, (conj₂ Γ p q) => hconj₂ Γ p q
  | _, _, (conj₃ Γ p q) => hconj₃ Γ p q
  | _, _, (disj₁ Γ p q) => hdisj₁ Γ p q
  | _, _, (disj₂ Γ p q) => hdisj₂ Γ p q
  | _, _, (disj₃ Γ p q r) => hdisj₃ Γ p q r
  | _, _, (explode Γ p) => hexplode Γ p
  | _, _, (dne Γ p) => hdne Γ p

end DerivationH

namespace LogicK

@[simp]
private def ModalAxioms : (Set (Formula α)) := { □(p ⟶ q) ⟶ □p ⟶ □q | (p : Formula α) (q : Formula α)}

notation "𝗞" => ModalAxioms

abbrev DerivationH := @Hilbert.DerivationH α 𝗞

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

lemma ProvableH.dne : (⊢ᴴ(𝗞)! ~~p) → (⊢ᴴ(𝗞)! p) := by
  intro d;
  have h₁ := @DerivationH.dne _ 𝗞 ∅ p;
  have h₂ := d.some; simp [ProofH, DerivationH] at h₂;
  simp_all [ProvableH, ProofH, DerivationH];
  exact ⟨(DerivationH.modus_ponens h₁ h₂)⟩

end LogicK

namespace LogicS4

@[simp]
private def ModalAxioms : Set (Formula α) := 𝗞
  ∪ { □p ⟶ p | p : Formula α} -- T
  ∪ { □p ⟶ □□p | p : Formula α} -- 4

notation "𝗦𝟰" => ModalAxioms

abbrev DerivationH := @Hilbert.DerivationH α 𝗦𝟰

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

@[simp]
private def ModalAxioms : Set (Formula α) :=𝗞
  ∪ { □p ⟶ p | p : Formula α} -- T
  ∪ { p ⟶ □◇p | p : Formula α} -- B
  ∪ { □p ⟶ □□p | p : Formula α} -- 4

notation "𝗦𝟱" => ModalAxioms

abbrev DerivationH := @Hilbert.DerivationH α 𝗦𝟱

end LogicS5


namespace LogicGL

variable {α : Type u}

@[simp]
private def ModalAxioms : Set (Formula α) := 𝗞 ∪ { □(□p ⟶ p) ⟶ □p | p : Formula α} -- L

notation "𝗚𝗟" => ModalAxioms

abbrev DerivationH := @Hilbert.DerivationH α 𝗚𝗟

end LogicGL


namespace LogicS4Dot2

@[simp]
private def ModalAxioms : Set (Formula α) := 𝗦𝟰 ∪ { ◇□p ⟶ □◇p | p : Formula α}  -- Dot2

notation "𝗦𝟰.𝟮" => ModalAxioms

abbrev DerivationH := @Hilbert.DerivationH α 𝗦𝟰.𝟮

end LogicS4Dot2


namespace LogicS4Dot3

@[simp]
private def ModalAxioms : Set (Formula α) := 𝗦𝟰 ∪ { □(□p ⟶ □q) ⋎ □(□q ⟶ □p) | (p : Formula α) (q : Formula α) }  -- Dot3

notation "𝗦𝟰.𝟯" => ModalAxioms

abbrev DerivationH := @Hilbert.DerivationH α 𝗦𝟰.𝟯

end LogicS4Dot3


namespace LogicS4Grz

@[simp]
private def ModalAxioms : Set (Formula α) := 𝗦𝟰 ∪ { □(□(p ⟶ □p) ⟶ p) ⟶ p | p : Formula α}  -- Grz

notation "𝗦𝟰𝗚𝗿𝘇" => ModalAxioms

abbrev DerivationH := @Hilbert.DerivationH α 𝗦𝟰𝗚𝗿𝘇

end LogicS4Grz


end Hilbert

end Modal

end LO
