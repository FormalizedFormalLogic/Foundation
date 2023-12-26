import Logic.Logic.System
import Logic.Modal.Basic.Formula

namespace LO

namespace Modal

variable (α : Type*)

structure Frame (α : Type*) where
  rel : α → α → Prop

namespace Frame

variable {α : Type*} (f : Frame α)

local infix:50 " ≺ " => f.rel

@[simp] def Reflexive := _root_.Reflexive f.rel

@[simp] def Transitive := _root_.Transitive f.rel

@[simp] def Symmetric := _root_.Symmetric f.rel

@[simp] def Eulidean := ∀ ⦃x y z⦄, x ≺ y → x ≺ z → (y ≺ z)

@[simp] def Serial := ∀x, ∃y, x ≺ y

@[simp] def Directed := ∀ ⦃x y z⦄, ((x ≺ y ∧ y ≺ z) → ∃ w, y ≺ w ∧ z ≺ w)

@[simp] def InfiniteAscent := ∃ (f : ℕ → α), ∀ n, f n ≺ f (n+1)

end Frame

structure Model (α β : Type*) extends Frame α where
  val : β → Set α

namespace Formula

variable {α β : Type*}

def satisfy (m : Model α β) (w : α) : Formula β → Prop
  | atom  p => w ∈ m.val p
  | natom p => w ∉ m.val p
  | ⊤       => True
  | ⊥       => False
  | p ⋏ q   => p.satisfy m w ∧ q.satisfy m w
  | p ⋎ q   => p.satisfy m w ∨ q.satisfy m w
  | □p      => ∀w', m.rel w w' → p.satisfy m w'
  | ◇p     => ∃w', m.rel w w' ∧ p.satisfy m w'

notation m "," w " ⊨ˢ "  p => satisfy m w p
notation m "," w " ⊭ˢ "  p => ¬(m, w ⊨ˢ p)

lemma satisfy_neg : (m, w ⊨ˢ (neg p)) ↔ (m, w ⊭ˢ p) := by
  sorry;

lemma satisfy_imp : (m, w ⊨ˢ p ⟶ q) ↔ ((m, w ⊭ˢ p) ∨ (m, w ⊨ˢ q)) := by
  simp [satisfy];
  simp [satisfy_neg];

lemma satisfy_imp2 : (m, w ⊨ˢ p ⟶ q)↔ ((m, w ⊨ˢ p) → (m, w ⊨ˢ q)) := by
  simp [satisfy_imp];
  sorry;

@[simp]
def modelValid (m : Model α β) (p : Formula β) := ∀w, (m, w ⊨ˢ p)
notation m " ⊨ᵐ "  p => modelValid m p
notation m " ⊭ᵐ "  p => ¬(m ⊨ᵐ p)

@[simp]
def frameValid (f : Frame α) (p : Formula β) := ∀v, (Model.mk f v) ⊨ᵐ p
notation f " ⊨ᶠ "  p => frameValid f p
notation f " ⊭ᶠ "  p => ¬(f ⊨ᶠ p)

variable (f : Frame α)

lemma validNec : (f ⊨ᶠ p) → (f ⊨ᶠ □p) := by
  intro h v w;
  simp [satisfy];
  aesop;

lemma validK : f ⊨ᶠ □(p ⟶ q) ⟶ □p ⟶ □q := by
  intro v w;
  simp [satisfy_imp2];
  simp [satisfy];
  intro h₁ h₂ w' rw';
  have this := h₁ w' rw';
  simp [satisfy_neg] at this;
  aesop;

lemma defineT : (f ⊨ᶠ □p ⟶ p) ↔ (f.Reflexive) := by
  constructor;
  . sorry;
  . intro hRefl v w;
    simp [satisfy_imp2];
    simp [satisfy];
    aesop;

lemma defineD : (f ⊨ᶠ □p ⟶ ◇p) ↔ (f.Serial) := by
  constructor;
  . sorry;
  . sorry;

lemma defineB : (f ⊨ᶠ p ⟶ □◇p) ↔ (f.Symmetric) := by
  constructor;
  . sorry;
  . intro hSymm v w₁;
    simp [satisfy_imp2];
    simp [satisfy];
    aesop;

lemma defineA4 : (f ⊨ᶠ □p ⟶ □□p) ↔ (f.Transitive) := by
  constructor;
  . sorry;
  . intro hTrans v w₁;
    simp [satisfy_imp2];
    simp [satisfy];
    aesop;

lemma defineA5 : (f ⊨ᶠ ◇p ⟶ □◇p) ↔ (f.Eulidean) := by
  constructor;
  . sorry;
  . intro hEucl v w₁;
    simp [satisfy_imp2];
    simp [satisfy];
    aesop;

lemma defineL : (f ⊨ᶠ □(□p ⟶ p) ⟶ □p) ↔ (f.Transitive ∧ ¬f.InfiniteAscent) := by
  constructor;
  . sorry;
  . sorry

lemma defineDot2 : (f ⊨ᶠ □p ⟶ ◇□p) ↔ (f.Directed) := by
  constructor;
  . sorry;
  . sorry;

end Formula

end Modal

end LO
