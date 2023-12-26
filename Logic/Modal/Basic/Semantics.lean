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

@[simp] def Euclidean := ∀ ⦃x y z⦄, x ≺ y → x ≺ z → (y ≺ z)

@[simp] def Serial := ∀x, ∃y, x ≺ y

@[simp] def Directed := ∀ ⦃x y z⦄, ((x ≺ y ∧ y ≺ z) → ∃ w, y ≺ w ∧ z ≺ w)

@[simp] def InfiniteAscent := ∃ (f : ℕ → α), ∀ n, f n ≺ f (n+1)

end Frame

structure Model (α β : Type*) extends Frame α where
  val : β → Set α

namespace Formula

variable {α β : Type*}

def satisfies (m : Model α β) (w : α) : Formula β → Prop
  | atom  p => w ∈ m.val p
  | natom p => w ∉ m.val p
  | ⊤       => True
  | ⊥       => False
  | p ⋏ q   => p.satisfies m w ∧ q.satisfies m w
  | p ⋎ q   => p.satisfies m w ∨ q.satisfies m w
  | □p      => ∀w', m.rel w w' → p.satisfies m w'
  | ◇p     => ∃w', m.rel w w' ∧ p.satisfies m w'

notation "[" m "," w "] ⊨ˢ " p => satisfies m w p
notation "[" m "," w "] ⊭ˢ " p => ¬([m, w] ⊨ˢ p)

notation "[" f "," v "," w "] ⊨ˢ " p => [(Model.mk f v), w] ⊨ˢ p
notation "[" f "," v "," w "] ⊭ˢ " p => ¬([f, v, w] ⊨ˢ p)

lemma satisfies_box : ([m, w] ⊨ˢ □p) ↔ (∀w', m.rel w w' → ([m, w'] ⊨ˢ p)) := by simp [satisfies];

lemma satisfies_dia : ([m, w] ⊨ˢ ◇p) ↔ (∃w', m.rel w w' ∧ ([m, w'] ⊨ˢ p)) := by simp [satisfies];

lemma satisfies_neg : ([m, w] ⊨ˢ (neg p)) ↔ ([m, w] ⊭ˢ p) := by
  sorry;

lemma satisfies_neg' : ([m, w] ⊨ˢ ~p) ↔ ([m, w] ⊭ˢ p) := by
  sorry;

lemma satisfies_imp : ([m, w] ⊨ˢ p ⟶ q) ↔ (([m, w] ⊭ˢ p) ∨ ([m, w] ⊨ˢ q)) := by
  simp [satisfies];
  simp [satisfies_neg];

lemma satisfies_imp2 : ([m, w] ⊨ˢ p ⟶ q) ↔ (([m, w] ⊨ˢ p) → ([m, w] ⊨ˢ q)) := by
  simp [satisfies_imp];
  sorry;

@[simp]
def models (m : Model α β) (p : Formula β) := ∀w, ([m, w] ⊨ˢ p)
notation m " ⊨ᵐ "  p => models m p
notation m " ⊭ᵐ "  p => ¬(m ⊨ᵐ p)

@[simp]
def frames (f : Frame α) (p : Formula β) := ∀v, (Model.mk f v) ⊨ᵐ p
notation f " ⊨ᶠ "  p => frames f p
notation f " ⊭ᶠ "  p => ¬(f ⊨ᶠ p)

lemma frames_imp2 : (f ⊨ᶠ p ⟶ q) ↔ ((f ⊨ᶠ p) → (f ⊨ᶠ q)) := by sorry;

variable (f : Frame α) {p q : Formula β}

lemma framesMP {f : Frame α} : (f ⊨ᶠ p ⟶ q) → (f ⊨ᶠ p) → (f ⊨ᶠ q) := by
  intro h₁ h₂ v;
  simp [satisfies_imp2] at h₁;
  aesop;

lemma framesNec {f : Frame α} : (f ⊨ᶠ p) → (f ⊨ᶠ □p) := by
  intro h v w;
  simp [satisfies];
  aesop;

lemma framesK : f ⊨ᶠ □(p ⟶ q) ⟶ □p ⟶ □q := by
  intro v w;
  simp [satisfies_imp2];
  simp [satisfies];
  intro h₁ h₂ w' rw';
  have this := h₁ w' rw';
  simp [satisfies_neg] at this;
  aesop;

lemma defineT : (f ⊨ᶠ □p ⟶ p) ↔ (f.Reflexive) := by
  constructor;
  . sorry;
  . intro hRefl v w;
    simp [satisfies_imp2];
    simp [satisfies];
    aesop;

lemma defineD : (f ⊨ᶠ □p ⟶ ◇p) ↔ (f.Serial) := by
  apply Iff.intro;
  . sorry;
  . intro hSerial v w₁;
    let ⟨w₂, r₁₂⟩ := hSerial w₁;
    simp [satisfies_imp2];
    simp [satisfies];
    aesop;

lemma defineB : (f ⊨ᶠ p ⟶ □◇p) ↔ (f.Symmetric) := by
  constructor;
  . sorry;
  . intro hSymm v w₁;
    simp [satisfies_imp2];
    simp [satisfies];
    aesop;

lemma defineA4 : (f ⊨ᶠ □p ⟶ □□p) ↔ (f.Transitive) := by
  constructor;
  . sorry;
  . intro hTrans v w₁;
    simp [satisfies_imp2];
    simp [satisfies];
    aesop;

lemma defineA5 : (f ⊨ᶠ ◇p ⟶ □◇p) ↔ (f.Euclidean) := by
  constructor;
  . sorry;
  . intro hEucl v w₁;
    simp [satisfies_imp2];
    simp [satisfies];
    aesop;

lemma defineL : (f ⊨ᶠ □(□p ⟶ p) ⟶ □p) ↔ (f.Transitive ∧ ¬f.InfiniteAscent) := by
  constructor;
  . sorry;
  . sorry;

lemma defineDot2 : (f ⊨ᶠ □p ⟶ ◇□p) ↔ (f.Directed) := by
  constructor;
  . sorry;
  . sorry;

end Formula

end Modal

end LO
