import Logic.Logic.System
import Logic.Modal.Basic.Formula2

namespace LO

namespace Modal

variable (α : Type*)

structure Frame (α : Type*) where
  nonempty : Nonempty α
  rel : α → α → Prop

namespace Frame

class Finite extends Frame α where
  finite : Finite α

variable {α : Type*} (f : Frame α)

local infix:50 " ≺ " => f.rel

@[simp] def Reflexive := _root_.Reflexive f.rel

@[simp] def Transitive := _root_.Transitive f.rel

@[simp] def Symmetric := _root_.Symmetric f.rel

@[simp] def Euclidean := ∀ ⦃w₁ w₂ w₃⦄, w₁ ≺ w₂ → w₁ ≺ w₃ → (w₂ ≺ w₃)

@[simp] def Serial := ∀w₁, ∃w₂, w₁ ≺ w₂

@[simp] def Directed := ∀ ⦃w₁ w₂ w₃⦄, ((w₁ ≺ w₂ ∧ w₂ ≺ w₃) → ∃ w₄, w₂ ≺ w₄ ∧ w₃ ≺ w₄)

@[simp] def InfiniteAscent := ∃ (f : ℕ → α), ∀ n, f n ≺ f (n+1)

end Frame

structure Model (α β : Type*) extends Frame α where
  val : α → β → Prop

def trivialVal (α β : Type*) : α → β → Prop := λ _ _ => True

namespace Formula

variable {α β : Type*}

def satisfies (m : Model α β) (w : α) : Formula β → Prop
  | atom  p => m.val w p
  | ⊤       => True
  | ⊥       => False
  | p ⋏ q   => p.satisfies m w ∧ q.satisfies m w
  | p ⋎ q   => p.satisfies m w ∨ q.satisfies m w
  | p ⟶ q  => p.satisfies m w → q.satisfies m w
  | □p      => ∀w', m.rel w w' → p.satisfies m w'
  | ◇p     => ∃w', m.rel w w' ∧ p.satisfies m w'

notation "[" m "," w "] ⊨ˢ " p => satisfies m w p
notation "[" m "," w "] ⊭ˢ " p => ¬([m, w] ⊨ˢ p)

notation "[" f "," v "," w "] ⊨ˢ " p => [(Model.mk f v), w] ⊨ˢ p
notation "[" f "," v "," w "] ⊭ˢ " p => ¬([f, v, w] ⊨ˢ p)

lemma satisfies_box : ([m, w] ⊨ˢ □p) ↔ (∀w', m.rel w w' → ([m, w'] ⊨ˢ p)) := by simp [satisfies];

lemma satisfies_dia : ([m, w] ⊨ˢ ◇p) ↔ (∃w', m.rel w w' ∧ ([m, w'] ⊨ˢ p)) := by simp [satisfies];

lemma satisfies_neg : ([m, w] ⊨ˢ (neg p)) ↔ ([m, w] ⊭ˢ p) := by simp [satisfies];

lemma satisfies_neg' : ([m, w] ⊨ˢ ~p) ↔ ([m, w] ⊭ˢ p) := by simp [satisfies];

lemma satisfies_imp : ([m, w] ⊨ˢ p ⟶ q) ↔ ([m, w] ⊨ˢ p) → ([m, w] ⊨ˢ q) := by simp [satisfies];

@[simp]
def models (m : Model α β) (p : Formula β) := ∀w, ([m, w] ⊨ˢ p)
notation m " ⊨ᵐ "  p => models m p
notation m " ⊭ᵐ "  p => ¬(m ⊨ᵐ p)

lemma models_MP {m : Model α β} : (m ⊨ᵐ p ⟶ q) ↔ (m ⊨ᵐ p) → (m ⊨ᵐ q) := by sorry;

@[simp]
def frames (f : Frame α) (p : Formula β) := ∀v, (Model.mk f v) ⊨ᵐ p
notation f " ⊨ᶠ "  p => frames f p
notation f " ⊭ᶠ "  p => ¬(f ⊨ᶠ p)

lemma frames_MP {f : Frame α} : (f ⊨ᶠ p ⟶ q) ↔ (f ⊨ᶠ p) → (f ⊨ᶠ q) := by
  apply Iff.intro;
  . intro h₁ h₂ v;
    exact models_MP.mp (h₁ v) (h₂ v);
  . intro h V;
    sorry;

lemma frames_Nec {f : Frame α} : (f ⊨ᶠ p) → (f ⊨ᶠ □p) := by
  intro h v w;
  simp [satisfies];
  aesop;

variable (f : Frame α) {p q : Formula β}

lemma frames_K : f ⊨ᶠ □(p ⟶ q) ⟶ □p ⟶ □q := by
  intro v w;
  simp [satisfies_imp];
  simp [satisfies];
  intro h₁ h₂ w' rw';
  have this := h₁ w' rw';
  simp [satisfies_neg] at this;
  aesop;

lemma defines_T : (f ⊨ᶠ □p ⟶ p) ↔ (f.Reflexive) := by
  constructor;
  . sorry;
  . intro hRefl v w;
    simp [satisfies];
    aesop;

lemma defines_D  : (f ⊨ᶠ □p ⟶ ◇p) ↔ (f.Serial) := by
  apply Iff.intro;
  . intro h;
    by_contra hC; simp at hC;
    have ⟨w₁, r₁⟩ := hC;
    simp [satisfies_imp] at h;
    let V : α → β → Prop := λ _ _ => True;
    have : [⟨f, V⟩, w₁] ⊨ˢ □p := by simp [satisfies]; simp_all;
    have : [⟨f, V⟩, w₁] ⊭ˢ ◇p := by simp [satisfies]; simp_all;
    aesop;
  . intro hSerial v w₁;
    let ⟨w₂, r₁₂⟩ := hSerial w₁;
    simp [satisfies_imp, satisfies];
    aesop;

lemma defines_B : (f ⊨ᶠ p ⟶ □◇p) ↔ (f.Symmetric) := by
  constructor;
  . sorry;
  . simp [satisfies_imp, satisfies]; aesop;

lemma defines_A4 : (f ⊨ᶠ □p ⟶ □□p) ↔ (f.Transitive) := by
  constructor;
  . sorry;
  . intro hTrans v w₁;
    simp [satisfies_imp, satisfies];
    aesop;

lemma defines_A5 : (f ⊨ᶠ ◇p ⟶ □◇p) ↔ (f.Euclidean) := by
  constructor;
  . sorry;
  . intro hEucl v w₁;
    simp [satisfies_imp, satisfies];
    aesop;

lemma defines_L : (f ⊨ᶠ □(□p ⟶ p) ⟶ □p) ↔ (f.Transitive ∧ ¬f.InfiniteAscent) := by
  constructor;
  . sorry;
  . sorry;

lemma defines_Dot2 : (f ⊨ᶠ □p ⟶ ◇□p) ↔ (f.Directed) := by
  constructor;
  . sorry;
  . sorry;

end Formula

end Modal

end LO
