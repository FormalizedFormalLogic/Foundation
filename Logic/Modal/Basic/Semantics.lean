import Logic.Logic.System
import Logic.Modal.Basic.Formula

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
  | ⊥       => False
  | p ⟶ q  => (p.satisfies m w) → (q.satisfies m w)
  | □p      => ∀w', m.rel w w' → p.satisfies m w'

notation w " ⊨ˢ[" m "] " p => satisfies m w p
notation w " ⊭ˢ[" m "] " p => ¬(w ⊨ˢ[m] p)

lemma satisfies_atom : (w ⊨ˢ[m] atom p) ↔ m.val w p := by simp [satisfies];

lemma satisfies_top : (w ⊨ˢ[m] ⊤) := by simp [satisfies];

lemma satisfies_bot : (w ⊨ˢ[m] ⊥) ↔ False := by simp [satisfies];

lemma satisfies_and : (w ⊨ˢ[m] p ⋏ q) ↔ (w ⊨ˢ[m] p) ∧ (w ⊨ˢ[m] q) := by simp [satisfies];

-- lemma satisfies_or : (w ⊨ˢ[m] p ⋎ q) ↔ (w ⊨ˢ[m] p) ∨ (w ⊨ˢ[m] q) := by simp [satisfies];

lemma satisfies_imp : (w ⊨ˢ[m] p ⟶ q) ↔ (w ⊨ˢ[m] p) → (w ⊨ˢ[m] q) := by simp [satisfies];

lemma satisfies_box : (w ⊨ˢ[m] □p) ↔ (∀w', m.rel w w' → (w' ⊨ˢ[m] p)) := by simp [satisfies];
lemma satisfies_dia : (w ⊨ˢ[m] ◇p) ↔ (∃w', m.rel w w' ∧ (w' ⊨ˢ[m] p)) := by simp [satisfies];

lemma satisfies_neg : (w ⊨ˢ[m] (neg p)) ↔ (w ⊭ˢ[m] p) := by simp [satisfies];
lemma satisfies_neg' : (w ⊨ˢ[m] ~p) ↔ (w ⊭ˢ[m] p) := by simp [satisfies];

@[simp]
def models (m : Model α β) (p : Formula β) := ∀w, (w ⊨ˢ[m] p)

notation "⊨ᵐ[" m "] "  p => models m p
notation "⊭ᵐ[" m "] "  p => ¬(⊨ᵐ[m] p)

lemma models_ModusPonens {m : Model α β} : (⊨ᵐ[m] p ⟶ q) → (⊨ᵐ[m] p) → (⊨ᵐ[m] q) := by simp_all [satisfies_imp];

@[simp]
def frames (f : Frame α) (p : Formula β) := ∀v, ⊨ᵐ[⟨f, v⟩] p

notation "⊨ᶠ[" f "] " p => frames f p
notation "⊭ᶠ[" f "] " p => ¬(⊨ᶠ[f] p)

lemma frames_ModusPonens {f : Frame α} : (⊨ᶠ[f] p ⟶ q) → (⊨ᶠ[f] p) → (⊨ᶠ[f] q) := by simp_all [satisfies_imp];

lemma frames_Necessitation {f : Frame α} : (⊨ᶠ[f] p) → (⊨ᶠ[f] □p) := by
  intro h v w;
  simp [satisfies];
  aesop;

variable (f : Frame α) {p q : Formula β}

lemma frames_AxiomK : ⊨ᶠ[f] □(p ⟶ q) ⟶ □p ⟶ □q := by
  intro v w;
  simp [satisfies_imp];
  simp [satisfies];
  intro h₁ h₂ w' rw';
  have this := h₁ w' rw';
  simp [satisfies_neg] at this;
  aesop;

lemma defines_T : (⊨ᶠ[f] □p ⟶ p) ↔ (f.Reflexive) := by
  constructor;
  . sorry;
  . intro hRefl v w;
    simp [satisfies];
    aesop;

lemma defines_D  : (⊨ᶠ[f] □p ⟶ ◇p) ↔ (f.Serial) := by
  apply Iff.intro;
  . intro h;
    by_contra hC; simp at hC;
    have ⟨w₁, r₁⟩ := hC;
    simp [satisfies_imp] at h;
    let V : α → β → Prop := λ _ _ => True;
    have : w₁ ⊨ˢ[⟨f, V⟩] □p := by simp [satisfies]; simp_all;
    have : w₁ ⊭ˢ[⟨f, V⟩] ◇p := by simp [satisfies]; simp_all;
    aesop;
  . intro hSerial v w₁;
    let ⟨w₂, r₁₂⟩ := hSerial w₁;
    simp [satisfies_imp, satisfies];
    aesop;

lemma defines_B : (⊨ᶠ[f] p ⟶ □◇p) ↔ (f.Symmetric) := by
  constructor;
  . sorry;
  . simp [satisfies_imp, satisfies]; aesop;

lemma defines_A4 : (⊨ᶠ[f] □p ⟶ □□p) ↔ (f.Transitive) := by
  constructor;
  . sorry;
  . intro hTrans v w₁;
    simp [satisfies_imp, satisfies];
    aesop;

lemma defines_A5 : (⊨ᶠ[f] ◇p ⟶ □◇p) ↔ (f.Euclidean) := by
  constructor;
  . sorry;
  . intro hEucl v w₁;
    simp [satisfies_imp, satisfies];
    aesop;

lemma defines_L : (⊨ᶠ[f] □(□p ⟶ p) ⟶ □p) ↔ (f.Transitive ∧ ¬f.InfiniteAscent) := by
  constructor;
  . sorry;
  . sorry;

lemma defines_Dot2 : (⊨ᶠ[f] □p ⟶ ◇□p) ↔ (f.Directed) := by
  constructor;
  . sorry;
  . sorry;

end Formula

end Modal

end LO
