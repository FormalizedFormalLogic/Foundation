import Logic.Logic.HilbertStyle2
import Logic.Modal.Normal.Formula
import Logic.Modal.Normal.Axioms
import Logic.Modal.Normal.Logics

namespace LO

namespace Hilbert

open LO.Modal.Normal

variable {F : Type u} [ModalLogicSymbol F] (Bew : Set F → F → Sort*)

class HasNecessitation where
  necessitation {Γ : Set F} {p : F} : (Bew Γ p) → (Bew Γ (□p))

class HasAxiomK where
  K (Γ : Set F) (p q : F) : Bew Γ $ AxiomK p q

class HasAxiomT where
  T (Γ : Set F) (p : F) : Bew Γ $ AxiomT p

class HasAxiomD where
  D (Γ : Set F) (p : F) : Bew Γ $ AxiomD p

class HasAxiomB where
  B (Γ : Set F) (p q : F) : Bew Γ $ AxiomB p

class HasAxiom4 where
  A4 (Γ : Set F) (p : F) : Bew Γ $ Axiom4 p

class HasAxiom5 where
  A5 (Γ : Set F) (p : F) : Bew Γ $ Axiom5 p

class HasAxiomL where
  L (Γ : Set F) (p : F) : Bew Γ $ AxiomL p

class HasAxiomDot2 where
  Dot2 (Γ : Set F) (p : F) : Bew Γ $ AxiomDot2 p

class HasAxiomDot3 where
  Dot3 (Γ : Set F) (p q : F) : Bew Γ $ AxiomDot3 p q

class HasAxiomGrz where
  Grz (Γ : Set F) (p : F) : Bew Γ $ AxiomGrz p

/-- McKinsey Axiom -/
class HasAxiomM where
  M (Γ : Set F) (p : F) : Bew Γ $ AxiomM p

class HasAxiomCD where
  CD (Γ : Set F) (p : F) : Bew Γ $ AxiomCD p

class HasAxiomC4 where
  C4 (Γ : Set F) (p : F) : Bew Γ $ AxiomC4 p

end Hilbert


namespace Modal.Normal

open Hilbert

section Logics

variable {F : Type u} [ModalLogicSymbol F] (Bew : Set F → F → Sort*)

class LogicK.Hilbert extends Hilbert.Classical Bew, HasNecessitation Bew, HasAxiomK Bew

class LogicKD.Hilbert extends LogicK.Hilbert Bew, HasAxiomD Bew

class LogicS4.Hilbert extends LogicK.Hilbert Bew, HasAxiomT Bew, HasAxiom4 Bew

class LogicS5.Hilbert extends LogicK.Hilbert Bew, HasAxiomT Bew, HasAxiom5 Bew

class LogicGL.Hilbert extends LogicK.Hilbert Bew, HasAxiomL Bew

class LogicS4Dot2.Hilbert extends LogicK.Hilbert Bew, HasAxiomDot2 Bew

class LogicS4Dot3.Hilbert extends LogicK.Hilbert Bew, HasAxiomDot3 Bew

class LogicS4Grz.Hilbert extends LogicK.Hilbert Bew, HasAxiomGrz Bew

end Logics


variable {α : Type u}

/--
  Hilbert-style deduction system
-/
inductive Deduction (Λ : Logic α) : Set (Formula α) → (Formula α) → Type _
  | axm {Γ p}            : p ∈ Γ → Deduction Λ Γ p
  | maxm {Γ p}           : p ∈ Λ → Deduction Λ Γ p
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

variable (Λ : Logic α) (Γ : Set (Formula α)) (p : Formula α)

abbrev Deducible := Nonempty (Γ ⊢ᴹ(Λ) p)
notation:45 Γ " ⊢ᴹ(" Λ ")! " p => Deducible Λ Γ p

abbrev Undeducible := ¬(Γ ⊢ᴹ(Λ)! p)
notation:45 Γ " ⊬ᴹ(" Λ ")! " p => Undeducible Λ Γ p

abbrev Proof := ∅ ⊢ᴹ(Λ) p
notation:45 "⊢ᴹ(" Λ ") " p => Proof Λ p

abbrev Provable := Nonempty (⊢ᴹ(Λ) p)
notation:45 "⊢ᴹ(" Λ ")! " p => Provable Λ p

abbrev Unprovable := IsEmpty (⊢ᴹ(Λ) p)
notation:45 "⊬ᴹ(" Λ ")!" p => Unprovable Λ p

namespace Deduction

def weakening' {Γ Δ p} (hs : Γ ⊆ Δ) : (Γ ⊢ᴹ(Λ) p) → (Δ ⊢ᴹ(Λ) p)
  | axm h => axm (hs h)
  | maxm h => maxm h
  | modus_ponens h₁ h₂ => by
      have ih₁ := weakening' hs h₁;
      have ih₂ := weakening' hs h₂;
      exact modus_ponens ih₁ ih₂;
  | necessitation h => by
      have ih := weakening' hs h;
      exact necessitation ih;
  | verum _ => by apply verum
  | imply₁ _ _ _ => by apply imply₁
  | imply₂ _ _ _ _ => by apply imply₂
  | conj₁ _ _ _ => by apply conj₁
  | conj₂ _ _ _ => by apply conj₂
  | conj₃ _ _ _ => by apply conj₃
  | disj₁ _ _ _ => by apply disj₁
  | disj₂ _ _ _ => by apply disj₂
  | disj₃ _ _ _ _ => by apply disj₃
  | explode _ _ => by apply explode
  | dne _ _ => by apply dne

instance : Hilbert.Classical (Deduction Λ) where
  neg          := rfl;
  axm          := axm;
  weakening'   := weakening' Λ;
  modus_ponens := modus_ponens;
  verum        := verum;
  imply₁       := imply₁;
  imply₂       := imply₂;
  conj₁        := conj₁;
  conj₂        := conj₂;
  conj₃        := conj₃;
  disj₁        := disj₁;
  disj₂        := disj₂;
  disj₃        := disj₃;
  explode      := explode;
  dne          := dne;

instance : HasNecessitation (Deduction Λ) where
  necessitation := by apply necessitation;

def length {Γ : Set (Formula α)} {p : Formula α} : (Γ ⊢ᴹ(Λ) p) → ℕ
  | modus_ponens d₁ d₂ => (max d₁.length d₂.length) + 1
  | necessitation d₁ => d₁.length + 1
  | _ => 0

variable {Λ : Logic α} {Γ : Set (Formula α)} {p q : Formula α}

protected def cast (d : Γ ⊢ᴹ(Λ) p) (e₁ : Γ = Δ) (e₂ : p = q) : Δ ⊢ᴹ(Λ) q := cast (by simp [e₁,e₂]) d

@[simp] lemma length_cast (d : Γ ⊢ᴹ(Λ) p) (e₁ : Γ = Δ) (e₂ : p = q) : (d.cast e₁ e₂).length = d.length := by
  rcases e₁ with rfl; rcases e₂ with rfl; simp [Deduction.cast]

def castL (d : Γ ⊢ᴹ(Λ) p) (e₁ : Γ = Δ) : Δ ⊢ᴹ(Λ) p := d.cast e₁ rfl

@[simp] lemma length_castL (d : Γ ⊢ᴹ(Λ) p) (e₁ : Γ = Δ) : (d.castL e₁).length = d.length := length_cast d e₁ rfl

def castR (d : Γ ⊢ᴹ(Λ) p) (e₂ : p = q) : Γ ⊢ᴹ(Λ) q := d.cast rfl e₂

@[simp] lemma length_castR (d : Γ ⊢ᴹ(Λ) p) (e₂ : p = q) : (d.castR e₂).length = d.length := length_cast d rfl e₂

lemma maxm_subset {Λ Λ'} (dΛ : Γ ⊢ᴹ(Λ) p) : (Λ ⊆ Λ') → (Γ ⊢ᴹ(Λ') p) := by
  intro hΛ;
  induction dΛ with
  | axm ih => exact axm ih
  | maxm ih => exact maxm (hΛ ih)
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

variable [Union (Finset (Formula α))] [Inter (Finset (Formula α))]
variable (Γ₁ Γ₂ Δ : Finset (Formula α))

structure Partial where
  union : (Γ₁ ∪ Γ₂) = Δ
  inter : (Γ₁ ∩ Γ₂) = ∅

structure UnprovablePartial extends Partial Γ₁ Γ₂ Δ where
  unprovable := ⊬ᴹ(Λ)! ⟪Γ₁ ⟹ Γ₂⟫

end

open Deduction Hilbert

def LogicK.Hilbert.ofKSubset (h : 𝐊 ⊆ Λ) : (LogicK.Hilbert (@Deduction α Λ)) where
  K _ p q := Deduction.maxm $ Set.mem_of_subset_of_mem h (by simp);

instance : LogicK.Hilbert (@Deduction α 𝐊) := LogicK.Hilbert.ofKSubset 𝐊 Set.Subset.rfl


instance : LogicK.Hilbert (@Deduction α 𝐆𝐋) := LogicK.Hilbert.ofKSubset _ (by simp)

instance : LogicGL.Hilbert (@Deduction α 𝐆𝐋) where
  L _ _ := by apply Deduction.maxm; simp;


def LogicS4.Hilbert.ofS4Subset (_ : 𝐒𝟒 ⊆ Λ) : (LogicS4.Hilbert (@Deduction α Λ)) where
  K _ p q := Deduction.maxm $ Set.mem_of_subset_of_mem (by assumption) (by simp);
  T _ p := Deduction.maxm $ Set.mem_of_subset_of_mem (by assumption) (by simp);
  A4 _ p := Deduction.maxm $ Set.mem_of_subset_of_mem (by assumption) (by simp);

instance : LogicS4.Hilbert (@Deduction α 𝐒𝟒) := LogicS4.Hilbert.ofS4Subset 𝐒𝟒 Set.Subset.rfl


instance : LogicS4.Hilbert (@Deduction α 𝐒𝟒.𝟐) := LogicS4.Hilbert.ofS4Subset _ (by simp)

instance : LogicS4Dot2.Hilbert (@Deduction α 𝐒𝟒.𝟐) where
  Dot2 _ _ := by apply Deduction.maxm; simp;


instance : LogicS4.Hilbert (@Deduction α 𝐒𝟒.𝟑) := LogicS4.Hilbert.ofS4Subset _ (by simp)

instance : LogicS4Dot3.Hilbert (@Deduction α 𝐒𝟒.𝟑) where
  Dot3 _ p q := by apply Deduction.maxm; apply Set.mem_union_right; existsi p, q; simp;


instance : LogicS4.Hilbert (@Deduction α 𝐒𝟒𝐆𝐫𝐳) := LogicS4.Hilbert.ofS4Subset _ (by simp)

instance : LogicS4Grz.Hilbert (@Deduction α 𝐒𝟒𝐆𝐫𝐳) where
  Grz _ _ := by apply Deduction.maxm; simp;


def LogicS5.Hilbert.ofS5Subset (_ : 𝐒𝟓 ⊆ Λ) : (LogicS5.Hilbert (@Deduction α Λ)) where
  K _ p q := Deduction.maxm $ Set.mem_of_subset_of_mem (by assumption) (by simp);
  T _ p := Deduction.maxm $ Set.mem_of_subset_of_mem (by assumption) (by simp);
  A5 _ p := Deduction.maxm $ Set.mem_of_subset_of_mem (by assumption) (by simp);

instance : LogicS5.Hilbert (@Deduction α 𝐒𝟓) := LogicS5.Hilbert.ofS5Subset 𝐒𝟓 Set.Subset.rfl

end Modal.Normal

end LO
