import Logic.Logic.HilbertStyle2
import Logic.Modal.Basic.Formula

namespace LO

namespace Modal

namespace Hilbert

section Axioms

variable {F : Type u} [ModalLogicSymbol F] (Bew : Set F → F → Sort*)

class HasNecessitation where
  necessitation {Γ : Set F} {p : F} : (Bew Γ p) → (Bew Γ (□p))

class HasAxiomK where
  K (Γ : Set F) (p q : F) : Bew Γ (□(p ⟶ q) ⟶ □p ⟶ □q)

class HasAxiomT where
  T (Γ : Set F) (p : F) : Bew Γ (□p ⟶ p)

class HasAxiomD where
  D (Γ : Set F) (p : F) : Bew Γ (□p ⟶ ◇p)

class HasAxiomB where
  B (Γ : Set F) (p q : F) : Bew Γ (p ⟶ □◇p)

class HasAxiom4 where
  A4 (Γ : Set F) (p : F) : Bew Γ (□p ⟶ □□p)

class HasAxiom5 where
  A5 (Γ : Set F) (p : F) : Bew Γ (◇p ⟶ □◇p)

class HasAxiomL where
  L (Γ : Set F) (p : F) : Bew Γ (□(□p ⟶ p) ⟶ □p)

class HasAxiomDot2 where
  Dot2 (Γ : Set F) (p : F) : Bew Γ (◇□p ⟶ □◇p)

class HasAxiomDot3 where
  Dot3 (Γ : Set F) (p q : F) : Bew Γ (□(□p ⟶ □q) ⋎ □(□q ⟶ □p))

class HasAxiomGrz where
  Grz (Γ : Set F) (p : F) : Bew Γ (□(□(p ⟶ □p) ⟶ p) ⟶ p)

/-- McKinsey Axiom -/
class HasAxiomM where
  M (Γ : Set F) (p : F) : Bew Γ (□◇p ⟶ ◇□p)

class HasAxiomCD where
  CD (Γ : Set F) (p : F) : Bew Γ (◇p ⟶ □p)

class HasAxiomC4 where
  C4 (Γ : Set F) (p : F) : Bew Γ (□□p ⟶ □p)

class LogicK extends Hilbert.Classical Bew, HasNecessitation Bew, HasAxiomK Bew

class LogicKD extends LogicK Bew, HasAxiomD Bew

class LogicKT extends LogicK Bew, HasAxiomT Bew

class LogicGL extends LogicK Bew, HasAxiomL Bew

class LogicS4 extends LogicK Bew, HasAxiomT Bew, HasAxiom4 Bew

class LogicS4Dot2 extends LogicS4 Bew, HasAxiomDot2 Bew

class LogicS4Dot3 extends LogicS4 Bew, HasAxiomDot3 Bew

class LogicS4Grz extends LogicS4 Bew, HasAxiomGrz Bew

class LogicS5 extends LogicK Bew, HasAxiomT Bew, HasAxiom5 Bew

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

instance : Hilbert.Classical (Deduction Λ) where
  neg          := rfl;
  axm          := by apply axm;
  weakening'   := by apply wk;
  modus_ponens := by apply modus_ponens;
  verum        := by apply verum;
  imply₁       := by apply imply₁;
  imply₂       := by apply imply₂;
  conj₁        := by apply conj₁;
  conj₂        := by apply conj₂;
  conj₃        := by apply conj₃;
  disj₁        := by apply disj₁;
  disj₂        := by apply disj₂;
  disj₃        := by apply disj₃;
  explode      := by apply explode;
  dne          := by apply dne;

instance : HasNecessitation (Deduction Λ) where
  necessitation := by apply necessitation;

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

instance inst (h : 𝐊 ⊆ Λ) : (LogicK (@Deduction α Λ)) where
  K _ p q := Deduction.maxm $ Set.mem_of_subset_of_mem h (by simp);

instance : LogicK (@Deduction α 𝐊) := inst 𝐊 Set.Subset.rfl

end LogicK


namespace LogicGL

instance : LogicK (@Deduction α 𝐆𝐋) := LogicK.inst _ (by simp [axiomsGL.ctx])

instance : LogicGL (@Deduction α 𝐆𝐋) where
  L _ _ := by apply Deduction.maxm; simp;

end LogicGL


namespace LogicS4

instance inst (_ : 𝐒𝟒 ⊆ Λ) : (LogicS4 (@Deduction α Λ)) where
  K _ p q := Deduction.maxm $ Set.mem_of_subset_of_mem (by assumption) (by simp);
  T _ p := Deduction.maxm $ Set.mem_of_subset_of_mem (by assumption) (by simp);
  A4 _ p := Deduction.maxm $ Set.mem_of_subset_of_mem (by assumption) (by simp);

instance : LogicS4 (@Deduction α 𝐒𝟒) := inst 𝐒𝟒 Set.Subset.rfl

end LogicS4


namespace LogicS4Dot2

instance : LogicS4 (@Deduction α 𝐒𝟒.𝟐) := LogicS4.inst _ (by simp)

instance : LogicS4Dot2 (@Deduction α 𝐒𝟒.𝟐) where
  Dot2 _ _ := by apply Deduction.maxm; simp;

end LogicS4Dot2


namespace LogicS4Dot3

instance : LogicS4 (@Deduction α 𝐒𝟒.𝟑) := LogicS4.inst _ (by simp)

instance : LogicS4Dot3 (@Deduction α 𝐒𝟒.𝟑) where
  Dot3 _ p q := by apply Deduction.maxm; apply Set.mem_union_right; existsi p, q; simp;

end LogicS4Dot3


namespace LogicS4Grz

instance : LogicS4 (@Deduction α 𝐒𝟒𝐆𝐫𝐳) := LogicS4.inst _ (by simp)

instance : LogicS4Grz (@Deduction α 𝐒𝟒𝐆𝐫𝐳) where
  Grz _ _ := by apply Deduction.maxm; simp;

end LogicS4Grz


namespace LogicS5

instance inst (_ : 𝐒𝟓 ⊆ Λ) : (LogicS5 (@Deduction α Λ)) where
  K _ p q := Deduction.maxm $ Set.mem_of_subset_of_mem (by assumption) (by simp);
  T _ p := Deduction.maxm $ Set.mem_of_subset_of_mem (by assumption) (by simp);
  A5 _ p := Deduction.maxm $ Set.mem_of_subset_of_mem (by assumption) (by simp);

instance : LogicS5 (@Deduction α 𝐒𝟓) := inst 𝐒𝟓 Set.Subset.rfl

end LogicS5


end Hilbert

end Modal

end LO
