import Logic.Logic.Deduction
import Logic.Modal.Normal.Formula
import Logic.Modal.Normal.Axioms
import Logic.Modal.Normal.HilbertStyle

attribute [simp] Set.subset_union_of_subset_left Set.subset_union_of_subset_right -- Finset.subset_insert

namespace LO

namespace Modal.Normal

open Hilbert

variable {α : Type u} [DecidableEq α]

/--
  Hilbert-style deduction system
-/
inductive Deduction (Λ : AxiomSet α) : (Theory α) → (Formula α) → Type _
  | axm {Γ p}            : p ∈ Γ → Deduction Λ Γ p
  | maxm {Γ p}           : p ∈ Λ → Deduction Λ Γ p
  | modus_ponens {Γ₁ Γ₂ p q} : Deduction Λ Γ₁ (p ⟶ q) → Deduction Λ Γ₂ p → Deduction Λ (Γ₁ ∪ Γ₂) q
  | necessitation {Γ p}  : Deduction Λ ∅ p → Deduction Λ Γ (□p)
  | verum (Γ)            : Deduction Λ Γ ⊤
  | imply₁ (Γ) (p q)     : Deduction Λ Γ (p ⟶ q ⟶ p)
  | imply₂ (Γ) (p q r)   : Deduction Λ Γ ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r)
  | conj₁ (Γ) (p q)      : Deduction Λ Γ (p ⋏ q ⟶ p)
  | conj₂ (Γ) (p q)      : Deduction Λ Γ (p ⋏ q ⟶ q)
  | conj₃ (Γ) (p q)      : Deduction Λ Γ (p ⟶ q ⟶ p ⋏ q)
  | disj₁ (Γ) (p q)      : Deduction Λ Γ (p ⟶ p ⋎ q)
  | disj₂ (Γ) (p q)      : Deduction Λ Γ (q ⟶ p ⋎ q)
  | disj₃ (Γ) (p q r)    : Deduction Λ Γ ((p ⟶ r) ⟶ (q ⟶ r) ⟶ (p ⋎ q ⟶ r))
  | dne (Γ p)            : Deduction Λ Γ (~~p ⟶ p)

notation:45 Γ " ⊢ᴹ[" Λ "] " p => Deduction Λ Γ p

variable (Λ : AxiomSet α) (Γ : Theory α) (p : Formula α)

abbrev Deducible := Nonempty (Γ ⊢ᴹ[Λ] p)
notation:45 Γ " ⊢ᴹ[" Λ "]! " p => Deducible Λ Γ p

abbrev Undeducible := ¬(Γ ⊢ᴹ[Λ]! p)
notation:45 Γ " ⊬ᴹ[" Λ "]! " p => Undeducible Λ Γ p

abbrev Proof := ∅ ⊢ᴹ[Λ] p
notation:45 "⊢ᴹ[" Λ "] " p => Proof Λ p

abbrev Provable := Nonempty (⊢ᴹ[Λ] p)
notation:45 "⊢ᴹ[" Λ "]! " p => Provable Λ p

abbrev Unprovable := IsEmpty (⊢ᴹ[Λ] p)
notation:45 "⊬ᴹ[" Λ "]! " p => Unprovable Λ p

abbrev Theory.Consistent := Deduction.Consistent (@Deduction α Λ) Γ
abbrev Theory.Inconsistent := Deduction.Inconsistent (@Deduction α Λ) Γ

namespace Deduction

variable {Λ : AxiomSet α} {Γ : Theory α} {p q : Formula α}

def length {Γ : Theory α} {p : Formula α} : (Γ ⊢ᴹ[Λ] p) → ℕ
  | modus_ponens d₁ d₂ => (max d₁.length d₂.length) + 1
  | necessitation d₁ => d₁.length + 1
  | _ => 0

protected def cast (d : Γ ⊢ᴹ[Λ] p) (e₁ : Γ = Δ) (e₂ : p = q) : Δ ⊢ᴹ[Λ] q := cast (by simp [e₁,e₂]) d

@[simp] lemma length_cast (d : Γ ⊢ᴹ[Λ] p) (e₁ : Γ = Δ) (e₂ : p = q) : (d.cast e₁ e₂).length = d.length := by
  rcases e₁ with rfl; rcases e₂ with rfl; simp [Deduction.cast]

def castL (d : Γ ⊢ᴹ[Λ] p) (e₁ : Γ = Δ) : Δ ⊢ᴹ[Λ] p := d.cast e₁ rfl

@[simp] lemma length_castL (d : Γ ⊢ᴹ[Λ] p) (e₁ : Γ = Δ) : (d.castL e₁).length = d.length := length_cast d e₁ rfl

def castR (d : Γ ⊢ᴹ[Λ] p) (e₂ : p = q) : Γ ⊢ᴹ[Λ] q := d.cast rfl e₂

@[simp] lemma length_castR (d : Γ ⊢ᴹ[Λ] p) (e₂ : p = q) : (d.castR e₂).length = d.length := length_cast d rfl e₂

def weakening' {Γ Δ p} (hs : Γ ⊆ Δ) : (Γ ⊢ᴹ[Λ] p) → (Δ ⊢ᴹ[Λ] p)
  | axm h => axm (hs h)
  | maxm h => maxm h
  | modus_ponens h₁ h₂ => by
      simp [Finset.union_subset_iff] at hs;
      simpa using (h₁.weakening' hs.1).modus_ponens (h₂.weakening' hs.2);
  | necessitation h => necessitation $ h.weakening' (by simp)
  | verum _ => by apply verum
  | imply₁ _ _ _ => by apply imply₁
  | imply₂ _ _ _ _ => by apply imply₂
  | conj₁ _ _ _ => by apply conj₁
  | conj₂ _ _ _ => by apply conj₂
  | conj₃ _ _ _ => by apply conj₃
  | disj₁ _ _ _ => by apply disj₁
  | disj₂ _ _ _ => by apply disj₂
  | disj₃ _ _ _ _ => by apply disj₃
  | dne _ _ => by apply dne

instance : Hilbert.Classical (Deduction Λ) where
  axm          := axm;
  weakening'   := weakening';
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
  dne          := dne;

instance : HasNecessitation (Deduction Λ) := ⟨necessitation⟩

lemma maxm_subset {Λ Λ'} (dΛ : Γ ⊢ᴹ[Λ] p) : (Λ ⊆ Λ') → (Γ ⊢ᴹ[Λ'] p) := by
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
  | dne => apply dne

def modus_ponens' {Γ p q} : (Γ ⊢ᴹ[Λ] (p ⟶ q)) → (Γ ⊢ᴹ[Λ] p) → (Γ ⊢ᴹ[Λ] q) := Hilbert.modus_ponens'

private def dtrAux (Γ) (p q : Formula α) : (Γ ⊢ᴹ[Λ] q) → ((Γ \ {p}) ⊢ᴹ[Λ] (p ⟶ q))
  | maxm h          => modus_ponens' (imply₁ _ _ _) (maxm h)
  | necessitation h => modus_ponens' (imply₁ _ _ _) (necessitation h)
  | verum _         => modus_ponens' (imply₁ _ _ _) (verum _)
  | imply₁ _ _ _    => modus_ponens' (imply₁ _ _ _) (imply₁ _ _ _)
  | imply₂ _ _ _ _  => modus_ponens' (imply₁ _ _ _) (imply₂ _ _ _ _)
  | conj₁ _ _ _     => modus_ponens' (imply₁ _ _ _) (conj₁ _ _ _)
  | conj₂ _ _ _     => modus_ponens' (imply₁ _ _ _) (conj₂ _ _ _)
  | conj₃ _ _ _     => modus_ponens' (imply₁ _ _ _) (conj₃ _ _ _)
  | disj₁ _ _ _     => modus_ponens' (imply₁ _ _ _) (disj₁ _ _ _)
  | disj₂ _ _ _     => modus_ponens' (imply₁ _ _ _) (disj₂ _ _ _)
  | disj₃ _ _ _ _   => modus_ponens' (imply₁ _ _ _) (disj₃ _ _ _ _)
  | dne _ _         => modus_ponens' (imply₁ _ _ _) (dne _ _)
  | @axm _ _ Γ q ih => by
    by_cases h : p = q
    case pos =>
      simpa [h] using Hilbert.imp_id (Γ \ {p}) p;
    case neg =>
      have d₁ : (Γ \ {p}) ⊢ᴹ[Λ] (q ⟶ p ⟶ q) := imply₁ _ q p
      have d₂ : (Γ \ {p}) ⊢ᴹ[Λ] q := axm (Set.mem_diff_singleton.mpr ⟨ih, Ne.symm h⟩)
      exact d₁.modus_ponens' d₂;
  | @modus_ponens _ _ Γ₁ Γ₂ a b h₁ h₂ =>
      have ih₁ : Γ₁ \ {p} ⊢ᴹ[Λ] p ⟶ a ⟶ b := dtrAux Γ₁ p (a ⟶ b) h₁
      have ih₂ : Γ₂ \ {p} ⊢ᴹ[Λ] p ⟶ a := dtrAux Γ₂ p a h₂
      have d₁ : ((Γ₁ ∪ Γ₂) \ {p}) ⊢ᴹ[Λ] (p ⟶ a) ⟶ p ⟶ b :=
        (imply₂ _ p a b).modus_ponens' ih₁ |>.weakening' (Set.diff_subset_diff (by { exact Set.subset_union_left Γ₁ Γ₂ }) (by simp))
      have d₂ : ((Γ₁ ∪ Γ₂) \ {p}) ⊢ᴹ[Λ] (p ⟶ a) :=
        ih₂.weakening' (Set.diff_subset_diff (Set.subset_union_right Γ₁ Γ₂) (by simp))
      d₁.modus_ponens' d₂

def dtr {Γ p q} (d : (insert p Γ) ⊢ᴹ[Λ] q) : (Γ ⊢ᴹ[Λ] (p ⟶ q)) := by
  exact dtrAux (insert p Γ) p q d |>.weakening' (by simp;);

instance : HasDT (Deduction Λ) := ⟨dtr⟩

def compact {Γ p} : (Γ ⊢ᴹ[Λ] p) → (Δ : { Δ : Context α | ↑Δ ⊆ Γ}) × (Δ ⊢ᴹ[Λ] p)
  | @axm _ _ Γ p h  => ⟨⟨{p}, by simpa⟩, axm (by simp)⟩
  | maxm h          => ⟨⟨∅, by simp⟩, maxm h⟩
  | @modus_ponens _ _ Γ₁ Γ₂ p q h₁ h₂ => by
      have ⟨⟨Δ₁, hs₁⟩, d₁⟩ := h₁.compact;
      have ⟨⟨Δ₂, hs₂⟩, d₂⟩ := h₂.compact;
      simp at hs₁ d₁ hs₂ d₂;
      exact ⟨
        ⟨Δ₁ ∪ Δ₂, by simp [hs₁, hs₂];⟩,
        by simpa using modus_ponens' (d₁.weakening' (by simp)) (d₂.weakening' (by simp));
      ⟩
  | necessitation _ => ⟨⟨∅, (by simp)⟩, by apply necessitation; simpa;⟩
  | verum _         => ⟨⟨∅, by simp⟩, verum _⟩
  | imply₁ _ _ _    => ⟨⟨∅, by simp⟩, imply₁ _ _ _⟩
  | imply₂ _ _ _ _  => ⟨⟨∅, by simp⟩, imply₂ _ _ _ _⟩
  | conj₁ _ _ _     => ⟨⟨∅, by simp⟩, conj₁ _ _ _⟩
  | conj₂ _ _ _     => ⟨⟨∅, by simp⟩, conj₂ _ _ _⟩
  | conj₃ _ _ _     => ⟨⟨∅, by simp⟩, conj₃ _ _ _⟩
  | disj₁ _ _ _     => ⟨⟨∅, by simp⟩, disj₁ _ _ _⟩
  | disj₂ _ _ _     => ⟨⟨∅, by simp⟩, disj₂ _ _ _⟩
  | disj₃ _ _ _ _   => ⟨⟨∅, by simp⟩, disj₃ _ _ _ _⟩
  | dne _ _         => ⟨⟨∅, by simp⟩, dne _ _⟩

instance : Hilbert.Compact (Deduction Λ) := ⟨compact⟩

end Deduction

namespace Deducible

variable {Λ}

lemma axm! {Γ p} (h : p ∈ Γ) : (Γ ⊢ᴹ[Λ]! p) := ⟨Deduction.axm h⟩

lemma maxm! {Γ p} (h : p ∈ Λ) : (Γ ⊢ᴹ[Λ]! p) := ⟨Deduction.maxm h⟩

lemma compact {Γ p} (d : Γ ⊢ᴹ[Λ]! p) : ∃ (Δ : Context α), ↑Δ ⊆ Γ ∧ (↑Δ ⊢ᴹ[Λ]! p) := by
  have ⟨⟨Δ, hΔ⟩, dΔ⟩ := d.some.compact;
  existsi Δ;
  constructor;
  . simpa using hΔ;
  . exact ⟨dΔ⟩

end Deducible

def Proof.length (d : ⊢ᴹ[Λ] p) : ℕ := Deduction.length (by simpa using d)

lemma Provable.dne : (⊢ᴹ[Λ]! ~~p) → (⊢ᴹ[Λ]! p) := by
  intro d;
  have h₁ : ⊢ᴹ[Λ] ~~p ⟶ p := Deduction.dne ∅ p;
  have h₂ := d.some; simp [Proof, Deduction] at h₂;
  simp_all [Provable, Proof, Deduction];
  exact ⟨(Deduction.modus_ponens' h₁ h₂)⟩

lemma Provable.consistent_no_bot : (⊬ᴹ[Λ]! ⊥) → (⊥ ∉ Λ) := by
  intro h; by_contra hC;
  have : ⊢ᴹ[Λ]! ⊥ := ⟨Deduction.maxm hC⟩;
  aesop;

-- TODO: 直接有限モデルを構成する方法（鹿島『コンピュータサイエンスにおける様相論理』2.8参照）で必要になる筈の定義だが，使わないかも知れない．
/-
section

variable [IsCommutative _ (λ (p q : Formula α) => p ⋏ q)]
         [IsCommutative _ (λ (p q : Formula α) => p ⋎ q)]
         [IsAssociative _ (λ (p q : Formula α) => p ⋏ q)]
         [IsAssociative _ (λ (p q : Formula α) => p ⋎ q)]

def Sequent (Γ Δ : (Theory α)) : Formula α := ((Γ.fold (· ⋏ ·) ⊤ id) ⟶ (Δ.fold (· ⋎ ·) ⊥ id))

notation "⟪" Γ "⟹" Δ "⟫" => Sequent Γ Δ

notation "⟪" "⟹" Δ "⟫" => Sequent ∅ Δ

notation "⟪" Γ "⟹" "⟫" => Sequent Γ ∅

def ProofS (Γ Δ : (Theory α)) := ⊢ᴹ[Λ] ⟪Γ ⟹ Δ⟫

variable [Union ((Theory α))] [Inter ((Theory α))]
variable (Γ₁ Γ₂ Δ : (Theory α))

structure Partial where
  union : (Γ₁ ∪ Γ₂) = Δ
  inter : (Γ₁ ∩ Γ₂) = ∅

structure UnprovablePartial extends Partial Γ₁ Γ₂ Δ where
  unprovable := ⊬ᴹ[Λ]! ⟪Γ₁ ⟹ Γ₂⟫

end
-/

variable [DecidableEq α]

open Deduction Hilbert

variable {Λ : AxiomSet α} (hK : 𝐊 ⊆ Λ)

instance Deduction.ofKSubset : Hilbert.K (Deduction Λ) where
  K _ _ _ := Deduction.maxm $ Set.mem_of_subset_of_mem hK (by simp);

namespace Deduction

def boxedNecessitation {Γ p} : (Γ ⊢ᴹ[Λ] p) → (□Γ ⊢ᴹ[Λ] □p)
  | maxm h => .necessitation $ .maxm h
  | verum _  => .necessitation $ .verum _
  | imply₁ _ _ _ => .necessitation $ .imply₁ _ _ _
  | imply₂ _ _ _ _ => .necessitation $ .imply₂ _ _ _ _
  | conj₁ _ _ _ => .necessitation $ .conj₁ _ _ _
  | conj₂ _ _ _ => .necessitation $ .conj₂ _ _ _
  | conj₃ _ _ _ => .necessitation $ .conj₃ _ _ _
  | disj₁ _ _ _ => .necessitation $ .disj₁ _ _ _
  | disj₂ _ _ _ => .necessitation $ .disj₂ _ _ _
  | disj₃ _ _ _ _ => .necessitation $ .disj₃ _ _ _ _
  | dne _ _ => .necessitation $ .dne _ _
  | necessitation h => .necessitation $ .necessitation h
  | axm h => by exact axm (by simp_all)
  | @modus_ponens _ _ Γ₁ Γ₂ a b h₁ h₂ => by
      have d : □Γ₁ ∪ □Γ₂ ⊢ᴹ[Λ] (□(a ⟶ b) ⟶ (□a ⟶ □b)) := .maxm (by apply hK; simp_all [AxiomK.set, AxiomK]);
      have d₁ : (□Γ₁ ∪ □Γ₂) ⊢ᴹ[Λ] □(a ⟶ b) := boxedNecessitation h₁ |>.weakening' (by simp);
      have d₂ : (□Γ₁ ∪ □Γ₂) ⊢ᴹ[Λ] □a := boxedNecessitation h₂ |>.weakening' (by simp);
      simpa [Set.box_union] using d.modus_ponens' d₁ |>.modus_ponens' d₂;

instance instBoxedNecessitation : HasBoxedNecessitation (Deduction Λ) := ⟨by apply boxedNecessitation; simpa;⟩

end Deduction

/-
def Deduction.ofGLSubset (h : 𝐆𝐋 ⊆ Λ) : (Hilbert.GL (Deduction (Λ : AxiomSet α))) where
  K _ _ _ := Deduction.maxm $ Set.mem_of_subset_of_mem h (by simp);
  L _ _ := Deduction.maxm $ Set.mem_of_subset_of_mem h (by simp);

instance : Hilbert.GL (Deduction (𝐆𝐋 : AxiomSet α)) := Deduction.ofGLSubset _ (by rfl)

def Deduction.ofS4Subset (_ : 𝐒𝟒 ⊆ Λ) : (Hilbert.S4 (Deduction (Λ : AxiomSet α))) where
  K _ _ _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by assumption) (by simp);
  T _ _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by assumption) (by simp);
  A4 _ _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by assumption) (by simp);

instance : Hilbert.S4 (Deduction (𝐒𝟒 : AxiomSet α)) := Deduction.ofS4Subset _ (by rfl)

instance : Hilbert.S4 (Deduction (𝐒𝟒.𝟐 : AxiomSet α)) := Deduction.ofS4Subset _ (by simp)

instance : Hilbert.S4Dot2 (Deduction (𝐒𝟒.𝟐 : AxiomSet α)) where
  Dot2 _ _ := by apply Deduction.maxm; simp;

instance : Hilbert.S4 (Deduction (𝐒𝟒.𝟑 : AxiomSet α)) := Deduction.ofS4Subset _ (by simp)

instance : Hilbert.S4Dot3 (Deduction (𝐒𝟒.𝟑 : AxiomSet α)) where
  Dot3 _ p q := by apply Deduction.maxm; apply Set.mem_union_right; existsi p, q; simp;

instance : Hilbert.S4 (Deduction (𝐒𝟒𝐆𝐫𝐳 : AxiomSet α)) := Deduction.ofS4Subset _ (by simp)

instance : Hilbert.S4Grz (Deduction (𝐒𝟒𝐆𝐫𝐳 : AxiomSet α)) where
  Grz _ _ := by apply Deduction.maxm; simp;

def Deduction.ofS5Subset (_ : 𝐒𝟓 ⊆ Λ) : (Hilbert.S5 (Deduction (Λ : AxiomSet α))) where
  K _ _ _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by assumption) (by simp);
  T _ _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by assumption) (by simp);
  A5 _ _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by assumption) (by simp);

instance : Hilbert.S5 (Deduction (𝐒𝟓 : AxiomSet α)) := Deduction.ofS5Subset 𝐒𝟓 (by rfl)
-/

end Modal.Normal

end LO
