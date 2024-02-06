import Logic.Logic.HilbertStyle2
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

abbrev Theory.Consistent := Hilbert.Consistent (@Deduction α Λ) Γ
abbrev Theory.Inconsistent := Hilbert.Inconsistent (@Deduction α Λ) Γ

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

@[deprecated] lemma axm {Γ p} (h : p ∈ Γ) : Γ ⊢ᴹ[Λ]! p := ⟨.axm h⟩

@[deprecated] lemma maxm {Γ p} (h : p ∈ Λ) : Γ ⊢ᴹ[Λ]! p := ⟨.maxm h⟩

@[deprecated] lemma modus_ponens {Γ₁ Γ₂ p q} (d₁ : Γ₁ ⊢ᴹ[Λ]! (p ⟶ q)) (d₂ : Γ₂ ⊢ᴹ[Λ]! p) : (Γ₁ ∪ Γ₂) ⊢ᴹ[Λ]! q := ⟨.modus_ponens d₁.some d₂.some⟩
@[deprecated] lemma modus_ponens' {Γ p q} (d₁ : Γ ⊢ᴹ[Λ]! (p ⟶ q)) (d₂ : Γ ⊢ᴹ[Λ]! p) : Γ ⊢ᴹ[Λ]! q := ⟨Hilbert.modus_ponens' d₁.some d₂.some⟩

@[deprecated] lemma necessitation {Γ p} (d : ∅ ⊢ᴹ[Λ]! p) : Γ ⊢ᴹ[Λ]! □p := ⟨.necessitation d.some⟩

@[deprecated] lemma weakening' {Γ Δ p} (d : Γ ⊢ᴹ[Λ]! p) (hs : Γ ⊆ Δ) : Δ ⊢ᴹ[Λ]! p := ⟨.weakening' hs d.some⟩

@[simp, deprecated] lemma id_insert (Γ p) : ((insert p Γ) ⊢ᴹ[Λ]! p) := ⟨Hilbert.id_insert Γ p⟩

@[simp, deprecated] lemma id_singleton (p) : ({p} ⊢ᴹ[Λ]! p) := ⟨Hilbert.id_singleton p⟩

@[deprecated] lemma verum (Γ) : Γ ⊢ᴹ[Λ]! ⊤ := ⟨.verum Γ⟩

@[deprecated] lemma boxverum (Γ) : Γ ⊢ᴹ[Λ]! □⊤ := ⟨.necessitation (.verum ∅)⟩

@[deprecated] lemma imply₁ (Γ p q) : Γ ⊢ᴹ[Λ]! (p ⟶ q ⟶ p) := ⟨.imply₁ Γ p q⟩
@[deprecated] lemma imply₁' {Γ p q} (d : Γ ⊢ᴹ[Λ]! p) : Γ ⊢ᴹ[Λ]! (q ⟶ p) := ⟨Hilbert.imply₁' d.some⟩

@[deprecated] lemma imply₂ (Γ p q r) : Γ ⊢ᴹ[Λ]! ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r) := ⟨Hilbert.imply₂ Γ p q r⟩
@[deprecated] lemma imply₂' {Γ p q r} (d₁ : Γ ⊢ᴹ[Λ]! (p ⟶ q ⟶ r)) (d₂ : Γ ⊢ᴹ[Λ]! (p ⟶ q)) (d₃ : Γ ⊢ᴹ[Λ]! p) : Γ ⊢ᴹ[Λ]! r := ⟨Hilbert.imply₂' d₁.some d₂.some d₃.some⟩

@[deprecated] lemma conj₁ (Γ p q) : Γ ⊢ᴹ[Λ]! (p ⋏ q) ⟶ p := ⟨Hilbert.conj₁ Γ p q⟩
@[deprecated] lemma conj₁' {Γ p q} (d : Γ ⊢ᴹ[Λ]! (p ⋏ q)) : Γ ⊢ᴹ[Λ]! p := ⟨Hilbert.conj₁' d.some⟩

@[deprecated] lemma conj₂ (Γ p q) : Γ ⊢ᴹ[Λ]! (p ⋏ q) ⟶ q := ⟨.conj₂ Γ p q⟩
@[deprecated] lemma conj₂' {Γ p q} (d : Γ ⊢ᴹ[Λ]! (p ⋏ q)) : Γ ⊢ᴹ[Λ]! q := ⟨Hilbert.conj₂' d.some⟩

@[deprecated] lemma conj₃ (Γ p q) : Γ ⊢ᴹ[Λ]! p ⟶ q ⟶ (p ⋏ q) := ⟨Hilbert.conj₃ Γ p q⟩
@[deprecated] lemma conj₃' {Γ p q} (d₁ : Γ ⊢ᴹ[Λ]! p) (d₂ : Γ ⊢ᴹ[Λ]! q) : Γ ⊢ᴹ[Λ]! (p ⋏ q) := ⟨Hilbert.conj₃' d₁.some d₂.some⟩

@[deprecated] lemma disj₁ (Γ p q) : Γ ⊢ᴹ[Λ]! p ⟶ (p ⋎ q) := ⟨Hilbert.disj₁ Γ p q⟩
@[deprecated] lemma disj₁' {Γ p q} (d : Γ ⊢ᴹ[Λ]! p) : Γ ⊢ᴹ[Λ]! (p ⋎ q) := ⟨Hilbert.disj₁' d.some⟩

@[deprecated] lemma disj₂ (Γ p q) : Γ ⊢ᴹ[Λ]! q ⟶ (p ⋎ q) := ⟨Hilbert.disj₂ Γ p q⟩
@[deprecated] lemma disj₂' {Γ p q} (d : Γ ⊢ᴹ[Λ]! q) : Γ ⊢ᴹ[Λ]! (p ⋎ q) := ⟨Hilbert.disj₂' d.some⟩

@[deprecated] lemma disj₃ (Γ p q r) : Γ ⊢ᴹ[Λ]! (p ⟶ r) ⟶ (q ⟶ r) ⟶ (p ⋎ q ⟶ r) := ⟨.disj₃ Γ p q r⟩
@[deprecated] lemma disj₃' {Γ p q r} (d₁ : Γ ⊢ᴹ[Λ]! (p ⟶ r)) (d₂ : Γ ⊢ᴹ[Λ]! (q ⟶ r)) (d₃ : Γ ⊢ᴹ[Λ]! (p ⋎ q)) : Γ ⊢ᴹ[Λ]! r := ⟨Hilbert.disj₃' d₁.some d₂.some d₃.some⟩

@[deprecated] lemma efq (Γ p) : Γ ⊢ᴹ[Λ]! (⊥ ⟶ p) := ⟨Hilbert.efq Γ p⟩
@[deprecated] lemma efq' {Γ p} (d : Γ ⊢ᴹ[Λ]! ⊥) : Γ ⊢ᴹ[Λ]! p := ⟨Hilbert.efq' d.some⟩

@[deprecated] lemma dni (Γ p) : Γ ⊢ᴹ[Λ]! (p ⟶ ~~p) := ⟨Hilbert.dni Γ p⟩
@[deprecated] lemma dni' {Γ p} (d : Γ ⊢ᴹ[Λ]! p) : Γ ⊢ᴹ[Λ]! ~~p := ⟨Hilbert.dni' d.some⟩

@[deprecated] lemma dne (Γ p) : Γ ⊢ᴹ[Λ]! (~~p ⟶ p) := ⟨Hilbert.dne Γ p⟩
@[deprecated] lemma dne' {Γ p} (d : Γ ⊢ᴹ[Λ]! ~~p) : Γ ⊢ᴹ[Λ]! p := ⟨Hilbert.dne' d.some⟩

@[deprecated] lemma dtl {Γ p q} (d : Γ ⊢ᴹ[Λ]! (p ⟶ q)) : ((insert p Γ) ⊢ᴹ[Λ]! q) := ⟨Hilbert.dtl d.some⟩
@[deprecated] lemma dtr {Γ p q} (d : (insert p Γ) ⊢ᴹ[Λ]! q) : Γ ⊢ᴹ[Λ]! (p ⟶ q) := ⟨Hilbert.dtr d.some⟩

@[deprecated] lemma iff_intro {Γ p q} (d₁ : Γ ⊢ᴹ[Λ]! (p ⟶ q)) (d₂ : Γ ⊢ᴹ[Λ]! (q ⟶ p)) : Γ ⊢ᴹ[Λ]! (p ⟷ q) := ⟨Hilbert.iff_intro d₁.some d₂.some⟩

@[deprecated] lemma equiv_dn (Γ p) : Γ ⊢ᴹ[Λ]! (p ⟷ ~~p) := ⟨Hilbert.equiv_dn Γ p⟩

@[deprecated] lemma iff_symm' {Γ p q} (d : Γ ⊢ᴹ[Λ]! (p ⟷ q)) : Γ ⊢ᴹ[Λ]! (q ⟷ p) := ⟨Hilbert.iff_symm' d.some⟩

@[deprecated] lemma iff_mp' {Γ p q} (d : Γ ⊢ᴹ[Λ]! (p ⟷ q)) : Γ ⊢ᴹ[Λ]! (p ⟶ q) := ⟨Hilbert.iff_mp' d.some⟩

@[deprecated] lemma iff_mpr' {Γ p q} (d : Γ ⊢ᴹ[Λ]! (p ⟷ q)) : Γ ⊢ᴹ[Λ]! (q ⟶ p) := ⟨Hilbert.iff_mpr' d.some⟩

@[deprecated] lemma iff_right' {Γ p q} (dpq : Γ ⊢ᴹ[Λ]! (p ⟷ q)) (dp : Γ ⊢ᴹ[Λ]! p) : Γ ⊢ᴹ[Λ]! q := ⟨Hilbert.iff_right' dpq.some dp.some⟩

@[deprecated] lemma iff_left' {Γ p q} (dpq : Γ ⊢ᴹ[Λ]! (p ⟷ q)) (dq : Γ ⊢ᴹ[Λ]! q) : Γ ⊢ᴹ[Λ]! p := ⟨Hilbert.iff_left' dpq.some dq.some⟩

@[deprecated]
lemma iff_def {Γ p q} : (Γ ⊢ᴹ[Λ]! (p ⟷ q)) ↔ (Γ ⊢ᴹ[Λ]! (p ⟶ q)) ∧ (Γ ⊢ᴹ[Λ]! (q ⟶ p)) := by
  constructor;
  . intro h; exact ⟨conj₁' h, conj₂' h⟩;
  . intro h; exact conj₃' h.1 h.2

@[deprecated]
lemma contra₀' {Γ p q} (d : Γ ⊢ᴹ[Λ]! (p ⟶ q)) : Γ ⊢ᴹ[Λ]! (~q ⟶ ~p) := ⟨Hilbert.contra₀' d.some⟩

@[deprecated]
lemma neg_iff' {Γ p q} (d : Γ ⊢ᴹ[Λ]! (p ⟷ q)) : Γ ⊢ᴹ[Λ]! (~p ⟷ ~q) := ⟨Hilbert.neg_iff' d.some⟩

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

def Deduction.ofKSubset (h : 𝐊 ⊆ Λ) : (Hilbert.K (Deduction (Λ : AxiomSet α))) where
  K _ _ _ := Deduction.maxm $ Set.mem_of_subset_of_mem h (by simp);

instance : Hilbert.K (Deduction (𝐊 : AxiomSet α)) := Deduction.ofKSubset _ (by rfl)

namespace Deduction

variable {Λ : AxiomSet α} (hK : 𝐊 ⊆ Λ)

lemma ctx_necessitation {Γ p} (d : Γ ⊢ᴹ[Λ] p) : (□Γ ⊢ᴹ[Λ] □p) := by
  induction d with
  | axm h => exact axm (by simp [Theory.box]; aesop;)
  | maxm h => exact .necessitation $ maxm h;
  | @modus_ponens Γ₁ Γ₂ p q _ _ ih₁ ih₂ =>
      have d : □Γ₁ ∪ □Γ₂ ⊢ᴹ[Λ] (□(p ⟶ q) ⟶ (□p ⟶ □q)) := .maxm (by simp_all [AxiomK.set, AxiomK]; aesop);
      simpa [Theory.box_union] using d |>.modus_ponens' (ih₁.weakening' (by simp)) |>.modus_ponens' (ih₂.weakening' (by simp));
  | necessitation _ ih =>
      simp at ih;
      exact .necessitation ih
  | verum =>  exact .necessitation $ .verum _
  | imply₁ => exact .necessitation $ .imply₁ _ _ _
  | imply₂ => exact .necessitation $ .imply₂ _ _ _ _
  | conj₁  => exact .necessitation $ .conj₁ _ _ _
  | conj₂  => exact .necessitation $ .conj₂ _ _ _
  | conj₃  => exact .necessitation $ .conj₃ _ _ _
  | disj₁  => exact .necessitation $ .disj₁ _ _ _
  | disj₂  => exact .necessitation $ .disj₂ _ _ _
  | disj₃  => exact .necessitation $ .disj₃ _ _ _ _
  | dne    => exact .necessitation $ .dne _ _

lemma preboxed_ctx_necessitation {Γ p} (h : □⁻¹Γ ⊢ᴹ[Λ]! p) : (Γ ⊢ᴹ[Λ]! □p) := by
  have : □(□⁻¹Γ) ⊢ᴹ[Λ]! □p := ⟨ctx_necessitation hK h.some⟩;
  exact this.weakening' (by simp);

@[deprecated]
lemma box_iff' {Γ p q} (d : ⊢ᴹ[Λ]! (p ⟷ q)) : Γ ⊢ᴹ[Λ]! (□p ⟷ □q) := by
  have := ofKSubset _ hK;
  exact ⟨LO.Hilbert.box_iff' d.some⟩

@[deprecated]
lemma equiv_dianeg_negbox (Γ p) : Γ ⊢ᴹ[Λ]! ((◇~p) ⟷ (~(□p))) := by
  have := ofKSubset _ hK;
  exact ⟨LO.Hilbert.equiv_dianeg_negbox _ _⟩

end Deduction

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

end Modal.Normal

end LO
