import Logic.Logic.HilbertStyle2
import Logic.Modal.Normal.Formula
import Logic.Modal.Normal.Axioms

attribute [simp] Finset.subset_union_right Finset.subset_union_left Finset.subset_insert

namespace LO

namespace Hilbert

open LO.Modal.Normal

variable {F : Type u} [ModalLogicSymbol F] [DecidableEq F] [NegDefinition F] (Bew : Finset F → F → Sort*)

class HasNecessitation where
  necessitation {Γ p} : (Bew ∅ p) → (Bew Γ (□p))

class HasAxiomK where
  K (Γ : Finset F) (p q : F) : Bew Γ $ AxiomK p q

class HasAxiomT where
  T (Γ : Finset F) (p : F) : Bew Γ $ AxiomT p

class HasAxiomD where
  D (Γ : Finset F) (p : F) : Bew Γ $ AxiomD p

class HasAxiomB where
  B (Γ : Finset F) (p q : F) : Bew Γ $ AxiomB p

class HasAxiom4 where
  A4 (Γ : Finset F) (p : F) : Bew Γ $ Axiom4 p

class HasAxiom5 where
  A5 (Γ : Finset F) (p : F) : Bew Γ $ Axiom5 p

class HasAxiomL where
  L (Γ : Finset F) (p : F) : Bew Γ $ AxiomL p

class HasAxiomDot2 where
  Dot2 (Γ : Finset F) (p : F) : Bew Γ $ AxiomDot2 p

class HasAxiomDot3 where
  Dot3 (Γ : Finset F) (p q : F) : Bew Γ $ AxiomDot3 p q

class HasAxiomGrz where
  Grz (Γ : Finset F) (p : F) : Bew Γ $ AxiomGrz p

class HasAxiomM where
  M (Γ : Finset F) (p : F) : Bew Γ $ AxiomM p

class HasAxiomCD where
  CD (Γ : Finset F) (p : F) : Bew Γ $ AxiomCD p

class HasAxiomC4 where
  C4 (Γ : Finset F) (p : F) : Bew Γ $ AxiomC4 p

variable {Bew : Finset F → F → Sort*}
variable [ModalDuality F] [HasDT Bew] [HasNecessitation Bew] [HasAxiomK Bew]

lemma box_iff' [Minimal Bew] {Γ p q} (d : Bew ∅ (p ⟷ q)) : Bew Γ (□p ⟷ □q) := by
  have dp₁ : Bew ∅ (□(p ⟶ q) ⟶ (□p ⟶ □q)) := by simpa using HasAxiomK.K ∅ p q;
  have dp₂ : Bew ∅ (□(p ⟶ q)) := HasNecessitation.necessitation $ Hilbert.iff_mp' d;

  have dq₁ : Bew ∅ (□(q ⟶ p) ⟶ (□q ⟶ □p)) := by simpa using HasAxiomK.K ∅ q p;
  have dq₂ : Bew ∅ (□(q ⟶ p)) := HasNecessitation.necessitation $ Hilbert.iff_mpr' d;

  exact Hilbert.iff_intro
    (Deduction.weakening' (by simp) (modus_ponens' dp₁ dp₂))
    (Deduction.weakening' (by simp) (modus_ponens' dq₁ dq₂))

lemma equiv_dianeg_negbox [Classical Bew] (Γ p) : Bew Γ ((◇~p) ⟷ (~(□p))) := by
  simp only [ModalDuality.dia]
  apply Hilbert.neg_iff';
  apply box_iff';
  apply iff_symm';
  apply equiv_dn;

end Hilbert

namespace Modal.Normal

open Hilbert

section Logics

variable {F : Type u} [ModalLogicSymbol F] [NegDefinition F] [ModalDuality F] [DecidableEq F] (Bew : Finset F → F → Sort*)

class LogicK.Hilbert [ModalDuality F] extends Hilbert.Classical Bew, HasNecessitation Bew, HasAxiomK Bew

class LogicKD.Hilbert extends LogicK.Hilbert Bew, HasAxiomD Bew

class LogicS4.Hilbert extends LogicK.Hilbert Bew, HasAxiomT Bew, HasAxiom4 Bew

class LogicS5.Hilbert extends LogicK.Hilbert Bew, HasAxiomT Bew, HasAxiom5 Bew

class LogicS4Dot2.Hilbert extends LogicS4.Hilbert Bew, HasAxiomDot2 Bew

class LogicS4Dot3.Hilbert extends LogicS4.Hilbert Bew, HasAxiomDot3 Bew

class LogicS4Grz.Hilbert extends LogicS4.Hilbert Bew, HasAxiomGrz Bew

class LogicGL.Hilbert extends LogicK.Hilbert Bew, HasAxiomL Bew

end Logics

variable {α : Type u} [DecidableEq α]

/--
  Hilbert-style deduction system
-/
inductive Deduction (Λ : AxiomSet α) : (Context α) → (Formula α) → Type _ where
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

variable (Λ : AxiomSet α) (Γ : (Context α)) (p : Formula α)

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

namespace Deduction

variable {Λ : AxiomSet α} {Γ : (Context α)} {p q : Formula α}

@[simp]
lemma axm_singleton : {p} ⊢ᴹ[Λ] p := by apply axm (by simp);

def length {Γ : (Context α)} {p : Formula α} : (Γ ⊢ᴹ[Λ] p) → ℕ
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

def modus_ponens' {Γ p q} : (Γ ⊢ᴹ[Λ] (p ⟶ q)) → (Γ ⊢ᴹ[Λ] p) → (Γ ⊢ᴹ[Λ] q) := Hilbert.modus_ponens'

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


def dtl {Γ p q} : (Γ ⊢ᴹ[Λ] (p ⟶ q)) → ((insert p Γ) ⊢ᴹ[Λ] q) := Hilbert.dtl

private noncomputable def dtrAux (Γ p q) (d : Γ ⊢ᴹ[Λ] q) : ((Γ.erase p) ⊢ᴹ[Λ] (p ⟶ q)) := by
  induction d with
  | maxm h => exact modus_ponens' (imply₁ _ _ _) (maxm h);
  | necessitation h => exact modus_ponens' (imply₁ _ _ _) (necessitation h);
  | verum => exact modus_ponens' (imply₁ _ _ _) (verum _);
  | imply₁ => exact modus_ponens' (imply₁ _ _ _) (imply₁ _ _ _);
  | imply₂ => exact modus_ponens' (imply₁ _ _ _) (imply₂ _ _ _ _);
  | conj₁ => exact modus_ponens' (imply₁ _ _ _) (conj₁ _ _ _);
  | conj₂ => exact modus_ponens' (imply₁ _ _ _) (conj₂ _ _ _);
  | conj₃ => exact modus_ponens' (imply₁ _ _ _) (conj₃ _ _ _);
  | disj₁ => exact modus_ponens' (imply₁ _ _ _) (disj₁ _ _ _);
  | disj₂ => exact modus_ponens' (imply₁ _ _ _) (disj₂ _ _ _);
  | disj₃ => exact modus_ponens' (imply₁ _ _ _) (disj₃ _ _ _ _);
  | dne => exact modus_ponens' (imply₁ _ _ _) (dne _ _)
  | @axm Γ q ih =>
    by_cases h : p = q
    case pos =>
      subst h
      exact Hilbert.imp_id (Γ.erase p) p;
    case neg =>
      have d₁ : (Γ.erase p) ⊢ᴹ[Λ] (q ⟶ p ⟶ q) := imply₁ _ q p
      have d₂ : (Γ.erase p) ⊢ᴹ[Λ] q := axm (by
        simp [Finset.mem_erase];
        aesop;
      )
      exact d₁.modus_ponens' d₂;
  | @modus_ponens Γ₁ Γ₂ a b _ _ ih₁ ih₂ =>
      have d₁ : Finset.erase (Γ₁ ∪ Γ₂) p ⊢ᴹ[Λ] (p ⟶ a) ⟶ p ⟶ b := (imply₂ _ p a b).modus_ponens' ih₁ |>.weakening' (by
        apply Finset.erase_subset_erase;
        simp;
      );
      have d₂ : Finset.erase (Γ₁ ∪ Γ₂) p ⊢ᴹ[Λ] (p ⟶ a) := ih₂.weakening' (by
        apply Finset.erase_subset_erase;
        simp;
      );
      exact d₁.modus_ponens' d₂;

noncomputable def dtr {Γ p q} (d : (insert p Γ) ⊢ᴹ[Λ] q) : (Γ ⊢ᴹ[Λ] (p ⟶ q)) := by
  exact dtrAux (insert p Γ) p q d |>.weakening' (by apply Finset.erase_insert_subset);

noncomputable instance : HasDT (Deduction Λ) := ⟨dtr⟩

end Deduction

namespace Deducible

variable {Λ}

lemma axm {Γ p} (h : p ∈ Γ) : Γ ⊢ᴹ[Λ]! p := ⟨.axm h⟩
@[simp] lemma axm_insert {Γ p} : (insert p Γ) ⊢ᴹ[Λ]! p := axm (by simp)
@[simp] lemma axm_singleton : {p} ⊢ᴹ[Λ]! p := ⟨.axm_singleton⟩

lemma maxm {Γ p} (h : p ∈ Λ) : Γ ⊢ᴹ[Λ]! p := ⟨.maxm h⟩

lemma modus_ponens {Γ₁ Γ₂ p q} (d₁ : Γ₁ ⊢ᴹ[Λ]! (p ⟶ q)) (d₂ : Γ₂ ⊢ᴹ[Λ]! p) : (Γ₁ ∪ Γ₂) ⊢ᴹ[Λ]! q := ⟨.modus_ponens d₁.some d₂.some⟩
lemma modus_ponens' {Γ p q} (d₁ : Γ ⊢ᴹ[Λ]! (p ⟶ q)) (d₂ : Γ ⊢ᴹ[Λ]! p) : Γ ⊢ᴹ[Λ]! q := ⟨Hilbert.modus_ponens' d₁.some d₂.some⟩

lemma necessitation {Γ p} (d : ∅ ⊢ᴹ[Λ]! p) : Γ ⊢ᴹ[Λ]! □p := ⟨.necessitation d.some⟩

lemma weakening' {Γ Δ p} (d : Γ ⊢ᴹ[Λ]! p) (hs : Γ ⊆ Δ) : Δ ⊢ᴹ[Λ]! p := ⟨.weakening' hs d.some⟩

lemma verum (Γ) : Γ ⊢ᴹ[Λ]! ⊤ := ⟨.verum Γ⟩

lemma boxverum (Γ) : Γ ⊢ᴹ[Λ]! □⊤ := ⟨.necessitation (.verum ∅)⟩

lemma conj₁ (Γ p q) : Γ ⊢ᴹ[Λ]! (p ⋏ q) ⟶ p := ⟨.conj₁ Γ p q⟩
lemma conj₁' {Γ p q} (d : Γ ⊢ᴹ[Λ]! (p ⋏ q)) : Γ ⊢ᴹ[Λ]! p := ⟨Hilbert.conj₁' d.some⟩

lemma conj₂ (Γ p q) : Γ ⊢ᴹ[Λ]! (p ⋏ q) ⟶ q := ⟨.conj₂ Γ p q⟩
lemma conj₂' {Γ p q} (d : Γ ⊢ᴹ[Λ]! (p ⋏ q)) : Γ ⊢ᴹ[Λ]! q := ⟨Hilbert.conj₂' d.some⟩

lemma conj₃ (Γ p q) : Γ ⊢ᴹ[Λ]! p ⟶ q ⟶ (p ⋏ q) := ⟨.conj₃ Γ p q⟩
lemma conj₃' {Γ p q} (d₁ : Γ ⊢ᴹ[Λ]! p) (d₂ : Γ ⊢ᴹ[Λ]! q) : Γ ⊢ᴹ[Λ]! (p ⋏ q) := ⟨Hilbert.conj₃' d₁.some d₂.some⟩

lemma disj₁ (Γ p q) : Γ ⊢ᴹ[Λ]! p ⟶ (p ⋎ q) := ⟨.disj₁ Γ p q⟩
lemma disj₁' {Γ p q} (d : Γ ⊢ᴹ[Λ]! p) : Γ ⊢ᴹ[Λ]! (p ⋎ q) := ⟨Hilbert.disj₁' d.some⟩

lemma disj₂ (Γ p q) : Γ ⊢ᴹ[Λ]! q ⟶ (p ⋎ q) := ⟨.disj₂ Γ p q⟩
lemma disj₂' {Γ p q} (d : Γ ⊢ᴹ[Λ]! q) : Γ ⊢ᴹ[Λ]! (p ⋎ q) := ⟨Hilbert.disj₂' d.some⟩

lemma disj₃ (Γ p q r) : Γ ⊢ᴹ[Λ]! (p ⟶ r) ⟶ (q ⟶ r) ⟶ (p ⋎ q ⟶ r) := ⟨.disj₃ Γ p q r⟩
lemma disj₃' {Γ p q r} (d₁ : Γ ⊢ᴹ[Λ]! (p ⟶ r)) (d₂ : Γ ⊢ᴹ[Λ]! (q ⟶ r)) (d₃ : Γ ⊢ᴹ[Λ]! (p ⋎ q)) : Γ ⊢ᴹ[Λ]! r := ⟨Hilbert.disj₃' d₁.some d₂.some d₃.some⟩

lemma efq (Γ p) : Γ ⊢ᴹ[Λ]! (⊥ ⟶ p) := ⟨HasEFQ.efq Γ p⟩
lemma efq' {Γ p} (d : Γ ⊢ᴹ[Λ]! ⊥) : Γ ⊢ᴹ[Λ]! p := ⟨Hilbert.efq' d.some⟩

lemma dni (Γ p) : Γ ⊢ᴹ[Λ]! (p ⟶ ~~p) := ⟨Hilbert.dni Γ p⟩
lemma dni' {Γ p} (d : Γ ⊢ᴹ[Λ]! p) : Γ ⊢ᴹ[Λ]! ~~p := ⟨Hilbert.dni' d.some⟩

lemma dne (Γ p) : Γ ⊢ᴹ[Λ]! (~~p ⟶ p) := ⟨.dne Γ p⟩
lemma dne' {Γ p} (d : Γ ⊢ᴹ[Λ]! ~~p) : Γ ⊢ᴹ[Λ]! p := ⟨Hilbert.dne' d.some⟩

lemma dtl {Γ p q} (d : Γ ⊢ᴹ[Λ]! (p ⟶ q)) : ((insert p Γ) ⊢ᴹ[Λ]! q) := ⟨.dtl d.some⟩

lemma dtr {Γ p q} (d : (insert p Γ) ⊢ᴹ[Λ]! q) : Γ ⊢ᴹ[Λ]! (p ⟶ q) := ⟨.dtr d.some⟩

lemma iff_intro {Γ p q} (d₁ : Γ ⊢ᴹ[Λ]! (p ⟶ q)) (d₂ : Γ ⊢ᴹ[Λ]! (q ⟶ p)) : Γ ⊢ᴹ[Λ]! (p ⟷ q) := ⟨Hilbert.iff_intro d₁.some d₂.some⟩

lemma equiv_dn (Γ p) : Γ ⊢ᴹ[Λ]! (p ⟷ ~~p) := ⟨Hilbert.equiv_dn Γ p⟩

lemma iff_symm' {Γ p q} (d : Γ ⊢ᴹ[Λ]! (p ⟷ q)) : Γ ⊢ᴹ[Λ]! (q ⟷ p) := ⟨Hilbert.iff_symm' d.some⟩

lemma iff_mp' {Γ p q} (d : Γ ⊢ᴹ[Λ]! (p ⟷ q)) : Γ ⊢ᴹ[Λ]! (p ⟶ q) := ⟨Hilbert.iff_mp' d.some⟩

lemma iff_mpr' {Γ p q} (d : Γ ⊢ᴹ[Λ]! (p ⟷ q)) : Γ ⊢ᴹ[Λ]! (q ⟶ p) := ⟨Hilbert.iff_mpr' d.some⟩

lemma iff_right' {Γ p q} (dpq : Γ ⊢ᴹ[Λ]! (p ⟷ q)) (dp : Γ ⊢ᴹ[Λ]! p) : Γ ⊢ᴹ[Λ]! q := ⟨Hilbert.iff_right' dpq.some dp.some⟩

lemma iff_left' {Γ p q} (dpq : Γ ⊢ᴹ[Λ]! (p ⟷ q)) (dq : Γ ⊢ᴹ[Λ]! q) : Γ ⊢ᴹ[Λ]! p := ⟨Hilbert.iff_left' dpq.some dq.some⟩

lemma iff_def {Γ p q} : (Γ ⊢ᴹ[Λ]! (p ⟷ q)) ↔ (Γ ⊢ᴹ[Λ]! (p ⟶ q)) ∧ (Γ ⊢ᴹ[Λ]! (q ⟶ p)) := by
  constructor;
  . intro h; exact ⟨conj₁' h, conj₂' h⟩;
  . intro h; exact conj₃' h.1 h.2

lemma contra₀' {Γ p q} (d : Γ ⊢ᴹ[Λ]! (p ⟶ q)) : Γ ⊢ᴹ[Λ]! (~q ⟶ ~p) := ⟨Hilbert.contra₀' d.some⟩

lemma neg_iff' {Γ p q} (d : Γ ⊢ᴹ[Λ]! (p ⟷ q)) : Γ ⊢ᴹ[Λ]! (~p ⟷ ~q) := ⟨Hilbert.neg_iff' d.some⟩

end Deducible

def Proof.length (d : ⊢ᴹ[Λ] p) : ℕ := Deduction.length (by simpa using d)

lemma Provable.dne : (⊢ᴹ[Λ]! ~~p) → (⊢ᴹ[Λ]! p) := by
  intro d;
  have h₁ : ⊢ᴹ[Λ] ~~p ⟶ p := Deduction.dne ∅ p;
  have h₂ := d.some; simp [Proof, Deduction] at h₂;
  simp_all [Provable, Proof, Deduction];
  exact ⟨(Deduction.modus_ponens h₁ h₂)⟩

lemma Provable.consistent_no_bot : (⊬ᴹ[Λ]! ⊥) → (⊥ ∉ Λ) := by
  intro h; by_contra hC;
  have : ⊢ᴹ[Λ]! ⊥ := ⟨Deduction.maxm hC⟩;
  aesop;

-- TODO: 直接有限モデルを構成する方法（鹿島『コンピュータサイエンスにおける様相論理』2.8参照）で必要になる筈の定義だが，使わないかも知れない．
section

variable [IsCommutative _ (λ (p q : Formula α) => p ⋏ q)]
         [IsCommutative _ (λ (p q : Formula α) => p ⋎ q)]
         [IsAssociative _ (λ (p q : Formula α) => p ⋏ q)]
         [IsAssociative _ (λ (p q : Formula α) => p ⋎ q)]

def Sequent (Γ Δ : (Context α)) : Formula α := ((Γ.fold (· ⋏ ·) ⊤ id) ⟶ (Δ.fold (· ⋎ ·) ⊥ id))

notation "⟪" Γ "⟹" Δ "⟫" => Sequent Γ Δ

notation "⟪" "⟹" Δ "⟫" => Sequent ∅ Δ

notation "⟪" Γ "⟹" "⟫" => Sequent Γ ∅

def ProofS (Γ Δ : (Context α)) := ⊢ᴹ[Λ] ⟪Γ ⟹ Δ⟫

variable [Union ((Context α))] [Inter ((Context α))]
variable (Γ₁ Γ₂ Δ : (Context α))

structure Partial where
  union : (Γ₁ ∪ Γ₂) = Δ
  inter : (Γ₁ ∩ Γ₂) = ∅

structure UnprovablePartial extends Partial Γ₁ Γ₂ Δ where
  unprovable := ⊬ᴹ[Λ]! ⟪Γ₁ ⟹ Γ₂⟫

end

variable [DecidableEq α]

open Deduction Hilbert

def LogicK.Hilbert.ofKSubset (h : 𝐊 ⊆ Λ) : (LogicK.Hilbert (Deduction (Λ : AxiomSet α))) where
  K _ _ _ := Deduction.maxm $ Set.mem_of_subset_of_mem h (by simp);

instance : LogicK.Hilbert (Deduction (𝐊 : AxiomSet α)) := LogicK.Hilbert.ofKSubset 𝐊 Set.Subset.rfl

namespace LogicK.Hilbert

variable {Λ : AxiomSet α} (hK : 𝐊 ⊆ Λ)

lemma deduction_by_boxed_context {Γ p} (d : Γ ⊢ᴹ[Λ] p) : (□Γ ⊢ᴹ[Λ] □p) := by
  induction d with
  | axm h => exact axm (by simp [Context.box]; aesop;)
  | maxm h => exact necessitation $ maxm h;
  | @modus_ponens Γ₁ Γ₂ p q _ _ ih₁ ih₂ =>
      have d : □Γ₁ ∪ □Γ₂ ⊢ᴹ[Λ] (□(p ⟶ q) ⟶ (□p ⟶ □q)) := .maxm (by simp_all [AxiomK.set, AxiomK]; aesop);
      simpa [Context.box_union] using d |>.modus_ponens' (ih₁.weakening' (by simp)) |>.modus_ponens' (ih₂.weakening' (by simp));
  | necessitation _ ih => exact necessitation ih
  | verum => exact necessitation $ verum _
  | imply₁ => exact necessitation $ imply₁ _ _ _
  | imply₂ => exact necessitation $ imply₂ _ _ _ _
  | conj₁ => exact necessitation $ conj₁ _ _ _
  | conj₂ => exact necessitation $ conj₂ _ _ _
  | conj₃ => exact necessitation $ conj₃ _ _ _
  | disj₁ => exact necessitation $ disj₁ _ _ _
  | disj₂ => exact necessitation $ disj₂ _ _ _
  | disj₃ => exact necessitation $ disj₃ _ _ _ _
  | dne => exact necessitation $ dne _ _

lemma box_iff' {Γ p q} (d : ⊢ᴹ[Λ]! (p ⟷ q)) : Γ ⊢ᴹ[Λ]! (□p ⟷ □q) := by
  have := ofKSubset _ hK;
  exact ⟨LO.Hilbert.box_iff' d.some⟩

lemma equiv_dianeg_negbox (Γ p) : Γ ⊢ᴹ[Λ]! ((◇~p) ⟷ (~(□p))) := by
  have := ofKSubset _ hK;
  exact ⟨LO.Hilbert.equiv_dianeg_negbox _ _⟩

end LogicK.Hilbert

def LogicGL.Hilbert.ofGLSubset (h : 𝐆𝐋 ⊆ Λ) : (LogicGL.Hilbert (Deduction (Λ : AxiomSet α))) where
  K _ _ _ := Deduction.maxm $ Set.mem_of_subset_of_mem h (by simp);
  L _ _ := Deduction.maxm $ Set.mem_of_subset_of_mem h (by simp);

instance : LogicGL.Hilbert (Deduction (𝐆𝐋 : AxiomSet α)) := LogicGL.Hilbert.ofGLSubset _ Set.Subset.rfl

def LogicS4.Hilbert.ofS4Subset (_ : 𝐒𝟒 ⊆ Λ) : (LogicS4.Hilbert (Deduction (Λ : AxiomSet α))) where
  K _ _ _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by assumption) (by simp);
  T _ _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by assumption) (by simp);
  A4 _ _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by assumption) (by simp);

instance : LogicS4.Hilbert (Deduction (𝐒𝟒 : AxiomSet α)) := LogicS4.Hilbert.ofS4Subset 𝐒𝟒 Set.Subset.rfl


instance : LogicS4.Hilbert (Deduction (𝐒𝟒.𝟐 : AxiomSet α)) := LogicS4.Hilbert.ofS4Subset _ (by simp)

instance : LogicS4Dot2.Hilbert (Deduction (𝐒𝟒.𝟐 : AxiomSet α)) where
  Dot2 _ _ := by apply Deduction.maxm; simp;


instance : LogicS4.Hilbert (Deduction (𝐒𝟒.𝟑 : AxiomSet α)) := LogicS4.Hilbert.ofS4Subset _ (by simp)

instance : LogicS4Dot3.Hilbert (Deduction (𝐒𝟒.𝟑 : AxiomSet α)) where
  Dot3 _ p q := by apply Deduction.maxm; apply Set.mem_union_right; existsi p, q; simp;


instance : LogicS4.Hilbert (Deduction (𝐒𝟒𝐆𝐫𝐳 : AxiomSet α)) := LogicS4.Hilbert.ofS4Subset _ (by simp)

instance : LogicS4Grz.Hilbert (Deduction (𝐒𝟒𝐆𝐫𝐳 : AxiomSet α)) where
  Grz _ _ := by apply Deduction.maxm; simp;


def LogicS5.Hilbert.ofS5Subset (_ : 𝐒𝟓 ⊆ Λ) : (LogicS5.Hilbert (Deduction (Λ : AxiomSet α))) where
  K _ _ _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by assumption) (by simp);
  T _ _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by assumption) (by simp);
  A5 _ _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by assumption) (by simp);

instance : LogicS5.Hilbert (Deduction (𝐒𝟓 : AxiomSet α)) := LogicS5.Hilbert.ofS5Subset 𝐒𝟓 Set.Subset.rfl


@[simp] def TheoryDeducible (Λ) (Γ : Theory α) (p) := ∃ (Δ : Context α), (↑Δ ⊆ Γ) ∧ (Δ ⊢ᴹ[Λ]! p)

-- TODO: 不便なのでなんとかして`Finset`の`Γ`を与えた時勝手に`↑Γ`しないように出来ないだろうかと思う．
notation:40 Γ " ⊢ᴹ[" Λ "]! " p => TheoryDeducible Λ Γ p

@[simp] abbrev TheoryUndeducible (Λ) (Γ : Theory α) (p) := ¬(Γ ⊢ᴹ[Λ]! p)

notation:40 Γ " ⊬ᴹ[" Λ "]! " p => TheoryUndeducible Λ Γ p

namespace TheoryDeducible

variable {Λ : AxiomSet α}

lemma axm {Γ : Theory α} {p} : (p ∈ Γ) → (Γ ⊢ᴹ[Λ]! p) := by
  intro hp;
  existsi {p}, (by aesop);
  exact ⟨(Deduction.axm (by simp))⟩;

lemma maxm {Γ : Theory α} {p} : (p ∈ Λ) → (Γ ⊢ᴹ[Λ]! p) := by
  intro hp;
  existsi ∅, (by aesop);
  exact ⟨(Deduction.maxm hp)⟩;

lemma modus_ponens' {Γ : Theory α} {p q : Formula α} : (Γ ⊢ᴹ[Λ]! (p ⟶ q)) → (Γ ⊢ᴹ[Λ]! p) → (Γ ⊢ᴹ[Λ]! q) := by
  intro h₁ h₂;
  simp [TheoryDeducible] at h₁ h₂;
  have ⟨Δ₁, ⟨hΔ₁₁, ⟨hΔ₁₂⟩⟩⟩ := h₁;
  have ⟨Δ₂, ⟨hΔ₂₁, ⟨hΔ₂₂⟩⟩⟩ := h₂;

  have hpq : (Δ₁ ∪ Δ₂) ⊢ᴹ[Λ] (p ⟶ q) := hΔ₁₂.weakening' (by simp);
  have hp : (Δ₁ ∪ Δ₂) ⊢ᴹ[Λ] p := hΔ₂₂.weakening' (by simp);

  existsi (Δ₁ ∪ Δ₂), (by aesop);
  exact ⟨(hpq.modus_ponens' hp)⟩

lemma monotone : Monotone (λ (Γ : Theory α) => Γ ⊢ᴹ[Λ]! p) := by
  rintro _ _ h ⟨Δ, hΔ₁, ⟨hΔ₂⟩⟩;
  existsi Δ;
  constructor;
  . apply Set.Subset.trans hΔ₁ h;
  . exact ⟨hΔ₂⟩;

lemma verum (Γ : Theory α) : (Γ ⊢ᴹ[Λ]! ⊤) := by
  existsi ∅, by simp;
  apply Deducible.verum ∅;

lemma boxverum (Γ : Theory α) : (Γ ⊢ᴹ[Λ]! □⊤) := by
  existsi ∅, by simp;
  apply Deducible.boxverum;

lemma equiv_dn (Γ : Theory α) (p : Formula α) : (Γ ⊢ᴹ[Λ]! (p ⟷ ~~p)) := by
  existsi ∅, by simp;
  apply Deducible.equiv_dn ∅ p;

lemma conj₁ (Γ : Theory α) (p q : Formula α) : (Γ ⊢ᴹ[Λ]! (p ⋏ q) ⟶ p) := by
  simp [TheoryDeducible];
  existsi ∅, by simp;
  apply Deducible.conj₁ ∅ p q;

lemma conj₁' {Γ : Theory α} {p q : Formula α } (d : Γ ⊢ᴹ[Λ]! (p ⋏ q)) : Γ ⊢ᴹ[Λ]! p := (conj₁ _ _ _).modus_ponens' d

lemma conj₂ (Γ : Theory α) (p q : Formula α) : (Γ ⊢ᴹ[Λ]! (p ⋏ q) ⟶ q) := by
  simp [TheoryDeducible];
  existsi ∅, by simp;
  apply Deducible.conj₂ ∅ p q;

lemma conj₂' {Γ : Theory α} {p q : Formula α } (d : Γ ⊢ᴹ[Λ]! (p ⋏ q)) : Γ ⊢ᴹ[Λ]! q := (conj₂ _ _ _).modus_ponens' d

lemma conj₃ (Γ : Theory α) (p q : Formula α) : (Γ ⊢ᴹ[Λ]! p ⟶ q ⟶ (p ⋏ q)) := by
  simp [TheoryDeducible];
  existsi ∅, by simp;
  apply Deducible.conj₃ ∅ p q;

lemma conj₃' {Γ : Theory α} {p q : Formula α } (d₁ : Γ ⊢ᴹ[Λ]! p) (d₂ : Γ ⊢ᴹ[Λ]! q) : Γ ⊢ᴹ[Λ]! (p ⋏ q) :=
  (conj₃ _ _ _)
    |>.modus_ponens' d₁
    |>.modus_ponens' d₂

lemma disj₁ (Γ : Theory α) (p q : Formula α) : (Γ ⊢ᴹ[Λ]! p ⟶ (p ⋎ q)) := by
  simp [TheoryDeducible];
  existsi ∅, by simp;
  apply Deducible.disj₁ ∅ p q;

lemma disj₁' {Γ : Theory α} {p q : Formula α } (d : Γ ⊢ᴹ[Λ]! p) : Γ ⊢ᴹ[Λ]! (p ⋎ q) := (disj₁ _ _ _).modus_ponens' d

lemma disj₂ (Γ : Theory α) (p q : Formula α) : (Γ ⊢ᴹ[Λ]! q ⟶ (p ⋎ q)) := by
  simp [TheoryDeducible];
  existsi ∅, by simp;
  apply Deducible.disj₂ ∅ p q;

lemma disj₂' {Γ : Theory α} {p q : Formula α } (d : Γ ⊢ᴹ[Λ]! q) : Γ ⊢ᴹ[Λ]! (p ⋎ q) := (disj₂ _ _ _).modus_ponens' d

lemma disj₃ (Γ : Theory α) (p q r : Formula α) : (Γ ⊢ᴹ[Λ]! (p ⟶ r) ⟶ (q ⟶ r) ⟶ ((p ⋎ q) ⟶ r)) := by
  simp [TheoryDeducible];
  existsi ∅, by simp;
  apply Deducible.disj₃ ∅ p q r;

lemma disj₃' {Γ : Theory α} {p q r : Formula α } (d₁ : Γ ⊢ᴹ[Λ]! (p ⟶ r)) (d₂ : Γ ⊢ᴹ[Λ]! (q ⟶ r)) (d₃ : Γ ⊢ᴹ[Λ]! (p ⋎ q)) : Γ ⊢ᴹ[Λ]! r :=
  (disj₃ _ _ _ _)
    |>.modus_ponens' d₁
    |>.modus_ponens' d₂
    |>.modus_ponens' d₃

lemma efq (Γ : Theory α) (p : Formula α) : (Γ ⊢ᴹ[Λ]! (⊥ ⟶ p)) := by
  simp [TheoryDeducible];
  existsi ∅, by simp;
  apply Deducible.efq ∅ p;

lemma efq' {Γ : Theory α} {p : Formula α } (d : Γ ⊢ᴹ[Λ]! ⊥) : Γ ⊢ᴹ[Λ]! p := (efq _ _).modus_ponens' d

lemma dni (Γ : Theory α) (p : Formula α) : (Γ ⊢ᴹ[Λ]! (p ⟶ ~~p)) := by
  simp [TheoryDeducible];
  existsi ∅, by simp;
  apply Deducible.dni ∅ p;

lemma dni' {Γ : Theory α} {p : Formula α } (d : Γ ⊢ᴹ[Λ]! p) : Γ ⊢ᴹ[Λ]! ~~p := (dni _ _).modus_ponens' d

end TheoryDeducible

end Modal.Normal

end LO
