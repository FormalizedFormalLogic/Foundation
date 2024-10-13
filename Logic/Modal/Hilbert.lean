import Logic.Modal.Formula
import Logic.Modal.System
import Logic.Logic.HilbertStyle.Lukasiewicz

namespace LO.Modal

variable {α : Type*} [DecidableEq α]

/-- instance of inference rule -/
structure InferenceRule (α : Type*) where
  antecedents : List (Formula α)
  /--
  Empty antecedent rule can be simply regarded as axiom rule.
  However, union of all these rules including to `Hilbert.rules` would be too complex for implementation and induction,
  so more than one antecedent is required.
  -/
  antecedents_nonempty : antecedents ≠ [] := by simp
  consequence : Formula α

abbrev InferenceRules (α : Type*) := Set (InferenceRule α)

abbrev Necessitation {α} : InferenceRules α := { { antecedents := [p], consequence := □p} | (p) }
notation "⟮Nec⟯" => Necessitation

abbrev LoebRule {α} : InferenceRules α := { { antecedents := [□p ➝ p], consequence := p} | (p) }
notation "⟮Loeb⟯" => LoebRule

abbrev HenkinRule {α} : InferenceRules α := { { antecedents := [□p ⭤ p], consequence := p }| (p) }
notation "⟮Henkin⟯" => HenkinRule

structure Hilbert (α : Type*) where
  axioms : Theory α
  rules : InferenceRules α

notation "Ax(" Λ ")" => Hilbert.axioms Λ
notation "Rl(" Λ ")" => Hilbert.rules Λ

inductive Deduction (Λ : Hilbert α) : (Formula α) → Type _
  | maxm {p}     : p ∈ Ax(Λ) → Deduction Λ p
  | rule {rl}    : rl ∈ Rl(Λ) → (∀ {p}, p ∈ rl.antecedents → Deduction Λ p) → Deduction Λ rl.consequence
  | mdp {p q}    : Deduction Λ (p ➝ q) → Deduction Λ p → Deduction Λ q
  | imply₁ p q   : Deduction Λ $ Axioms.Imply₁ p q
  | imply₂ p q r : Deduction Λ $ Axioms.Imply₂ p q r
  | ec p q       : Deduction Λ $ Axioms.ElimContra p q

namespace Deduction

variable {Λ Λ₁ Λ₂ : Hilbert α}

instance : System (Formula α) (Hilbert α) := ⟨Deduction⟩

instance : System.Lukasiewicz Λ where
  mdp := mdp
  imply₁ := imply₁
  imply₂ := imply₂
  elim_contra := ec

instance : System.Classical Λ where

instance : System.HasDiaDuality Λ := inferInstance

lemma maxm! {p} (h : p ∈ Λ.axioms) : Λ ⊢! p := ⟨maxm h⟩

end Deduction


namespace Hilbert

open Deduction

class HasNecessitation (Λ : Hilbert α) where
  has_necessitation : ⟮Nec⟯ ⊆ Rl(Λ) := by aesop

instance [HasNecessitation Λ] : System.Necessitation Λ where
  nec := @λ p d => rule (show { antecedents := [p], consequence := □p } ∈ Rl(Λ) by apply HasNecessitation.has_necessitation; simp_all) (by aesop);


class HasLoebRule (Λ : Hilbert α) where
  has_loeb : ⟮Loeb⟯ ⊆ Rl(Λ) := by aesop

instance [HasLoebRule Λ] : System.LoebRule Λ where
  loeb := @λ p d => rule (show { antecedents := [□p ➝ p], consequence := p } ∈ Rl(Λ) by apply HasLoebRule.has_loeb; simp_all) (by aesop);


class HasHenkinRule (Λ : Hilbert α) where
  has_henkin : ⟮Henkin⟯ ⊆ Rl(Λ) := by aesop

instance [HasHenkinRule Λ] : System.HenkinRule Λ where
  henkin := @λ p d => rule (show { antecedents := [□p ⭤ p], consequence := p } ∈ Rl(Λ) by apply HasHenkinRule.has_henkin; simp_all) (by aesop);


class HasNecOnly (Λ : Hilbert α) where
  has_necessitation_only : Rl(Λ) = ⟮Nec⟯ := by rfl

instance [h : HasNecOnly Λ] : Λ.HasNecessitation where
  has_necessitation := by rw [h.has_necessitation_only]

class HasAxiomK (Λ : Hilbert α) where
  has_axiomK : 𝗞 ⊆ Ax(Λ) := by aesop

instance [HasAxiomK Λ] : System.HasAxiomK Λ where
  K _ _ := maxm (by apply HasAxiomK.has_axiomK; simp_all)

class IsNormal (Λ : Hilbert α) extends Λ.HasNecOnly, Λ.HasAxiomK where

end Hilbert


namespace Deduction

open Hilbert

variable {Λ : Hilbert α}

noncomputable def inducition!
  {motive  : (p : Formula α) → Λ ⊢! p → Sort*}
  (hRules  : (r : InferenceRule α) → (hr : r ∈ Rl(Λ)) →
             (hant : ∀ {p}, p ∈ r.antecedents → Λ ⊢! p) →
             (ih : ∀ {p}, (hp : p ∈ r.antecedents) →
             motive p (hant hp)) → motive r.consequence ⟨rule hr (λ hp => (hant hp).some)⟩)
  (hMaxm     : ∀ {p}, (h : p ∈ Ax(Λ)) → motive p ⟨maxm h⟩)
  (hMdp      : ∀ {p q}, {hpq : Λ ⊢! p ➝ q} → {hp : Λ ⊢! p} → motive (p ➝ q) hpq → motive p hp → motive q ⟨mdp hpq.some hp.some⟩)
  (hImply₁     : ∀ {p q}, motive (p ➝ q ➝ p) $ ⟨imply₁ p q⟩)
  (hImply₂     : ∀ {p q r}, motive ((p ➝ q ➝ r) ➝ (p ➝ q) ➝ p ➝ r) $ ⟨imply₂ p q r⟩)
  (hElimContra : ∀ {p q}, motive (Axioms.ElimContra p q) $ ⟨ec p q⟩)
  : ∀ {p}, (d : Λ ⊢! p) → motive p d := by
  intro p d;
  induction d.some with
  | maxm h => exact hMaxm h
  | mdp hpq hp ihpq ihp => exact hMdp (ihpq ⟨hpq⟩) (ihp ⟨hp⟩)
  | rule hr h ih => apply hRules _ hr; intro p hp; exact ih hp ⟨h hp⟩;
  | imply₁ => exact hImply₁
  | imply₂ => exact hImply₂
  | ec => exact hElimContra

/-- Useful induction for normal modal logic. -/
noncomputable def inducition_with_necOnly! [Λ.HasNecOnly]
  {motive  : (p : Formula α) → Λ ⊢! p → Prop}
  (hMaxm   : ∀ {p}, (h : p ∈ Ax(Λ)) → motive p ⟨maxm h⟩)
  (hMdp    : ∀ {p q}, {hpq : Λ ⊢! p ➝ q} → {hp : Λ ⊢! p} → motive (p ➝ q) hpq → motive p hp → motive q (hpq ⨀ hp))
  (hNec    : ∀ {p}, {hp : Λ ⊢! p} → (ihp : motive p hp) → motive (□p) (System.nec! hp))
  (hImply₁   : ∀ {p q}, motive (p ➝ q ➝ p) $ ⟨imply₁ p q⟩)
  (hImply₂   : ∀ {p q r}, motive ((p ➝ q ➝ r) ➝ (p ➝ q) ➝ p ➝ r) $ ⟨imply₂ p q r⟩)
  (hElimContra : ∀ {p q}, motive (Axioms.ElimContra p q) $ ⟨ec p q⟩)
  : ∀ {p}, (d : Λ ⊢! p) → motive p d := by
  intro p d;
  induction d using Deduction.inducition! with
  | hMaxm h => exact hMaxm h
  | hMdp ihpq ihp => exact hMdp (ihpq) (ihp);
  | hRules rl hrl hant ih =>
    rw [HasNecOnly.has_necessitation_only] at hrl;
    obtain ⟨p, rfl⟩ := hrl;
    exact @hNec p (hant (by simp)) $ ih (by simp);
  | hImply₁ => exact hImply₁
  | hImply₂ => exact hImply₂
  | hElimContra => exact hElimContra

open System in
macro_rules | `(tactic| trivial) => `(tactic|
    first
    | apply verum!
    | apply imply₁!
    | apply imply₂!
    | apply elim_contra!
    | apply elim_contra_neg!
  )
macro_rules | `(tactic| trivial) => `(tactic | apply dne!)

end Deduction


abbrev Hilbert.theorems (Λ : Hilbert α) := System.theory Λ


protected abbrev K : Hilbert α := ⟨𝗞, ⟮Nec⟯⟩
notation "𝐊" => Modal.K
instance : 𝐊.IsNormal (α := α) where

abbrev ExtK (Ax : Theory α) : Hilbert α := ⟨𝗞 ∪ Ax, ⟮Nec⟯⟩
instance : Hilbert.IsNormal (α := α) (ExtK Ax) where
prefix:max "𝜿" => ExtK

lemma K_is_extK_of_empty : (𝐊 : Hilbert α) = 𝜿∅ := by aesop;

lemma K_is_extK_of_AxiomK : (𝐊 : Hilbert α) = 𝜿𝗞 := by aesop;

namespace Normal

open System

variable {Ax : Theory α}

lemma def_ax : Ax(𝜿Ax) = (𝗞 ∪ Ax) := by simp;

lemma maxm! (h : p ∈ Ax) : 𝜿Ax ⊢! p := ⟨Deduction.maxm (by simp [def_ax]; right; assumption)⟩

end Normal


-- tools of Modal Companion
section

abbrev ExtS4 (Ax : Theory α) : Hilbert α := 𝜿(𝗧 ∪ 𝟰 ∪ Ax)
prefix:max "𝝈" => ExtS4
instance : System.S4 (𝝈Ax) where
  T _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)
  Four _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)

@[simp] lemma ExtS4.def_ax : Ax(𝝈Ax) = (𝗞 ∪ 𝗧 ∪ 𝟰 ∪ Ax) := by aesop;

end


protected abbrev KT : Hilbert α := 𝜿(𝗧)
notation "𝐊𝐓" => Modal.KT

protected abbrev KB : Hilbert α := 𝜿(𝗕)
notation "𝐊𝐁" => Modal.KB

protected abbrev KD : Hilbert α := 𝜿(𝗗)
notation "𝐊𝐃" => Modal.KD
instance : System.KD (𝐊𝐃 : Hilbert α) where
  D _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)

protected abbrev KP : Hilbert α := 𝜿(𝗣)
notation "𝐊𝐏" => Modal.KP
instance : System.HasAxiomP (𝐊𝐏 : Hilbert α) where
  P := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)

protected abbrev KTB : Hilbert α := 𝜿(𝗧 ∪ 𝗕)
notation "𝐊𝐓𝐁" => Modal.KTB

protected abbrev K4 : Hilbert α := 𝜿(𝟰)
notation "𝐊𝟒" => Modal.K4
instance : System.K4 (𝐊𝟒 : Hilbert α) where
  Four _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)

protected abbrev K5 : Hilbert α := 𝜿(𝟱)
notation "𝐊𝟓" => Modal.K5

protected abbrev S4 : Hilbert α := 𝝈(∅)
notation "𝐒𝟒" => Modal.S4
instance : System.S4 (𝐒𝟒 : Hilbert α) where
  T _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)
  Four _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)

protected abbrev S4Dot2 : Hilbert α := 𝝈(.𝟮)
notation "𝐒𝟒.𝟐" => Modal.S4Dot2

protected abbrev S4Dot3 : Hilbert α := 𝝈(.𝟯)
notation "𝐒𝟒.𝟑" => Modal.S4Dot3

protected abbrev S4Grz : Hilbert α := 𝝈(𝗚𝗿𝘇) -- S4 + 𝗚𝗿𝘇
notation "𝐒𝟒𝐆𝐫𝐳" => Modal.S4Grz

protected abbrev KT4B : Hilbert α := 𝝈(𝗕)
notation "𝐊𝐓𝟒𝐁" => Modal.KT4B

protected abbrev S5 : Hilbert α := 𝜿(𝗧 ∪ 𝟱)
notation "𝐒𝟓" => Modal.S5
instance : System.S5 (𝐒𝟓 : Hilbert α) where
  T _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)
  Five _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)

protected abbrev S5Grz : Hilbert α := 𝜿(𝗧 ∪ 𝟱 ∪ 𝗚𝗿𝘇) -- 𝐒𝟓 + 𝗚𝗿𝘇
notation "𝐒𝟓𝐆𝐫𝐳" => Modal.S5Grz
instance : System.S5 (𝐒𝟓𝐆𝐫𝐳 : Hilbert α) where
  T _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)
  Five _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)
instance : System.Grz (𝐒𝟓𝐆𝐫𝐳 : Hilbert α) where
  Grz _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)

protected abbrev Triv : Hilbert α := 𝜿(𝗧 ∪ 𝗧𝗰)
notation "𝐓𝐫𝐢𝐯" => Modal.Triv
instance : System.Triv (𝐓𝐫𝐢𝐯 : Hilbert α) where
  T _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)
  Tc _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)

protected abbrev Ver : Hilbert α := 𝜿(𝗩𝗲𝗿)
notation "𝐕𝐞𝐫" => Modal.Ver
instance : System.Ver (𝐕𝐞𝐫 : Hilbert α) where
  Ver _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)

protected abbrev GL : Hilbert α := 𝜿(𝗟)
notation "𝐆𝐋" => Modal.GL
instance : System.GL (𝐆𝐋 : Hilbert α) where
  L _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)

protected abbrev Grz : Hilbert α := 𝜿(𝗚𝗿𝘇)
notation "𝐆𝐫𝐳" => Modal.Grz
instance : System.Grz (𝐆𝐫𝐳 : Hilbert α) where
  Grz _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)

protected abbrev K4H : Hilbert α := 𝜿(𝟰 ∪ 𝗛)
notation "𝐊𝟒𝐇" => Modal.K4H
instance : System.K4H (𝐊𝟒𝐇 : Hilbert α) where
  Four _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)
  H _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)

-- Non-normal modal logic

protected abbrev K4Loeb : Hilbert α := ⟨𝗞 ∪ 𝟰, ⟮Nec⟯ ∪ ⟮Loeb⟯⟩
notation "𝐊𝟒(𝐋)" => Modal.K4Loeb
instance : 𝐊𝟒(𝐋).HasAxiomK (α := α) where
instance : 𝐊𝟒(𝐋).HasNecessitation (α := α) where
instance : 𝐊𝟒(𝐋).HasLoebRule (α := α) where
instance : System.K4Loeb (𝐊𝟒(𝐋) : Hilbert α) where
  Four _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)

protected abbrev K4Henkin : Hilbert α := ⟨𝗞 ∪ 𝟰, ⟮Nec⟯ ∪ ⟮Henkin⟯⟩
notation "𝐊𝟒(𝐇)" => Modal.K4Henkin
instance : 𝐊𝟒(𝐇).HasAxiomK (α := α)  where
instance : 𝐊𝟒(𝐇).HasNecessitation (α := α) where
instance : 𝐊𝟒(𝐇).HasHenkinRule (α := α) where
instance : System.K4Henkin (𝐊𝟒(𝐇) : Hilbert α) where
  Four _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)

/--
  Solovey's Provability Logic of True Arithmetic.
  Remark necessitation is *not* permitted.
-/
protected abbrev GLS : Hilbert α := ⟨𝐆𝐋.theorems ∪ 𝗧, ∅⟩
notation "𝐆𝐋𝐒" => Modal.GLS
instance : System.HasAxiomK (𝐆𝐋𝐒 : Hilbert α) where
  K _ _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) $ by simp [Hilbert.theorems, System.theory, System.axiomK!];
instance : System.HasAxiomL (𝐆𝐋𝐒 : Hilbert α) where
  L _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) $ by simp [Hilbert.theorems, System.theory, System.axiomK!];
instance : System.HasAxiomT (𝐆𝐋𝐒 : Hilbert α) where
  T _ := Deduction.maxm $ Set.mem_of_subset_of_mem (by rfl) (by simp)

/-- Logic of Pure Necessitation -/
protected abbrev N : Hilbert α := ⟨∅, ⟮Nec⟯⟩
notation "𝐍" => Modal.N
instance : 𝐍.HasNecOnly (α := α) where


section

open System
open Formula (atom)

lemma normal_weakerThan_of_maxm {Λ₁ Λ₂ : Hilbert α} [Λ₁.IsNormal] [Λ₂.IsNormal]
  (hMaxm : ∀ {p : Formula α}, p ∈ Ax(Λ₁) → Λ₂ ⊢! p)
  : Λ₁ ≤ₛ Λ₂ := by
  apply System.weakerThan_iff.mpr;
  intro p h;
  induction h using Deduction.inducition_with_necOnly! with
  | hMaxm hp => exact hMaxm hp;
  | hMdp ihpq ihp => exact ihpq ⨀ ihp;
  | hNec ihp => exact nec! ihp;
  | _ => trivial;

lemma normal_weakerThan_of_subset {Λ₁ Λ₂ : Hilbert α} [Λ₁.IsNormal] [Λ₂.IsNormal]
  (hSubset : Ax(Λ₁) ⊆ Ax(Λ₂) := by intro; aesop;)
  : Λ₁ ≤ₛ Λ₂ := by
  apply normal_weakerThan_of_maxm;
  intro p hp;
  exact ⟨Deduction.maxm $ hSubset hp⟩;

lemma K_weakerThan_KD : (𝐊 : Hilbert α) ≤ₛ 𝐊𝐃 := normal_weakerThan_of_subset

lemma K_weakerThan_KB : (𝐊 : Hilbert α) ≤ₛ 𝐊𝐁 := normal_weakerThan_of_subset

lemma K_weakerThan_KT : (𝐊 : Hilbert α) ≤ₛ 𝐊𝐓 := normal_weakerThan_of_subset

lemma K_weakerThan_K4 : (𝐊 : Hilbert α) ≤ₛ 𝐊𝟒 := normal_weakerThan_of_subset

lemma K_weakerThan_K5 : (𝐊 : Hilbert α) ≤ₛ 𝐊𝟓 := normal_weakerThan_of_subset

lemma KT_weakerThan_S4 : (𝐊𝐓 : Hilbert α) ≤ₛ 𝐒𝟒 := normal_weakerThan_of_subset

lemma K4_weakerThan_S4 : (𝐊𝟒 : Hilbert α) ≤ₛ 𝐒𝟒 := normal_weakerThan_of_subset

lemma S4_weakerThan_S4Dot2 : (𝐒𝟒 : Hilbert α) ≤ₛ 𝐒𝟒.𝟐 := normal_weakerThan_of_subset

lemma S4_weakerThan_S4Dot3 : (𝐒𝟒 : Hilbert α) ≤ₛ 𝐒𝟒.𝟑 := normal_weakerThan_of_subset

lemma S4_weakerThan_S4Grz : (𝐒𝟒 : Hilbert α) ≤ₛ 𝐒𝟒𝐆𝐫𝐳 := normal_weakerThan_of_subset

lemma K_weakerThan_GL : (𝐊 : Hilbert α) ≤ₛ 𝐆𝐋 := normal_weakerThan_of_subset

lemma K4_weakerThan_Triv : (𝐊𝟒 : Hilbert α) ≤ₛ 𝐓𝐫𝐢𝐯 := by
  apply normal_weakerThan_of_maxm;
  intro p hp;
  rcases hp with (hK | hFour)
  . obtain ⟨_, _, rfl⟩ := hK; exact axiomK!;
  . obtain ⟨_, _, rfl⟩ := hFour; exact axiomFour!;

lemma K4_weakerThan_GL : (𝐊𝟒 : Hilbert α) ≤ₛ 𝐆𝐋 := by
  apply normal_weakerThan_of_maxm;
  intro p hp;
  rcases hp with (hK | hFour)
  . obtain ⟨_, _, rfl⟩ := hK; exact axiomK!;
  . obtain ⟨_, _, rfl⟩ := hFour; exact axiomFour!;

lemma KT_weakerThan_Grz : (𝐊𝐓 : Hilbert α) ≤ₛ 𝐆𝐫𝐳 := by
  apply normal_weakerThan_of_maxm;
  intro p hp;
  rcases hp with (hK | hGrz)
  . obtain ⟨_, _, rfl⟩ := hK; exact axiomK!;
  . obtain ⟨_, _, rfl⟩ := hGrz; exact axiomT!;

lemma K4_weakerThan_Grz : (𝐊𝟒 : Hilbert α) ≤ₛ 𝐆𝐫𝐳 := by
  apply normal_weakerThan_of_maxm;
  intro p hp;
  rcases hp with (hK | hGrz)
  . obtain ⟨_, _, rfl⟩ := hK; exact axiomK!;
  . obtain ⟨_, _, rfl⟩ := hGrz; exact axiomFour!;


lemma KD_weakerThan_KP : (𝐊𝐃 : Hilbert α) ≤ₛ 𝐊𝐏 := normal_weakerThan_of_maxm $ by
  rintro p (⟨p, q, rfl⟩ | ⟨p, rfl⟩);
  . exact axiomK!;
  . exact axiomD!;

lemma KP_weakerThan_KD : (𝐊𝐏 : Hilbert α) ≤ₛ 𝐊𝐃 := normal_weakerThan_of_maxm $ by
  rintro p (⟨p, q, rfl⟩ | ⟨_, rfl⟩);
  . exact axiomK!;
  . exact axiomP!;

lemma KD_equiv_KP : (𝐊𝐃 : Hilbert α) =ₛ 𝐊𝐏 := Equiv.antisymm_iff.mpr ⟨KD_weakerThan_KP, KP_weakerThan_KD⟩


lemma GL_weakerThan_K4Loeb : (𝐆𝐋 : Hilbert α) ≤ₛ 𝐊𝟒(𝐋) := by
  apply System.weakerThan_iff.mpr;
  intro p h;
  induction h using Deduction.inducition_with_necOnly! with
  | hMaxm hp =>
    rcases hp with (hK | hL)
    . obtain ⟨_, _, rfl⟩ := hK; exact axiomK!;
    . obtain ⟨_, rfl⟩ := hL; exact axiomL!;
  | hMdp ihpq ihp => exact ihpq ⨀ ihp;
  | hNec ihp => exact nec! ihp;
  | _ => trivial;

lemma K4Loeb_weakerThan_K4Henkin : (𝐊𝟒(𝐋) : Hilbert α) ≤ₛ 𝐊𝟒(𝐇) := by
  apply System.weakerThan_iff.mpr;
  intro p h;
  induction h using Deduction.inducition! with
  | hMaxm hp =>
    rcases hp with (hK | hFour)
    . obtain ⟨_, _, rfl⟩ := hK; exact axiomK!;
    . obtain ⟨_, rfl⟩ := hFour; exact axiomFour!;
  | hMdp ihpq ihp => exact ihpq ⨀ ihp;
  | hRules rl hrl hant ihp =>
    rcases hrl with (hNec | hLoeb);
    . obtain ⟨p, rfl⟩ := hNec; exact nec! $ ihp $ by simp_all only [List.mem_singleton, forall_eq];
    . obtain ⟨p, rfl⟩ := hLoeb; exact loeb! $ ihp $ by simp_all only [List.mem_singleton, forall_eq];
  | _ => trivial;

lemma K4Henkin_weakerThan_K4H : (𝐊𝟒(𝐇) : Hilbert α) ≤ₛ 𝐊𝟒𝐇 := by
  apply System.weakerThan_iff.mpr;
  intro p h;
  induction h using Deduction.inducition! with
  | hMaxm hp =>
    rcases hp with (hK | hFour)
    . obtain ⟨_, _, rfl⟩ := hK; exact axiomK!;
    . obtain ⟨_, rfl⟩ := hFour; exact axiomFour!;
  | hMdp ihpq ihp => exact ihpq ⨀ ihp;
  | hRules rl hrl hant ihp =>
    rcases hrl with (hNec | hHenkin);
    . obtain ⟨p, rfl⟩ := hNec; exact nec! $ ihp $ by simp_all only [List.mem_singleton, forall_eq];
    . obtain ⟨p, rfl⟩ := hHenkin; exact henkin! $ ihp $ by simp_all only [List.mem_singleton, forall_eq];
  | _ => trivial;

lemma K4Henkin_weakerThan_GL : (𝐊𝟒𝐇 : Hilbert α) ≤ₛ 𝐆𝐋 := by
  apply normal_weakerThan_of_maxm;
  intro p hp;
  rcases hp with hK | hFour | hH
  . obtain ⟨_, _, rfl⟩ := hK; exact axiomK!;
  . obtain ⟨_, _, rfl⟩ := hFour; exact axiomFour!;
  . obtain ⟨_, _, rfl⟩ := hH; exact axiomH!;

lemma GL_equiv_K4Loeb : (𝐆𝐋 : Hilbert α) =ₛ 𝐊𝟒(𝐋) := by
  apply Equiv.antisymm_iff.mpr;
  constructor;
  . exact GL_weakerThan_K4Loeb;
  . exact WeakerThan.trans (K4Loeb_weakerThan_K4Henkin) $ WeakerThan.trans K4Henkin_weakerThan_K4H K4Henkin_weakerThan_GL

lemma GL_weakerThan_GLS : (𝐆𝐋 : Hilbert α) ≤ₛ 𝐆𝐋𝐒 := by
  apply System.weakerThan_iff.mpr;
  intro p h;
  exact Deduction.maxm! (by left; simpa);

lemma S5Grz_weakerThan_Triv : (𝐒𝟓𝐆𝐫𝐳 : Hilbert α) ≤ₛ 𝐓𝐫𝐢𝐯 := by
  apply normal_weakerThan_of_maxm;
  intro p hp;
  rcases hp with ⟨_, _, rfl⟩ | (⟨_, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩
  . exact axiomK!;
  . exact axiomT!;
  . exact axiomFive!;
  . exact axiomGrz!;

lemma Triv_weakerThan_S5Grz : (𝐓𝐫𝐢𝐯 : Hilbert α) ≤ₛ 𝐒𝟓𝐆𝐫𝐳 := by
  apply normal_weakerThan_of_maxm;
  intro p hp;
  rcases hp with ⟨_, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
  . exact axiomK!;
  . exact axiomT!;
  . exact axiomTc!;

lemma S5Grz_equiv_Triv : (𝐒𝟓𝐆𝐫𝐳 : Hilbert α) =ₛ 𝐓𝐫𝐢𝐯
  := Equiv.antisymm_iff.mpr ⟨S5Grz_weakerThan_Triv, Triv_weakerThan_S5Grz⟩

end

end LO.Modal
