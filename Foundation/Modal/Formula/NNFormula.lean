module

public import Foundation.Modal.Formula.Basic

@[expose] public section

namespace LO.Modal

variable {α : Type u}

inductive NNFormula (α : Type u) : Type u where
  | atom   : α → NNFormula α
  | natom  : α → NNFormula α
  | falsum : NNFormula α
  | verum  : NNFormula α
  | or     : NNFormula α → NNFormula α → NNFormula α
  | and    : NNFormula α → NNFormula α → NNFormula α
  | box    : NNFormula α → NNFormula α
  | dia    : NNFormula α → NNFormula α
  deriving DecidableEq

namespace NNFormula

variable {φ ψ χ : NNFormula α}

def neg : NNFormula α → NNFormula α
  | atom a  => natom a
  | natom a => atom a
  | falsum  => verum
  | verum   => falsum
  | or φ ψ  => and (neg φ) (neg ψ)
  | and φ ψ => or (neg φ) (neg ψ)
  | box φ   => dia (neg φ)
  | dia φ   => box (neg φ)

def imp (φ ψ : NNFormula α) : NNFormula α := or (neg φ) ψ

instance : BasicModalLogicalConnective (NNFormula α) where
  tilde := neg
  arrow := imp
  wedge := and
  vee := or
  top := verum
  bot := falsum
  box := box
  dia := dia

lemma or_eq : or φ ψ = φ ⋎ ψ := rfl

lemma and_eq : and φ ψ = φ ⋏ ψ := rfl

lemma imp_eq : imp φ ψ = φ ➝ ψ := rfl

lemma box_eq : box φ = □φ := rfl

lemma dia_eq : dia φ = ◇φ := rfl

@[simp] lemma imp_eq' : φ ➝ ψ = ∼φ ⋎ ψ := rfl

@[simp] lemma iff_eq : φ ⭤ ψ = (φ ➝ ψ) ⋏ (ψ ➝ φ) := rfl

lemma falsum_eq : (falsum : NNFormula α) = ⊥ := rfl

lemma verum_eq : (verum : NNFormula α) = ⊤ := rfl

@[simp] lemma and_inj (φ₁ ψ₁ φ₂ ψ₂ : Formula α) : φ₁ ⋏ φ₂ = ψ₁ ⋏ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by simp [Wedge.wedge]

@[simp] lemma or_inj (φ₁ ψ₁ φ₂ ψ₂ : Formula α) : φ₁ ⋎ φ₂ = ψ₁ ⋎ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by simp [Vee.vee]

@[simp] lemma imp_inj (φ₁ ψ₁ φ₂ ψ₂ : Formula α) : φ₁ ➝ φ₂ = ψ₁ ➝ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by simp [Arrow.arrow]

@[simp] lemma neg_inj (φ ψ : Formula α) : ∼φ = ∼ψ ↔ φ = ψ := by simp [NegAbbrev.neg];

lemma neg_eq : neg φ = ∼φ := rfl

@[simp] lemma neg_atom (a : α) : ∼atom a = natom a := by rfl

@[simp] lemma neg_natom (a : α) : ∼natom a = atom a := by rfl

@[grind =]
lemma negneg : ∼∼φ = φ := by
  induction φ with
  | and φ ψ ihφ ihψ =>
    simp only [←neg_eq, neg, and.injEq];
    exact ⟨ihφ, ihψ⟩;
  | or φ ψ ihφ ihψ =>
    simp only [←neg_eq, neg, or.injEq];
    exact ⟨ihφ, ihψ⟩;
  | box φ ihφ =>
    simp only [←neg_eq, neg, box.injEq];
    exact ihφ;
  | dia φ ihφ =>
    simp only [←neg_eq, neg, dia.injEq];
    exact ihφ;
  | _ => tauto;

instance : ModalDeMorgan (NNFormula α) where
  verum   := by tauto;
  falsum  := by tauto;
  imply   := by tauto;
  and     := by tauto;
  or      := by tauto;
  neg     := by grind;
  neg_dia := by tauto;
  neg_box := by tauto;

section toString

variable [ToString α]
def toStr : NNFormula α → String
  | atom a  => s!"+{a}"
  | natom a => s!"-{a}"
  | falsum  => "⊥"
  | verum   => "⊤"
  | or φ ψ  => s!"({φ.toStr} ∨ {ψ.toStr})"
  | and φ ψ => s!"({φ.toStr} ∧ {ψ.toStr})"
  | box φ   => s!"□{φ.toStr}"
  | dia φ   => s!"◇{φ.toStr}"
instance : Repr (NNFormula α) := ⟨fun t _ => toStr t⟩

end toString


section toFormula

def toFormula : NNFormula α → Formula α
  | atom a  => Formula.atom a
  | natom a => ∼Formula.atom a
  | ⊥       => ⊥
  | ⊤       => ⊤
  | φ ⋎ ψ   => φ.toFormula ⋎ ψ.toFormula
  | φ ⋏ ψ   => φ.toFormula ⋏ ψ.toFormula
  | □φ      => □(φ.toFormula)
  | ◇φ      => ◇(φ.toFormula)
instance : Coe (NNFormula α) (Formula α) := ⟨toFormula⟩

@[simp] lemma toFormula_atom (a : α) : toFormula  (.atom a) = Formula.atom a := rfl

@[simp] lemma toFormula_natom (a : α) : toFormula (.natom a) = ∼Formula.atom a := rfl

@[simp] lemma toFormula_falsum : toFormula ⊥ = (⊥ : Formula α) := rfl

@[simp] lemma toFormula_verum : toFormula ⊤ = (⊤ : Formula α) := rfl

end toFormula


section

@[elab_as_elim]
def cases'
  {C : NNFormula α → Sort v}
  (hAtom   : ∀ a, C (atom a))
  (hNatom  : ∀ a, C (natom a))
  (hFalsum : C ⊥)
  (hVerum  : C ⊤)
  (hOr     : ∀ φ ψ, C (φ ⋎ ψ))
  (hAnd    : ∀ φ ψ, C (φ ⋏ ψ))
  (hBox    : ∀ φ, C (□φ))
  (hDia    : ∀ φ, C (◇φ))
  : ∀ φ, C φ
  | atom a  => hAtom a
  | natom a => hNatom a
  | ⊥  => hFalsum
  | ⊤   => hVerum
  | φ ⋎ ψ => hOr φ ψ
  | φ ⋏ ψ => hAnd φ ψ
  | □φ => hBox φ
  | ◇φ => hDia φ

@[elab_as_elim]
def rec'
  {C : NNFormula α → Sort v}
  (hAtom   : ∀ a, C (atom a))
  (hNatom  : ∀ a, C (natom a))
  (hFalsum : C ⊥)
  (hVerum  : C ⊤)
  (hOr     : ∀ φ ψ, C φ → C ψ → C (φ ⋎ ψ))
  (hAnd    : ∀ φ ψ, C φ → C ψ → C (φ ⋏ ψ))
  (hBox    : ∀ φ, C φ → C (□φ))
  (hDia    : ∀ φ, C φ → C (◇φ))
  : ∀ φ, C φ
  | atom a  => hAtom a
  | natom a => hNatom a
  | falsum  => hFalsum
  | verum   => hVerum
  | or φ ψ => hOr φ ψ (rec' hAtom hNatom hFalsum hVerum hOr hAnd hBox hDia φ) (rec' hAtom hNatom hFalsum hVerum hOr hAnd hBox hDia ψ)
  | and φ ψ => hAnd φ ψ (rec' hAtom hNatom hFalsum hVerum hOr hAnd hBox hDia φ) (rec' hAtom hNatom hFalsum hVerum hOr hAnd hBox hDia ψ)
  | box φ => hBox φ (rec' hAtom hNatom hFalsum hVerum hOr hAnd hBox hDia φ)
  | dia φ => hDia φ (rec' hAtom hNatom hFalsum hVerum hOr hAnd hBox hDia φ)

end


section Decidable

end Decidable


section Encodable

open Encodable

variable [Encodable α]

def toNat : NNFormula α → Nat
  | ⊥       => (Nat.pair 0 0) + 1
  | ⊤       => (Nat.pair 1 0) + 1
  | atom a  => (Nat.pair 2 <| encode a) + 1
  | natom a => (Nat.pair 3 <| encode a) + 1
  | φ ⋎ ψ   => (Nat.pair 4 <| Nat.pair φ.toNat ψ.toNat) + 1
  | φ ⋏ ψ   => (Nat.pair 5 <| Nat.pair φ.toNat ψ.toNat) + 1
  | □φ      => (Nat.pair 6 <| φ.toNat) + 1
  | ◇φ      => (Nat.pair 7 <| φ.toNat) + 1

def ofNat : Nat → Option (NNFormula α)
  | 0 => none
  | e + 1 =>
    let idx := e.unpair.1
    let c := e.unpair.2
    match idx with
    | 0 => some ⊥
    | 1 => some ⊤
    | 2 => (decode c).map NNFormula.atom
    | 3 => (decode c).map NNFormula.natom
    | 4 =>
      have : c.unpair.1 < e + 1 := Nat.lt_succ_iff.mpr $ le_trans (Nat.unpair_left_le _) $ Nat.unpair_right_le _
      have : c.unpair.2 < e + 1 := Nat.lt_succ_iff.mpr $ le_trans (Nat.unpair_right_le _) $ Nat.unpair_right_le _
      do
        let φ ← ofNat c.unpair.1
        let ψ ← ofNat c.unpair.2
        return φ ⋎ ψ
    | 5 =>
      have : c.unpair.1 < e + 1 := Nat.lt_succ_iff.mpr $ le_trans (Nat.unpair_left_le _) $ Nat.unpair_right_le _
      have : c.unpair.2 < e + 1 := Nat.lt_succ_iff.mpr $ le_trans (Nat.unpair_right_le _) $ Nat.unpair_right_le _
      do
        let φ ← ofNat c.unpair.1
        let ψ ← ofNat c.unpair.2
        return φ ⋏ ψ
    | 6 =>
      have : c < e + 1 := Nat.lt_succ_iff.mpr $ Nat.unpair_right_le _
      do
        let φ ← ofNat c;
        return □φ
    | 7 =>
      have : c < e + 1 := Nat.lt_succ_iff.mpr $ Nat.unpair_right_le _
      do
        let φ ← ofNat c;
        return ◇φ
    | _ => none

instance : Encodable (NNFormula α) where
  encode := toNat
  decode := ofNat
  encodek := by
    intro φ;
    induction φ using rec' <;> simp [toNat, ofNat, encodek, *]

end Encodable

def isPrebox : NNFormula α → Prop
  | □_ => true
  | _   => false

lemma exists_isPrebox (hφ : φ.isPrebox) : ∃ ψ, φ = □ψ := by match φ with | □ψ => exact ⟨ψ, rfl⟩

def isPredia : NNFormula α → Prop
  | ◇_ => true
  | _   => false

lemma exists_isPredia (hφ : φ.isPredia) : ∃ ψ, φ = ◇ψ := by match φ with | ◇ψ => exact ⟨ψ, rfl⟩

def degree : NNFormula α → Nat
  | ⊤       => 0
  | ⊥       => 0
  | atom _  => 0
  | natom _ => 0
  | φ ⋏ ψ   => max φ.degree ψ.degree
  | φ ⋎ ψ   => max φ.degree ψ.degree
  | □φ      => φ.degree + 1
  | ◇φ      => φ.degree + 1



abbrev isModalCNFPart (φ : NNFormula α) :=
  ∃ Γ : List { ψ : NNFormula α // ψ.isPrebox ∨ ψ.isPredia ∨ ψ.degree = 0 }, φ = ⋁Γ.unattach

namespace isModalCNFPart

variable {a : α} {φ ψ : NNFormula α}

lemma def_atom : isModalCNFPart (.atom a) := by use [⟨(.atom a), by tauto⟩]; tauto;
lemma def_natom : isModalCNFPart (.natom a) := by use [⟨(.natom a), by tauto⟩]; tauto;
lemma def_verum : isModalCNFPart (⊤ : NNFormula α) := by use [⟨⊤, by tauto⟩]; tauto;
lemma def_falsum : isModalCNFPart (⊥ : NNFormula α) := by use [⟨⊥, by tauto⟩]; tauto;
lemma def_box : isModalCNFPart (□φ) := by use [⟨□φ, by tauto⟩]; tauto;
lemma def_dia : isModalCNFPart (◇φ) := by use [⟨◇φ, by tauto⟩]; tauto;

end isModalCNFPart


def isModalCNF (φ : NNFormula α) := ∃ Γ : List { ψ // isModalCNFPart ψ }, φ = ⋀Γ.unattach

namespace isModalCNF

@[simp] lemma def_atom {a : α} : isModalCNF (.atom a) := by use [⟨(.atom a), isModalCNFPart.def_atom⟩]; simp;
@[simp] lemma def_natom {a : α} : isModalCNF (.natom a) := by use [⟨(.natom a), isModalCNFPart.def_natom⟩]; simp;
@[simp] lemma def_falsum : isModalCNF (⊥ : NNFormula α) := by use [⟨⊥, isModalCNFPart.def_falsum⟩]; simp;
@[simp] lemma def_verum : isModalCNF (⊤ : NNFormula α) := by use [⟨⊤, isModalCNFPart.def_verum⟩]; simp;
@[simp] lemma def_box {φ : NNFormula α} : isModalCNF (□φ) := by use [⟨□φ, isModalCNFPart.def_box⟩]; simp;
@[simp] lemma def_dia {φ : NNFormula α} : isModalCNF (◇φ) := by use [⟨◇φ, isModalCNFPart.def_dia⟩]; simp;

end isModalCNF


def isModalDNFPart : NNFormula α → Prop
  | φ ⋏ ψ  => (φ.isModalDNFPart) ∧ (ψ.isModalDNFPart)
  | φ      => φ.isPrebox ∨ φ.isPredia ∨ φ.degree = 0


namespace isModalDNFPart

lemma of_degree_zero {φ : NNFormula α} (h : φ.degree = 0) : isModalDNFPart φ := by
  induction φ using rec' with
  | hAnd φ ψ ihφ ihψ =>
    constructor;
    . apply ihφ; simp_all [degree];
    . apply ihψ; simp_all [degree];
  | _ => tauto;

end isModalDNFPart


def isModalDNF : NNFormula α → Prop
  | φ ⋎ ψ => φ.isModalDNF ∧ ψ.isModalDNF
  | φ => φ.isModalDNFPart

namespace isModalDNF

@[simp] lemma def_atom {a : α} : isModalDNF (.atom a) := by simp [isModalDNF, isModalDNFPart, degree]
@[simp] lemma def_natom {a : α} : isModalDNF (.natom a) := by simp [isModalDNF, isModalDNFPart, degree]
@[simp] lemma def_falsum : isModalDNF (⊥ : NNFormula α) := by simp [isModalDNF, isModalDNFPart, degree]
@[simp] lemma def_verum : isModalDNF (⊤ : NNFormula α) := by simp [isModalDNF, isModalDNFPart, degree]
@[simp] lemma def_box {φ : NNFormula α} : isModalDNF (□φ) := by simp [isModalDNF, isPrebox, isModalDNFPart]
@[simp] lemma def_dia {φ : NNFormula α} : isModalDNF (◇φ) := by simp [isModalDNF, isPredia, isModalDNFPart]


end isModalDNF

end NNFormula


namespace Formula

def toNNFormula : Formula α → NNFormula α
  | atom a  => NNFormula.atom a
  | ⊥       => NNFormula.falsum
  | φ ➝ ψ   => φ.toNNFormula.neg ⋎ ψ.toNNFormula
  | □φ      => □φ.toNNFormula
instance : Coe (Formula α) (NNFormula α) := ⟨toNNFormula⟩

@[simp] lemma toNNFormula_atom (a : α) : toNNFormula (atom a) = .atom a := rfl

@[simp] lemma toNNFormula_falsum : toNNFormula ⊥ = (⊥ : NNFormula α) := rfl

end Formula


end LO.Modal
end
