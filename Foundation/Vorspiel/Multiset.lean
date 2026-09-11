module

public import Mathlib.Data.Multiset.AddSub
public import Mathlib.Data.Multiset.Basic
public import Mathlib.Logic.Encodable.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Algebra.Order.Group.Multiset

@[expose] public section

namespace Multiset

/-- Function to avoid reducing `{a} + s` to `a ::ₘ s` -/
def atom (a : α) : Multiset α := {a}

/-- `⦃x, y, z, ...⦄` notation for `kpair` -/
syntax "⦃" term,* "⦄" : term

macro_rules
  | `(⦃$terms:term,*, $term:term⦄) => `(⦃$terms,*⦄ + atom $term)
  | `(⦃$term:term⦄) => `(atom $term)
  | `(⦃⦄) => `(0)

@[app_unexpander atom]
meta def pairUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $term) => `(⦃$term⦄)
  | _ => throw ()

lemma atom_eq_singleton (a : α) : ⦃a⦄ = {a} := rfl

lemma add_atom_eq_cons (a : α) (s : Multiset α) : s + ⦃a⦄ = a ::ₘ s := by
  rw [atom_eq_singleton, add_comm]; simp

@[simp] lemma mem_atom_iff {a b : α} : a ∈ ⦃b⦄ ↔ a = b := by simp [atom_eq_singleton]

@[simp] lemma atom_le_iff {a : α} {s : Multiset α} : ⦃a⦄ ≤ s ↔ a ∈ s := by simp [atom_eq_singleton]

@[simp] lemma atom_subset_iff {a : α} {s : Multiset α} : ⦃a⦄ ⊆ s ↔ a ∈ s := by simp [atom_eq_singleton]

@[simp] lemma map_atom (f : α → β) (a : α) : ⦃a⦄.map f = ⦃f a⦄ := by
  simp [atom_eq_singleton]

/-- Universal membership over a sum splits into the two summands. This is a routine
property of multiset membership. -/
@[simp] lemma forall_mem_add {p : α → Prop} {s t : Multiset α} :
    (∀ a ∈ s + t, p a) ↔ (∀ a ∈ s, p a) ∧ ∀ a ∈ t, p a := by
  simp only [mem_add, or_imp, forall_and]

/-- Universal membership over an atom reduces to its unique member. This is a routine
property of multiset membership. -/
@[simp] lemma forall_mem_atom {p : α → Prop} {a : α} : (∀ b ∈ ⦃a⦄, p b) ↔ p a := by
  simp only [mem_atom_iff, forall_eq]

/-- After filtering out `a`, adjoining `f a` recovers every mapped member.
This is a routine technical property of multiset membership. -/
lemma add_map_subset_map_filter_add_atom [DecidableEq α]
    (s : Multiset α) (t : Multiset β) (f : α → β) (a : α) :
    t + s.map f ⊆ (s.filter (· ≠ a)).map f + ⦃f a⦄ + t := by
  intro b hb
  rcases mem_add.mp hb with hb | hb
  · exact mem_add.mpr (Or.inr hb)
  · obtain ⟨c, hc, rfl⟩ := mem_map.mp hb
    by_cases h : c = a
    · subst c
      exact mem_add.mpr <| Or.inl <| mem_add.mpr <| Or.inr <| by simp
    · exact mem_add.mpr <| Or.inl <| mem_add.mpr <| Or.inl <|
        mem_map.mpr ⟨c, mem_filter.mpr ⟨hc, h⟩, rfl⟩

/-- Constructively extract a preimage from a mapped multiset over an encodable type. -/
def getPreimage [Encodable α] [DecidableEq β] {f : α → β} {s : Multiset α}
    (h : b ∈ s.map f) : {a : α // a ∈ s ∧ f a = b} := by
  letI := Encodable.decidableEqOfEncodable α
  exact Encodable.chooseX (mem_map.mp h)

lemma map_subset_iff {s₁ s₂ : Multiset α} (f : α → β) (hf : Function.Injective f) :
    map f s₁ ⊆ map f s₂ ↔ s₁ ⊆ s₂ := by
  constructor
  · intro h a ha
    have : f a ∈ map f s₁ := by simp; grind
    have : ∃ a' ∈ s₂, f a' = f a := by simpa using h this
    obtain ⟨a', ha', heq⟩ := this
    rcases hf heq
    assumption
  · exact map_subset_map

inductive Traversal {α : Type*} : Multiset α → Type _ where
  | zero : Traversal 0
  | succ (a : α) : Traversal s → Traversal (s + ⦃a⦄)

namespace Traversal

def cast {s t : Multiset α} (h : s = t) : Traversal s → Traversal t := fun t ↦ h ▸ t

def atom (a : α) : Traversal ⦃a⦄ := zero.succ a

def add (t₁ : Traversal s₁) (t₂ : Traversal s₂) : Traversal (s₁ + s₂) :=
  match t₂ with
  |     zero => t₁.cast (by simp)
  | succ a t => (add t₁ t).succ a |>.cast (by abel)

def toList {s : Multiset α} : Traversal s → List α
  |     zero => []
  | succ a t => a :: t.toList

lemma toList_cast {s t : Multiset α} (h : s = t) (u : Traversal s) :
    (u.cast h).toList = u.toList := by
  cases h
  rfl

@[simp] lemma coe_toList {s : Multiset α} (t : Traversal s) : (t.toList : Multiset α) = s :=
  match t with
  |     zero => rfl
  | succ a t => by
    simp [toList, coe_toList t, add_atom_eq_cons, ←Multiset.cons_coe]

def ofList : (l : List α) → Traversal (l : Multiset α)
  |     [] => zero
  | a :: t => (ofList t).succ a |>.cast (by simp [add_atom_eq_cons, ←Multiset.cons_coe])

lemma toList_ofList (l : List α) : (ofList l).toList = l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    change (cast _ (succ a (ofList l))).toList = _
    rw [toList_cast]
    exact congrArg (List.cons a) ih

lemma ofList_toList {s : Multiset α} (t : Traversal s) :
    (ofList t.toList).cast (by simp) = t := by
  induction t with
  | zero => rfl
  | succ a t ih =>
    dsimp [toList, ofList]
    have h₁ := congrArg (succ a) ih
    convert h₁ using 1 <;> apply proof_irrelheq

def equiv {s : Multiset α} : Traversal s ≃ {l : List α // (l : Multiset α) = s} where
  toFun t := ⟨t.toList, by simp⟩
  invFun l := ofList l.1 |>.cast (by simp [l.2])
  left_inv t := ofList_toList t
  right_inv s := by
    apply Subtype.ext
    simp [toList_cast, toList_ofList]

/-- Construct a traversal after applying a function to every element. -/
def map (f : α → β) {s : Multiset α} (t : Traversal s) : Traversal (s.map f) :=
  (ofList (t.toList.map f)).cast (by
    simpa only [Multiset.map_coe] using congrArg (Multiset.map f) t.coe_toList)

/-- Construct a traversal after removing one occurrence of an element. -/
def erase [DecidableEq α] (a : α) {s : Multiset α} (t : Traversal s) :
    Traversal (s.erase a) :=
  (ofList (t.toList.erase a)).cast (by
    simpa only [Multiset.coe_erase] using congrArg (fun u ↦ u.erase a) t.coe_toList)

/-- Remove the distinguished occurrence from a traversal of an adjoined atom. -/
def remove [DecidableEq α] {a : α} {s : Multiset α}
    (t : Traversal (s + ⦃a⦄)) : Traversal s :=
  (erase a t).cast (by
    rw [atom_eq_singleton, erase_add_right_pos s (mem_singleton_self a)]
    rw [erase_singleton, add_zero]
    )

/-- Constructively extract a preimage from a mapped traversal. -/
def getPreimage [DecidableEq β] {f : α → β} {s : Multiset α}
    (t : Traversal s) {b : β} (h : b ∈ s.map f) :
    {a : α // a ∈ s ∧ f a = b} := by
  have hex : ∃ a ∈ t.toList, f a = b := by
    have h' : b ∈ Multiset.map f (t.toList : Multiset α) := by
      rw [t.coe_toList]
      exact h
    obtain ⟨a, ha, hab⟩ := mem_map.mp h'
    exact ⟨a, ha, hab⟩
  let w : {a : α // a ∈ t.toList ∧ f a = b} :=
    List.chooseX (fun a ↦ f a = b) t.toList hex
  have hs : w.1 ∈ s := by
    have hc := t.coe_toList
    exact Eq.mp (congrArg (fun m : Multiset α => w.1 ∈ m) hc) w.2.1
  exact ⟨w.1, hs, w.2.2⟩

noncomputable instance inhabited {s : Multiset α} : Inhabited (Traversal s) :=
  ⟨ofList (s.toList) |>.cast (by simp)⟩

end Traversal

end Multiset
