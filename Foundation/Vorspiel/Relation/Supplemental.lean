import Mathlib.Logic.Relation

attribute [mk_iff] IsAntisymm

section

variable {α : Sort*} (rel : α → α → Prop)
local infix:50 " ≺ " => rel

def Asymmetric := ∀ ⦃x y⦄, (x ≺ y) → ¬(y ≺ x)

def Euclidean := ∀ ⦃x y z⦄, x ≺ y → x ≺ z → z ≺ y

def Serial := ∀ x, ∃ y, x ≺ y

def Confluent := ∀ ⦃x y z⦄, ((x ≺ y ∧ x ≺ z) → ∃ w, (y ≺ w ∧ z ≺ w))

def WeakConfluent := ∀ ⦃x y z⦄, (x ≺ y ∧ x ≺ z ∧ y ≠ z) → (∃ w, y ≺ w ∧ z ≺ w)

def Dense := ∀ ⦃x y⦄, x ≺ y → ∃z, x ≺ z ∧ z ≺ y

def Connected := ∀ ⦃x y z⦄, (x ≺ y ∧ x ≺ z) → (y ≺ z ∨ z ≺ y)

def WeakConnected := ∀ ⦃x y z⦄, (x ≺ y ∧ x ≺ z ∧ y ≠ z) → (y ≺ z ∨ z ≺ y)

def Functional := ∀ ⦃x y z⦄, x ≺ y ∧ x ≺ z → y = z

def RightConvergent := ∀ ⦃x y z⦄, x ≺ y ∧ x ≺ z → y ≺ z ∨ z ≺ y ∨ y = z

def Coreflexive := ∀ ⦃x y⦄, x ≺ y → x = y

def Equality := ∀ ⦃x y⦄, x ≺ y ↔ x = y

def Isolated := ∀ ⦃x y⦄, ¬(x ≺ y)

def Universal := ∀ ⦃x y⦄, x ≺ y

end


section

variable (α : Sort*) (rel : α → α → Prop)

@[mk_iff] class IsEuclidean : Prop where euclidean : Euclidean rel

@[mk_iff] class IsSerial : Prop where serial : Serial rel

@[mk_iff] class IsConfluent : Prop where confluent : Confluent rel

@[mk_iff] class IsWeakConfluent : Prop where weak_confluent : WeakConfluent rel

@[mk_iff] class IsConnected : Prop where connected : Connected rel

@[mk_iff] class IsWeakConnected : Prop where weak_connected : WeakConnected rel

@[mk_iff] class IsCoreflexive : Prop where coreflexive : Coreflexive rel

@[mk_iff] class IsEquality : Prop where equality : Equality rel

@[mk_iff] class IsIsolated : Prop where isolated : Isolated rel

@[mk_iff] class IsUniversal : Prop where universal : Universal rel

end



section

variable {α : Type*} {rel : α → α → Prop}

lemma serial_of_refl (hRefl : Reflexive rel) : Serial rel := by
  rintro w;
  use w;
  exact hRefl w;

instance [IsRefl α rel] : IsSerial α rel := ⟨serial_of_refl IsRefl.reflexive⟩


lemma eucl_of_symm_trans (hSymm : Symmetric rel) (hTrans : Transitive rel) : Euclidean rel := by
  intro x y z Rxy Rxz;
  have Ryx := hSymm Rxy;
  exact hSymm $ hTrans Ryx Rxz;

instance [IsSymm α rel] [IsTrans α rel] : IsEuclidean α rel := ⟨eucl_of_symm_trans IsSymm.symm IsTrans.trans⟩


lemma trans_of_symm_eucl (hSymm : Symmetric rel) (hEucl : Euclidean rel) : Transitive rel := by
  rintro x y z Rxy Ryz;
  exact hSymm $ hEucl (hSymm Rxy) Ryz;

instance [IsSymm α rel] [IsEuclidean α rel] : IsTrans α rel := ⟨trans_of_symm_eucl IsSymm.symm IsEuclidean.euclidean⟩


lemma symm_of_refl_eucl (hRefl : Reflexive rel) (hEucl : Euclidean rel) : Symmetric rel := by
  intro x y Rxy;
  exact hEucl (hRefl x) Rxy;

instance [IsRefl α rel] [IsEuclidean α rel] : IsSymm α rel := ⟨symm_of_refl_eucl IsRefl.reflexive IsEuclidean.euclidean⟩


lemma trans_of_refl_eucl (hRefl : Reflexive rel) (hEucl : Euclidean rel) : Transitive rel := by
  have hSymm := symm_of_refl_eucl hRefl hEucl;
  exact trans_of_symm_eucl hSymm hEucl;

instance [IsRefl α rel] [IsEuclidean α rel] : IsTrans α rel := ⟨trans_of_refl_eucl IsRefl.reflexive IsEuclidean.euclidean⟩


lemma refl_of_symm_serial_eucl (hSymm : Symmetric rel) (hSerial : Serial rel) (hEucl : Euclidean rel) : Reflexive rel := by
  rintro x;
  obtain ⟨y, Rxy⟩ := hSerial x;
  have Ryx := hSymm Rxy;
  exact trans_of_symm_eucl hSymm hEucl Rxy Ryx;

instance [IsSymm α rel] [IsSerial α rel] [IsEuclidean α rel] : IsRefl α rel := ⟨refl_of_symm_serial_eucl IsSymm.symm IsSerial.serial IsEuclidean.euclidean⟩


lemma corefl_of_refl_assym_eucl (hRefl : Reflexive rel) (hAntisymm : AntiSymmetric rel) (hEucl : Euclidean rel) : Coreflexive rel := by
  intro x y Rxy;
  have Ryx := hEucl (hRefl x) Rxy;
  exact hAntisymm Rxy Ryx;

instance [IsRefl α rel] [IsAntisymm α rel] [IsEuclidean α rel] : IsCoreflexive α rel := ⟨corefl_of_refl_assym_eucl IsRefl.reflexive IsAntisymm.antisymm IsEuclidean.euclidean⟩


lemma equality_of_refl_corefl (hRefl : Reflexive rel) (hCorefl : Coreflexive rel) : Equality rel := by
  intro x y;
  constructor;
  . apply hCorefl;
  . rintro rfl; apply hRefl;

instance [IsRefl α rel] [IsCoreflexive α rel] : IsEquality α rel := ⟨equality_of_refl_corefl IsRefl.reflexive IsCoreflexive.coreflexive⟩


lemma refl_of_equality (h : Equality rel) : Reflexive rel := by
  intro x;
  exact h.mpr rfl;

instance [IsEquality α rel] : IsRefl α rel := ⟨refl_of_equality IsEquality.equality⟩


lemma corefl_of_equality (h : Equality rel) : Coreflexive rel := by
  intro x y Rxy;
  apply h.mp Rxy;

instance [IsEquality α rel] : IsCoreflexive α rel := ⟨corefl_of_equality IsEquality.equality⟩


lemma irreflexive_of_assymetric (hAssym : Asymmetric rel) : Irreflexive rel := by
  intro x Rxx;
  have := hAssym Rxx;
  contradiction;

instance [IsAsymm α rel] : IsIrrefl α rel := ⟨irreflexive_of_assymetric IsAsymm.asymm⟩


lemma refl_of_universal (h : Universal rel) : Reflexive rel := by intro x; exact @h x x;

instance [IsUniversal α rel] : IsRefl α rel := ⟨refl_of_universal IsUniversal.universal⟩


lemma eucl_of_universal (h : Universal rel) : Euclidean rel := by rintro x y z _ _; exact @h z y;

instance [IsUniversal α rel] : IsEuclidean α rel := ⟨eucl_of_universal IsUniversal.universal⟩


lemma confluent_of_refl_connected (hRefl : Reflexive rel) (hConfl : Connected rel) : Confluent rel := by
  rintro x y z ⟨Rxy, Rxz⟩;
  rcases @hConfl x y z ⟨Rxy, Rxz⟩ with (Ryz | Rzy);
  . use z;
    constructor;
    . assumption;
    . apply hRefl;
  . use y;
    constructor;
    . apply hRefl;
    . assumption;

instance [IsRefl α rel] [IsConnected α rel] : IsConfluent α rel := ⟨confluent_of_refl_connected IsRefl.reflexive IsConnected.connected⟩


end
