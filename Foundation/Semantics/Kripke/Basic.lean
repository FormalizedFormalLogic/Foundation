module

public import Foundation.Logic.LindenbaumAlgebra

@[expose] public section

namespace LO

variable {α : Type u}

structure KripkeFrame (α : Type u) where
  points : Set α
  points_nonempty : points.Nonempty
  Rel : α → α → Prop

namespace KripkeFrame

variable {K : KripkeFrame α}

class Generated (K : KripkeFrame α) (R : Set K.points) (hR : R ≠ ∅) : Prop where
  generated : ∀ x : K.points, ∃ r ∈ R, K.Rel r x
alias generated := Generated.generated


class Rooted (K : KripkeFrame α) (r : K.points) extends Generated K {r} (by simp)
@[grind .]
lemma rooted {r} [hR : K.Rooted r] : ∀ x : K.points, K.Rel r x := by simpa using hR.generated;



class Reflexive (K : KripkeFrame α) extends Std.Refl (α := K.points) (K.Rel ↑· ↑·)
@[grind .]
lemma refl [hRefl : K.Reflexive] : ∀ x : K.points, K.Rel ↑x ↑x := hRefl.refl


class Transitive (K : KripkeFrame α) extends IsTrans (α := K.points) (K.Rel ↑· ↑·)
@[trans]
lemma trans [hTrans : K.Transitive] : ∀ x y z : K.points, K.Rel ↑x ↑y → K.Rel ↑y ↑z → K.Rel ↑x ↑z := hTrans.trans


class Preorder (K : KripkeFrame α) extends IsPreorder (α := K.points) (K.Rel ↑· ↑·)


end KripkeFrame

end LO

end
