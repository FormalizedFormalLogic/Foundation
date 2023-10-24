import Logic.Vorspiel.Vorspiel

namespace String

instance (ι : Type*) [h : IsEmpty ι] : ToString ι  := ⟨h.elim⟩

def subscript : ℕ → String
  | 0 => "₀"
  | 1 => "₁"
  | 2 => "₂"
  | 3 => "₃"
  | 4 => "₄"
  | 5 => "₅"
  | 6 => "₆"
  | 7 => "₇"
  | 8 => "₈"
  | 9 => "₉"
  | _ => ""

def _root_.List.seqStr {α : Type*} (f : α → String) (s : String) : List α → String
  | []      => ""
  | [a]     => f a
  | a :: as => f a ++ s ++ seqStr f s as

end String
