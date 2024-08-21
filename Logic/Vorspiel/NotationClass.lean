import Logic.Vorspiel.Vorspiel

namespace LO

/-- Coding object into syntactic object (natural numbers, first-order term, etc.) -/
class GoedelQuote (α β : Sort*) where
  quote : α → β

notation:max "⌜" x "⌝" => GoedelQuote.quote x

/-- Coding object into semantic object (model of theory) -/
class StarQuote (α β : Sort*) where
  quote : α → β

prefix:max "✶" => StarQuote.quotes

end LO
