import Foundation.Vorspiel.Vorspiel

namespace LO

/-- Coding objects into syntactic objects (e.g. natural numbers, first-order terms) -/
class GoedelQuote (α β : Sort*) where
  quote : α → β

notation:max "⌜" x "⌝" => GoedelQuote.quote x

/-- Coding objects into semantic objects (e.g. individuals of a model of a theory) -/
class StarQuote (α β : Sort*) where
  quote : α → β

prefix:max "✶" => StarQuote.quote

end LO
