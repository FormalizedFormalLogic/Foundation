import Foundation.Vorspiel.Vorspiel

class Exp (α : Type*) where
  exp : α → α

class Smash (α : Type*) where
  smash : α → α → α

infix:80 " ⨳ " => Smash.smash

class Length (α : Type*) where
  length : α → α

notation "‖" x "‖" => Length.length x

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
