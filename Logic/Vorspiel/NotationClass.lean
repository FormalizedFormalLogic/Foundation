import Logic.Vorspiel.Vorspiel

namespace LO

class GoedelQuote (α β : Sort*) where
  quote : α → β

notation:max "⌜" x "⌝" => GoedelQuote.quote x

end LO
