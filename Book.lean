import Book.Main
import VersoManual

open Verso.Genre.Manual

def main := manualMain (%doc Book.Main) (config := {
  sourceLink := some "https://github.com/FormalizedFormalLogic/Foundation",
  issueLink := some "https://github.com/FormalizedFormalLogic/Foundation/issues",
})
