import Foundation

import VersoBlog
import VersoManual
import Book.Bibliography

set_option linter.tacticAnalysis false

open Verso Doc Elab in
@[code_block_expander math]
def Verso.Genre.Manual.math : CodeBlockExpander
  | _args, str => do
    return #[(← `(Doc.Block.para #[Doc.Inline.math Doc.MathMode.display s!"{$str}"]))]
