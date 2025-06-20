import VersoBlog
import VersoManual

import Foundation.FirstOrder.Incompleteness.First

open Verso.Genre
open Verso.Genre.Manual

set_option verso.docstring.allowMissing true

#doc (Manual) "Gödel's First Incompleteness Theorem" =>
%%%
tag := "goedel-1"
%%%

A deduction system $``\mathcal{S}`` is _complete_ iff it can prove or refute every sentence $``\sigma``.
Otherwise, $``\mathcal{S}`` is _incomplete_.

{docstring LO.R0.goedel_first_incompleteness}
