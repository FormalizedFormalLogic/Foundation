import VersoBlog
import VersoManual

import Foundation.FirstOrder.ISigma0.Exponential

import Book.Bibliography

open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option verso.docstring.allowMissing true

#doc (Manual) "ISigma0" =>
%%%
tag := "first-order-isigma0"
%%%

# Exponential

The graph of exponential $``\mathrm{Exp}(x, y)`` is definable by $``\Sigma_0``-fomrula,
and its inductive properties are proved in $``\mathsf{I}\Sigma_0``.

{docstring LO.ISigma0.exponential_definable}

{docstring LO.ISigma0.Exponential.exponential_zero_one}

{docstring LO.ISigma0.Exponential.exponential_succ_mul_two}

Other basic functions, such as $``\log x, |x|`` are defined by using exponential.
