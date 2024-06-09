# Notation

Quantification of formulae are  defined using de Bruijn index, but we can write terms and formulae by usual binder notation using macro.

variables `x y z` is just an example and can take any number of `ident`s.
`e` is an expression of term/formula.

## Binder Notation

Binder notation of term takes either form:
- Term: `‘x y z | e’`, Formula: `“x y z | e”`
  - `x y z` is the symbol for the bound variables, `k:num`-variables denotes the terms in `Semiterm L ξ (n + $k)`/`Semiformula L ξ (n + $k)`. (`n` can be variable)
- Term: `‘e’`, Formula: `“e”`
  - An abbreviation of `‘ | e’`/`“ | e”`


## Expression of term/formula

