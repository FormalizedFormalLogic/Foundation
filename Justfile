# List available recipes
default:
    @just --list

format-references:
    bibtool -F -r .bibtoolrsc -i ./references.bib -o references.bib
    sed -i '1{/^$/d}' references.bib

cache:
    lake exe cache get
    LAKE_CONFIG=lake-cache.toml lake cache get \
      --service ffl \
      --max-revs=100 \
      --repo FormalizedFormalLogic/Foundation \
      --package Foundation \
    || echo "Foundation cache missing"

import-graph:
    lake exe graph --to Foundation import_graph.png import_graph.pdf import_graph.html

zoo:
    lake build zoo_arithmetic
    lake exe zoo_arithmetic Zoo/arithmetic.json
    mkdir -p pages/zoo
    typst compile Zoo/arithmetic.typ pages/zoo/arithmetic.png
    typst compile Zoo/arithmetic.typ pages/zoo/arithmetic.pdf

mk-all:
    lake exe mk_all --module --lib Foundation

shake:
    lake shake --keep-public --fix

forgive:
    lake exe forgive Foundation

docs:
    rm -rf .lake/build/doc
    rm -f .lake/build/doc-data/references.json .lake/build/doc-data/*.docs_built
    lake build Foundation:docs

cloc:
    cloc --include-lang=Lean Foundation/
