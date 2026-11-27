# List available recipes
default:
    @just --list

cache:
    lake exe cache get
    LAKE_CONFIG=lake-cache.toml lake cache get \
      --service ffl \
      --max-revs=100 \
      --repo FormalizedFormalLogic/Foundation \
      --package Foundation \
    || echo "Foundation cache missing"

build:
    lake build Foundation --wfail

# Rebuild and replay the project through the kernel in a sandbox, rejecting `sorry` and any axiom
# outside `propext`, `Classical.choice`, `Quot.sound`.
kernel-check:
    lake check

# Export the project with its dependencies for the external kernels below.
kernel-export:
    lake env leanexport Foundation > .lake/export.ndjson

# Replay the export through lean4lean, a kernel written independently of Lean's own.
lean4lean: kernel-export
    lake env lean4lean --import .lake/export.ndjson

# Replay the export through `leanchecker-paranoid`. Needs about 15 GB of memory.
leanchecker-paranoid: kernel-export
    lake env leanchecker-paranoid --silent --from-export .lake/export.ndjson

mk-all:
    lake exe mk_all --module --lib Foundation

check: build kernel-check
    lake exe mk_all --module --lib Foundation --check

format-references:
    bibtool -F -r .bibtoolrsc -i ./references.bib -o references.bib
    sed -i '1{/^$/d}' references.bib

shake:
    lake shake --keep-public --fix

zoo:
    mkdir -p pages/zoo
    lake build Foundation zoo_arithmetic zoo_provability_logic
    lake exe zoo_arithmetic Zoo/arithmetic.json
    lake exe zoo_provability_logic Zoo/provability_logic.json
    typst compile Zoo/arithmetic.typ pages/zoo/arithmetic.png
    typst compile Zoo/arithmetic.typ pages/zoo/arithmetic.pdf
    typst compile Zoo/provability_logic.typ pages/zoo/provability_logic.png
    typst compile Zoo/provability_logic.typ pages/zoo/provability_logic.pdf

import-graph:
    lake build Foundation
    lake exe graph --to Foundation import_graph.png import_graph.pdf import_graph.html

docs:
    rm -rf .lake/build/doc
    rm -f .lake/build/doc-data/references.json .lake/build/doc-data/*.docs_built
    lake build Foundation:docs

cloc:
    cloc --include-lang=Lean Foundation/
