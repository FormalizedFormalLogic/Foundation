# List available recipes
default:
    @just --list

# Fetch prebuilt oleans of Mathlib and of Foundation itself
cache:
    lake exe cache get
    LAKE_CONFIG=lake-cache.toml lake cache get \
      --service ffl \
      --max-revs=100 \
      --repo FormalizedFormalLogic/Foundation \
      --package Foundation \
    || echo "Foundation cache missing"

# Build Foundation, failing on any warning as CI does
build:
    lake build Foundation --wfail

# Audit sorry-freeness and the axiom allowlist
forgive:
    lake exe forgive Foundation

# Regenerate `Foundation.lean` to import every module
mk-all:
    lake exe mk_all --module --lib Foundation

# Run the checks CI runs on every pull request
check: build forgive
    lake exe mk_all --module --lib Foundation --check

# Format `references.bib`
format-references:
    bibtool -F -r .bibtoolrsc -i ./references.bib -o references.bib
    sed -i '1{/^$/d}' references.bib

# Remove unused imports across the whole repository (rewrites files in place)
shake:
    lake shake --keep-public --fix

# Draw the zoo diagrams into `pages/zoo` (requires typst)
zoo:
    lake build Foundation zoo_arithmetic zoo_provability_logic
    lake exe zoo_arithmetic Zoo/arithmetic.json
    lake exe zoo_provability_logic Zoo/provability_logic.json
    mkdir -p pages/zoo
    typst compile Zoo/arithmetic.typ pages/zoo/arithmetic.png
    typst compile Zoo/arithmetic.typ pages/zoo/arithmetic.pdf
    typst compile Zoo/provability_logic.typ pages/zoo/provability_logic.png
    typst compile Zoo/provability_logic.typ pages/zoo/provability_logic.pdf

# Draw the import graph of Foundation (requires graphviz)
import-graph:
    lake build Foundation
    lake exe graph --to Foundation import_graph.png import_graph.pdf import_graph.html

# Generate the API documentation into `.lake/build/doc`
docs:
    rm -rf .lake/build/doc
    rm -f .lake/build/doc-data/references.json .lake/build/doc-data/*.docs_built
    lake build Foundation:docs

# Count the lines of Lean code
cloc:
    cloc --include-lang=Lean Foundation/
