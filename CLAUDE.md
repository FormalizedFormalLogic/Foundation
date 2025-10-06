# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Foundation is a Lean 4 project formalizing mathematical logics including propositional logic, first-order logic, modal logic, and provability logic. The project establishes completeness theorems, incompleteness results, and logical relationships between different systems.

## Build System and Development Commands

### Essential Commands

**Building the project:**
```bash
lake build
```

**Generating documentation:**
```bash
lake build doc
```

**Running specific zoo generators:**
```bash
lake exec generate_arith_zoo
lake exec generate_modal_zoo
lake exec generate_propositional_zoo
```

**Building specific targets:**
```bash
lake build Foundation        # Main library
lake build Zoo              # Logic zoo generation
```

### Development Workflow

- Use `lake build` to rebuild after changes - imports may become outdated
- Check `lakefile.toml` for linter configurations and dependencies
- The project uses Lean `4.22.0-rc3` with Mathlib dependency
- Run diagnostic checks with Lean LSP for import and proof issues
