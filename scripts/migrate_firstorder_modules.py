#!/usr/bin/env python3
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TARGET = ROOT / "Foundation" / "FirstOrder"

module_line = "module\n"
section_line = "@[expose] public section\n"
end_line = "end\n"

IMPORT_RE = re.compile(r"^\s*(?:public\s+)?import\s+(.*)\s*$")
EXPOSE_SECTION_RE = re.compile(r"^\s*@\[expose\]\s+public\s+section\s*$")
MODULE_RE = re.compile(r"^\s*module\s*$")


def process_file(path: Path) -> bool:
    text = path.read_text(encoding="utf-8")
    lines = text.splitlines(keepends=True)

    # Skip if already migrated (has expose public section)
    if any(EXPOSE_SECTION_RE.match(l) for l in lines):
        return False

    # Collect import lines (in order encountered)
    imports = []
    body_lines = []
    for l in lines:
        m = IMPORT_RE.match(l)
        if m:
            imports.append(m.group(1).strip())
        else:
            body_lines.append(l)

    # Determine if file already has 'module' as first non-empty line
    has_module = False
    for l in body_lines:
        if l.strip() == "":
            continue
        has_module = MODULE_RE.match(l) is not None
        break

    out = []
    # Always place module at very top for consistency
    if not has_module:
        out.append(module_line)
    else:
        # Ensure 'module' is the very first line
        # Move any leading content before existing module below after section
        # Find and remove the first occurrence of module
        new_body = []
        module_emitted = False
        for l in body_lines:
            if not module_emitted and MODULE_RE.match(l):
                out.append(module_line)
                module_emitted = True
            else:
                new_body.append(l)
        body_lines = new_body

    # Emit imports as 'public import ...'
    for imp in imports:
        out.append(f"public import {imp}\n")

    # Add a blank line before section
    if len(imports) > 0:
        out.append("\n")

    # Emit section header
    out.append(section_line)

    # Emit body (without original imports and with module normalized)
    out.extend(body_lines)

    # Ensure trailing end
    # If last non-empty line already 'end', don't duplicate
    last_nonempty = None
    for l in reversed(out):
        if l.strip() != "":
            last_nonempty = l.strip()
            break
    if last_nonempty != "end":
        if not out or out[-1].endswith("\n"):
            out.append(end_line)
        else:
            out.append("\n" + end_line)

    new_text = "".join(out)
    if new_text != text:
        path.write_text(new_text, encoding="utf-8")
        return True
    return False


def main():
    changed = 0
    total = 0
    for p in TARGET.rglob("*.lean"):
        total += 1
        try:
            if process_file(p):
                changed += 1
                print(f"migrated: {p.relative_to(ROOT)}")
            else:
                print(f"skipped:  {p.relative_to(ROOT)}")
        except Exception as e:
            print(f"error:    {p.relative_to(ROOT)}: {e}")
    print(f"Done. Changed {changed} of {total} files.")


if __name__ == "__main__":
    main()
