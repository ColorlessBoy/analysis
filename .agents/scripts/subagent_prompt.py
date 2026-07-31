#!/usr/bin/env python3
"""Generate a minimal prompt for the lean-prover subagent."""
import sys, os, re

def extract_theorem(filepath, line_num, context=30):
    """Extract the theorem statement containing the given line."""
    with open(filepath) as f:
        lines = f.readlines()
    # Search backwards for theorem declaration
    start = max(0, line_num - 1 - context)
    decl_start = 0
    for i in range(line_num - 1, start - 1, -1):
        if re.match(r'^\s*(theorem|lemma|example|private\s+lemma|private\s+theorem)', lines[i]):
            decl_start = i
            break
    # Extract the declaration from decl_start until the ':= by' line (or the sorry line)
    decl_lines = []
    for i in range(decl_start, len(lines)):
        decl_lines.append(lines[i])
        if re.search(r':=\s*by\s*$', lines[i]) or re.search(r'\bsorry\b', lines[i]):
            break
    return ''.join(decl_lines), decl_start

def extract_imports(filepath):
    """Extract import lines from the file."""
    imports = []
    with open(filepath) as f:
        for line in f:
            if line.startswith('import '):
                imports.append(line.strip())
            elif line.strip() == '':
                continue
            else:
                break
    return imports

def main():
    if len(sys.argv) < 3:
        print("Usage: subagent_prompt.py <file> <line> [--theorem N] [--deps F]")
        sys.exit(1)
    filepath = os.path.abspath(sys.argv[1])
    line_num = int(sys.argv[2])
    imports = extract_imports(filepath)
    theorem, decl_start = extract_theorem(filepath, line_num)
    filename = os.path.basename(filepath).replace('.lean', '')
    temp_name = f"_temp_{filename}_line{line_num}"

    prompt = f"""Prove the following Lean theorem. It is in a temp file.

## Temp file setup

Create `{temp_name}.lean` in the project root with this content:

```lean
{chr(10).join(imports)}

{theorem}
```

## Environment

- Use `lean_local_search` before guessing any lemma name
- Use `lean_goal` with `timeout_s=30` to check proof state
- Use `lean_diagnostic_messages` with `timeout_s=30` to check errors
- Use `lean_multi_attempt` to test tactics without editing

## Session tracking

Start with:
```bash
python3 .agents/scripts/experience.py session start "{filename}_line{line_num}" "{filepath}" "goal"
```

After each successful/failed attempt:
```bash
python3 .agents/scripts/experience.py session attempt <id> "<what you tried>" <errors_before> <errors_after> "..."
```

End with:
```bash
python3 .agents/scripts/experience.py session end <id> success|fail "notes"
```

## Rules

- Edit ONLY the proof body (after `:= by`). Never change the statement.
- 1-3 lines per edit, then check diagnostics.
- If proof needs >30 lines, write helper lemmas first.
- Return PROOF_BLOCK when done.
"""
    print(prompt)

if __name__ == "__main__":
    main()
