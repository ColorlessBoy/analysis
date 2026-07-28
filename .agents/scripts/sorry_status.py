#!/usr/bin/env python3
"""Find all sorry statements in a Lean file with context."""
import re, sys, os

def find_sorries(filepath):
    with open(filepath) as f:
        lines = f.readlines()
    sorries = []
    for i, line in enumerate(lines, 1):
        if re.search(r'\bsorry\b', line) and not line.strip().startswith('--'):
            # Find the enclosing theorem/lemma/example
            start = max(0, i - 30)
            context = lines[start:i]
            # Look backwards for theorem declaration
            for j in range(len(context) - 1, -1, -1):
                if re.match(r'^\s*(theorem|lemma|example|private)', context[j]):
                    sorries.append({
                        'line': i,
                        'decl_start': start + j + 1,
                        'decl_line': context[j].strip()[:100],
                    })
                    break
            else:
                sorries.append({'line': i, 'decl_start': i, 'decl_line': 'unknown'})
    return sorries

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: sorry_status.py <file.lean>")
        sys.exit(1)
    filepath = sys.argv[1]
    if not os.path.exists(filepath):
        print(f"File not found: {filepath}")
        sys.exit(1)
    sorries = find_sorries(filepath)
    print(f"Found {len(sorries)} sorries in {filepath}:")
    for s in sorries:
        print(f"  Line {s['line']}: {s['decl_line']}")
