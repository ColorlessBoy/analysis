#!/usr/bin/env python3
"""Generate a minimal dispatch prompt for the notes-writer subagent.

Usage:
  notes_prompt.py <type> <section-title> <target-file> [--sources F1 F2 ...] [--book T] [--no-loop]

Example:
  notes_prompt.py 1.1.1 "Elementary measure" notes/MeasureTheory/01-1.1.1-初等测度.md \
      --sources analysis/MeasureTheory/Section_1_1_1.lean analysis/MeasureTheory/Section_1_1_2.lean

The prompt stays SHORT (the deep skill files carry the standard). Keep <2600 chars.
--no-loop skips the teacher-student revision loop (use for first-pass drafts).
"""
import sys, os

def main():
    if len(sys.argv) < 4:
        print(__doc__)
        sys.exit(1)
    stype = sys.argv[1]
    title = sys.argv[2]
    target = os.path.abspath(sys.argv[3])
    args = sys.argv[4:]
    sources = []
    book = None
    loop = True
    while args:
        if args[0] == '--sources':
            args = args[1:]
            while args and not args[0].startswith('--'):
                sources.append(os.path.abspath(args[0])); args = args[1:]
        elif args[0] == '--book':
            book = args[1]; args = args[2:]
        elif args[0] == '--no-loop':
            loop = False; args = args[1:]
        else:
            args = args[1:]
    if not sources:
        print("ERROR: need --sources with at least one Lean file", file=sys.stderr)
        sys.exit(1)

    srcs = "\n".join(f"  - {s}" for s in sources)
    bookline = f"\nBOOK TEXT: {book}" if book else ""
    loopline = "\nLOOP: yes (run the teacher-student loop after self-check)" if loop else "\nLOOP: no"

    prompt = f"""Write the deep-math-notes section note for:

SECTION: {stype} — {title}
TARGET FILE: {target}  (create dirs as needed; write the FULL markdown there)

READ FIRST (in this order):
- .opencode/skills/deep-math-notes/SKILL.md     (the standard; follow §2 framework, §3 rules, §4 self-check)
- .opencode/skills/classics-crossref/SKILL.md   (add the 教材对照 block)

SOURCES (read before writing; copy REAL theorem names + grep exact :line numbers):
{srcs}{bookline}{loopline}

Then: write the note; verify every analysis/*.lean:NNN with a second grep and recompute ≥2 example numbers; then report per §5 of the skill (one-line checks + DONE/NEEDS_HELP, no body pasted).

Rules: no AI-summary prose; ≥1200 chars; ≥2 worked examples; ≥1 counterexample; every theorem needs a proof skeleton + Lean ref; include 教材对照 and FAQ blocks."""
    print(prompt)
    print(f"# chars: {len(prompt)}", file=sys.stderr)

if __name__ == "__main__":
    main()