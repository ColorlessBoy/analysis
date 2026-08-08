# PM Skills (Product Manager Skills)

Source: https://github.com/deanpeters/Product-Manager-Skills (v0.83, 70 skills total)
Selected 35 skills most relevant to this project's product work + 5 command workflows.

## License

CC BY-NC-SA 4.0 — see `LICENSE-PM-SKILLS`. Non-commercial, share-alike.
Use in this project's day-to-day workflow (including a for-profit company) is
explicitly permitted by the author. Do NOT repackage or sell the skills
themselves, or commercialize content derived directly from them, without the
author's written permission.

## What was installed

- `.opencode/skills/` — 35 skills (each `<name>/SKILL.md` + templates/examples)
- `.opencode/command/` — 5 workflows: `discover`, `strategy`, `plan-roadmap`,
  `prioritize`, `write-prd` (frontmatter cleaned to opencode-compatible fields)

## Full catalog

Clone upstream for the remaining 35 (AI PM, intel suite, workshops, career):

```bash
git clone --depth 1 https://github.com/deanpeters/Product-Manager-Skills /tmp/pm-skills
ls /tmp/pm-skills/skills/        # full list
ls /tmp/pm-skills/catalog/       # index with descriptions
```

## Update

```bash
cd /tmp/pm-skills && git pull
# then re-copy updated skill dirs into .opencode/skills/
```
