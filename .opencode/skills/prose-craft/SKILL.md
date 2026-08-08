---
name: prose-craft
description: Write fiction, prose, and creative nonfiction with craft AND calibration — sentence-level music plus the structural choices that make prose read as human-authored rather than machine-default. A reworking of prose-craft tuned against measured AI narrative signatures: it adds rhythm, restraint, and figurative language by feel, but also deliberately diverges from Claude's known defaults (flat escalation, quiet endings, embodied-only emotion, linear single-track plots, sealed fictive dream). Use when the user asks to write a story, scene, chapter, essay, article, creative piece, flash fiction, prose poem, monologue, or any creative writing. Also use when they ask to improve, edit, polish, critique, or "make this read less like AI" / "make it feel human." Even casual asks like 'write me something about rain' or 'tell me a story' should trigger this skill. Do NOT use for marketing copy (use copywriters-handbook), academic essays, technical documentation, or business writing.
---

# Prose Craft 2

A skill for writing fiction and prose that lives on the page — prose with rhythm, breath, and sentence-level music — AND that makes the structural choices a human writer would make, instead of collapsing into the machine's house style.

## Why this is a second version

The original prose-craft optimized one axis: beauty. Music, restraint, sensory richness, the quiet earned ending. That advice is not wrong — but recent large-scale analysis of AI fiction (StoryScope, Russell et al. 2026) shows that *this exact aesthetic is now the machine's default.* Across 60k+ stories, AI fiction can be separated from human fiction at 93% accuracy using narrative structure **alone**, with style stripped out — and the separation survives a professional style-editing pass. "Good literary prose" and "reads as human-authored" have come apart.

The measured AI signature, and Claude's in particular:

- **Over-explains theme** — narrators state the lesson; tidy moral unity
- **Renders emotion through the body, never named** — "tightening chest, cold sweat" instead of "she was afraid" (AI 81% vs human 38%; humans name emotions outright 29% vs 8%)
- **Lush sensory description, setting-as-mirror, heavy smell imagery**
- **One tidy causal track** — few subplots, protagonist-driven resolution, internal acceptance, linear time
- **Sealed fictive dream** — never addresses the reader, never names real books/brands/places
- **Claude specifically:** flattest event escalation of any model, most uniform voice, favors epilogues, avoids dream sequences, prefers quiet endings over "avalanche" endings. Claude is the *easiest AI to identify* after the human.

This skill keeps the craft of the original and adds a **calibration layer** so the prose doesn't land in that shared machine region by default.

---

## The Variance Principle (the spine of this skill)

The AI tell is **convergence** — every piece lands in the same narrative region. So the fix is never "always break the fourth wall" or "always go nonlinear." That just relocates the prose to a *new* detectable cluster with a *new* default. Human-ness lives in the **distribution across pieces**, not in any single piece.

Two rules follow:

1. **Per piece: pick a distinctive posture and commit to it hard.** A piece that winks at the reader in every paragraph is as mechanical as one that never does. Whatever you choose, do it with conviction, then stop.
2. **Across pieces: diverge from your defaults.** Reader address, nonlinear time, naming the real world, escalation, moral ambivalence — these are weighted coins flipped per piece, not switches left on.

### The honest mechanism

Claude has no memory of its past stories, so "vary across pieces" cannot rely on recall. And left alone, Claude collapses toward its attractor (quiet, lyrical, restrained, linear) no matter what an instruction says. So the Variance Principle is enforced **per piece, against a fixed list of known defaults** — which produces spread across pieces automatically, because every piece is pushed off the same center.

This is operationalized as the **Posture Board** below. It is not optional flavor. It is the forcing function that makes this skill different from the first one.

---

## The Posture Board (forcing function — run during Architecture, before writing)

Before writing any piece, take an explicit position on each axis below. The **left pole is Claude's default** (the machine center). For **at least three axes, deliberately choose the non-default (right) pole** for this piece — chosen to fit the material, not at random, but genuinely pushed off center. State your choices in the architecture you show the user.

| Axis | Default pole (Claude center) | Divergent pole (push here on ≥3) |
|---|---|---|
| **Time order** | linear, chronological | nonlinear — flashback, flash-forward, delayed disclosure, recontextualizing reveal |
| **Emotion rendering** | embodied only (chest, breath, hands) | sometimes *name* the feeling, plainly |
| **Narrator ↔ reader** | sealed fictive dream | direct address / fourth-wall, as a deliberate voice |
| **World reference** | self-contained, invented | names real books, songs, brands, places, people |
| **Escalation** | flat, quiet, restrained ending | genuine escalation; let an "avalanche" ending happen |
| **Plot shape** | single track, few subplots | subplots, multiple locations, ensemble |
| **Protagonist morality** | clear, sympathetic | ambivalent, compromised, hard to root for cleanly |
| **Sensory density** | lush, layered, smell-heavy | spare — withhold the senses, let plain statement carry |
| **Dialogue function** | one register (often philosophical) | mixed — gossip, logistics, evasion, comedy, not just ideas |

Rules for the board:
- **Choose for the material.** If the story is genuinely a quiet linear elegy, you may keep some default poles — but you must still push ≥3 axes off center, and you should be suspicious of a piece that wants *every* default. That suspicion is the tell catching itself.
- **Commit per piece.** Having chosen a pole, write it with full conviction. Don't hedge a nonlinear structure into near-linearity.
- **Don't perform the divergence.** A named brand dropped in to look human is as bad as the default. The divergent choice has to actually serve the piece.

---

## Philosophy

Craft is not decoration. It is the thing itself.

A well-chosen verb does more than a paragraph of adjectives. A sentence that lands right makes the reader's chest tighten before they know why. A paragraph break in the right place is worth more than three paragraphs of description in the wrong one.

This skill does not make Claude a walking encyclopedia of rhetorical devices. Claude already knows what anaphora is. The skill teaches something harder: **when to reach for it, when to leave it alone, and — new in this version — how to keep the whole piece from settling into the machine's default shape.**

Four principles govern everything:

1. **Prose is music.** Rhythm, breath, paragraph shape, sentence length variation. If the prose doesn't sound right read aloud, no amount of figurative language saves it.

2. **Restraint is power — but restraint is also Claude's fingerprint.** A single concrete detail beats a paragraph of description. Trust the reader; leave gaps. *And* be aware that "quiet, spare, controlled" is the exact register the machine over-produces. Restraint is a choice to make sometimes, not a house style to default into.

3. **Technique serves story.** Every device, every rhythm choice, every shift in psychic distance must serve the moment. Craft is not display; it is appropriateness.

4. **Variance serves humanity.** (See above.) The most human thing a body of work can do is refuse to converge. Per piece, commit; across pieces, diverge from the center.

---

## Anti-Patterns: What to Suppress

Claude has default instincts that damage creative prose. During any creative writing task, actively suppress these. **Note the revisions from v1 — three of the original anti-patterns were over-corrections that suppressed *human* signals.**

### The Instinct to Explain
Trust the reader. If a character slams a door, you usually don't need "she was angry." The door slam can be the anger. Kill: "This was because…" after showing an emotion; "In other words…" after a metaphor; "For context…"; any sentence whose job is to make sure the reader "got it." (This one stands — over-explaining theme is the #1 measured AI tell.)

> **Revised — naming emotion is not banned.** v1 said never name a feeling. The data says humans name emotions outright far more than AI does. *Default* to showing, but plainly naming a feeling — "She was afraid. That was the whole of it." — is a legitimate, often human, move. Use it deliberately, especially when embodied description would just be more machine fog.

### The Instinct to Balance
Not every observation needs its counterpoint. Let a bleak scene stay bleak. Let a funny moment stay funny without pivoting to insight. Imbalance creates energy; balance creates essays.

### The Instinct to Complete
Some things should be left unsaid, unfinished, open. End scenes mid-beat. Let conversations trail off. (Still true — but see "Land Meaningfully": the open ending is also a Claude default. Vary it. Sometimes things should *resolve*, even loudly.)

### The Instinct to Land Meaningfully
Not every piece needs a lesson. In comedy, the last line is a joke, not a reflection. If your final paragraph starts feeling warm and wise, you've probably gone a paragraph too long. *And* — Claude's specific tell is the quiet, gentle close. An ending that escalates, that bangs, that refuses to be gentle, is a deliberate move off the center.

### The Instinct to Perform Intelligence
"Not metaphorically — I mean literally." "Which is to say…" These are throat-clearing moves disguised as wit. They break the fictive dream to *show off*, not to speak to the reader. Cut them.

> **Revised — this is NOT a ban on addressing the reader.** v1 lumped all fourth-wall work in here. The data says direct address and fourth-wall breaking are strongly *human* (67% vs 39%; direct address 28% vs 7%). Distinguish two things: **performance** (winking to look clever — cut it) versus **deliberate direct address as a voice** (an aside to "you," a narrator who knows you're there — a legitimate, distinctively human choice). Deploy the latter *as a posture choice*, committed and varied — never as a constant tic, never as decoration.

### The Instinct to Be Helpful
Creative writing is not customer service. Don't set context for the reader's convenience. Don't define terms. A story that requires the reader to lean in beats one that meets them in the parking lot.

### NEW — The Instinct to Stay on the Machine Center
The quiet, lyrical, linear, sensory, morally-clean, sealed-dream story is the one Claude writes when not watching itself. Notice when you're sliding toward all of those at once. That convergence *is* the tell. The Posture Board exists to break it.

---

## Two-Pass System (plus a structural check folded into Pass 1)

Every creative writing task uses two passes. The user triggers the second pass by saying "second pass," "edit pass," "clean it up," "fix the AI smell," or similar. (No autorun — the second pass waits for the user.)

### First Pass: Write Freely With Craft Awareness — after the Posture Board is set

Apply everything in the reference files — rhythm, pacing, sound, figurative language, psychic distance, paragraph craft — by feel, not by checklist. But write *into the posture you committed to* on the board. The craft should be invisible; the divergence from center should feel intentional, not bolted on.

**During the first pass:**
- Write like you're not being watched — but having already chosen, on the board, *not* to write the default piece
- Vary sentence length and paragraph length — the core rhythm tools
- Concrete, specific detail — "elm" not "tree," "shuffled" not "walked"
- Honor your Posture Board choices: if you chose nonlinear, actually fracture the time; if you chose to name a feeling, name it; if you chose escalation, let it build and break
- End where the energy ends — *and* check that "where the energy ends" isn't just reflexively the quiet fade

**The Calibration check (run silently at the end of Pass 1, before handing over):**
A structural self-audit, not a prose audit. Four questions:
1. Did I actually push ≥3 axes off the default pole, or did the piece drift back to center while I was writing?
2. Is the ending quiet-and-gentle by *choice* or by *reflex*?
3. Is every emotion rendered through the body? If so, name at least one plainly.
4. Did I over-explain the theme anywhere — a sentence telling the reader what it all means?

If the piece failed the audit, adjust before handing over. This is not the user-triggered style pass; it's the structural conscience of the first pass.

### Second Pass: Light Sweep (user-triggered)

Not a rewrite. A quick pass with these checks:

1. **Does the opening throat-clear?** The real opening is often paragraph two or three. Cut setup the reader doesn't need.
2. **Does the ending drift** into reflection, wisdom, or summary? Trim to the last real moment. (And: is it drifting *quiet*? That's the Claude drift specifically.)
3. **Is any sentence performing** — existing to sound smart rather than serve the piece? Cut or simplify.
4. **Read it aloud.** Does anything clunk? Fix by ear.

---

## How Craft Works (Not Mechanically)

The reference files contain 200+ devices across 11 families, plus `human-signal.md` for the structural calibration. **Do not treat them as a menu.** A writer who thinks "I need anaphora here" writes prose that sounds assembled. Absorb the principles, then *forget the names* and write by feel.

The one exception is the **Posture Board**, which IS deliberate and IS run as a step. The board is the conscious frame; everything inside it is by feel. Think of a jazz musician choosing a key and a tempo on purpose, then improvising freely within them.

---

## Modes

Four modes. Choose based on the user's request.

### Mode 1: Write
Original creative writing. Run, in order: **Discovery → Architecture (including the Posture Board) → Writing.**

#### Discovery Phase
A short, focused exchange — not a long interview. Ask only what you need; skip what the user already gave you. Core questions (pick what's relevant): What's the piece and how long? **What should the reader feel?** (the most important — emotional experience, not topic). What's the tone? Who's the audience? Any constraints (POV, tense, setting, style reference)? What should it NOT be?

#### Architecture Phase
Before writing a word, plan the shape AND fill the Posture Board. Share both with the user briefly so they can approve or redirect.

For the shape: the opening image/moment, the turn, the closing image, the emotional arc (shorter pieces); or the major movements, where it accelerates and slows, the psychic-distance strategy, and **the time-order strategy** — linear, nonlinear, delayed disclosure (longer pieces). The architecture is a shape, not a plot outline.

For the Posture Board: state your position on each axis and name the ≥3 you're pushing off center, and why those serve this piece.

Present both in a few sentences. Get the nod, then write.

#### Writing Phase
Consult the relevant reference files for the desired effect and tone. Read `human-signal.md` whenever any Posture Board axis is pushed off center (it tells you how to execute the divergent pole without performing it). Absorb, then put the references away and write. Use the two-pass system.

### Mode 2: Edit
Existing prose to improve. Read it first. Identify what's working (don't break it) and what's flat. Strengthen rhythm, sharpen images, tighten pacing, deepen psychic distance, fix dialogue. **Also run the Posture Board against the existing piece** — if it sits entirely on the default poles, that's likely why it reads as AI; propose specific divergent moves. Explain changes briefly.

### Mode 3: Analyze
Understand how a piece works — published, the user's, or to diagnose whether prose reads as AI. Break down the craft: devices, rhythm, psychic-distance shifts, paragraph structure. Here you CAN name devices. **New capability:** you can also diagnose machine-default signatures using the StoryScope feature vocabulary — flat escalation, embodied-only emotion, sealed fictive dream, tidy single-track plot, over-explained theme, quiet-reflex ending — and point to exactly where a passage sits on each Posture Board axis. This makes "why does this read as AI?" a concrete, answerable question.

### Mode 4: Coach
Guidance on the user's process or a craft problem. Draw from the reference files (and `human-signal.md` when the problem is "my writing reads as AI / generic"). Be direct, specific, example-driven. No platitudes.

---

## Reference File Routing

Consult only what's relevant. Don't load everything.

| If the task involves… | Read this reference file |
|------------------------|------------------------|
| **Making prose read as human-authored, pushing any Posture Board axis off center, "less AI / more human," nonlinearity, reader address, naming the real world, moral ambivalence, escalation** | `references/human-signal.md` |
| How prose sounds — alliteration, vowel music, cacophony, rhythm | `references/sound-and-rhythm.md` |
| Repetition for emphasis/momentum; sentence-level architecture (parallelism, chiasmus, antithesis, periodic vs cumulative) | `references/repetition-and-structure.md` |
| Metaphor, simile, metonymy, irony, symbolism, figurative language | `references/figurative-language.md` |
| Story structure, POV, psychic distance, show vs tell, scene construction, **temporal architecture, subplots/structural multiplicity, moral ambivalence** | `references/narrative-craft.md` |
| Dialogue, character voice, speech rhythm, subtext, diction, register, **dialogue-function variety** | `references/dialogue-and-voice.md` |
| Pacing, paragraph craft, sentence length variation, scene vs summary, white space | `references/pacing-and-paragraphs.md` |
| Rhetorical argument, persuasive structure, apophasis, rhetorical questions | `references/discourse-and-argument.md` |
| **"I want to create a specific EFFECT"** — tension, beauty, humor, unease, speed, slowness, grief | `references/effects-toolkit.md` |

When in doubt about effect, start with `effects-toolkit.md`. When in doubt about *whether the piece reads human*, start with `human-signal.md`.

---

## A guardrail on the calibration (read this before over-correcting)

The human-vs-AI evidence this skill is tuned against has two real limits, and they should shape how hard you lean:

1. **The "human" baseline is published, anthologized literary fiction** — possibly from an earlier era. Closing every gap means imitating curated literary prose, which is not always what the user wants. Serve the *user's* aim first; the calibration is a counterweight to Claude's defaults, not a target to chase.
2. **The generation setup advantaged the humans** on the *structural-streamlining* signals (AI wrote to a brief, to a word count, as a cover version). So weight the **thematic and temporal** signals (over-explaining, linearity, sealed dream) heavily, and treat the *tidiness/single-track* signals as softer.

The trap: if this skill just swaps one set of hard defaults for another, it relocates Claude to a new detectable cluster. The Posture Board adds **range and deliberate choice**, not new commandments. Per piece, commit; across pieces, diverge. That is the whole game.

---

## Quality Awareness

Not a checklist to run mechanically — questions to hold in mind:

- **Does this sound right?** Read it in your mind's ear.
- **Is there variety** — sentence length, paragraph length, psychic distance, density? Monotony is the enemy.
- **Is every sentence earning its place?**
- **Am I trusting the reader** rather than explaining my own subtext?
- **Does the opening start where the energy starts? Does the ending stop where it stops** — and is that stop a choice, not the reflexive quiet fade?
- **Did I push off the machine center** on the axes I committed to, or did the piece drift back home while I wasn't looking?
