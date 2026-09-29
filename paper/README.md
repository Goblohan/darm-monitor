# Paper drafts

One core, two framings.

- `core.md`: the shared results, one section per result, each with its claims,
  its exact theorem citations, and its limit.
- `framing-security.md`: abstract, introduction plan and section order for a
  security venue (S&P, USENIX Security, CCS).
- `framing-fm.md`: the same for a formal-methods venue (CAV, ITP, CPP).

## Conventions

- **Citations.** A theorem is cited as `<Module>.<theorem>` in backticks, where
  `Module` is a file in `GRBS/`. `python3 paper/check_citations.py` fails if any
  cited theorem does not exist, so the paper cannot claim a result the corpus
  does not contain, or cite one that has been renamed.
- **Say what is proved, no more.** A citation supports exactly its statement.
  If prose says more than the theorem, the prose is wrong (the review of E25 and
  E26.6 found exactly this pattern in theorem docstrings).
- **Disclosure.** Results of experiments against a specific third-party defense
  are withheld from this public repository until the relevant disclosure has
  been made. Such passages are marked `[withheld pending disclosure]`.
