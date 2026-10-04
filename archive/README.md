# Archived modules

Modules here are not built, not counted, and not citable as checked.

- `R5R4Audit.lean`: archived at the commit that moved it here. It refers to
  `R4bCorrespondence.R4bSourceDomain` and `R4bTargetDomain`, which no module in
  this repository has ever defined (the file's history has a single commit,
  45786a0). CI's tier 3 elaborated it on every push, but every
  workflow step ran without pipefail, so `lake lean … | tee` reported tee's success and its
  failure never failed a run. Found by compiling it directly; the workflow now runs with
  pipefail. Restoring it requires defining those domains.
