# DARM releases

Release identities published by PerceptraAI Lab. Check any copy against these SHA-256 digests. Qualification evidence is signed with the key in [SIGNING-KEY.md](SIGNING-KEY.md).

## darmd 0.5.3 (25 October 2026)

| Item | SHA-256 |
| --- | --- |
| `release-manifest.json` | `73b1d5339af1a6a7a4265c34081428b0fe3e318ca68c438570cc795063af10e6` |
| `darmd` binary | `a16e360e77a59a10f473d53a15cd1b059ea66ab2e2b73ea364bfa48dc4d19c21` |
| Gate 7 suite 0.3.2 (55 cases) | `b7da0796f782218e88b22745eb2c6f80e6d24c97c68c4ac2854de67e1d936910` |
| Release archive `darm-v053-final.tgz` | `e927721534d7cc64a616efef09a9eecfaead250bed39f3f5028895e28c013bf1` |

**Qualification** (`tools/run_qualification.sh`, disposable Hyper-V host, Ubuntu 24.04.5, kernel 6.8.0-147-generic, BPF-LSM active). Userspace: 49 PASS, 3 OUT_OF_SCOPE, 3 FAIL; qualified for STRICT_PROFILE and C8 (bundle `4da229371def438ead9bcfdc6b87671b0b2d9f7671c46cb23a27073c06ce9be6`). Kernel floor: 52 PASS, 3 OUT_OF_SCOPE, 0 FAIL; qualified for STRICT_KERNEL_RELATIVE and C8 (bundle `65ccbf9b3d8df6ad9441fdc30dfc348c63ec0925cd4a74b777704076b44f1236`). Both verifiers reported CURRENT after a fresh rerun. All four bundles (both assessments and both reproductions) are signed by key `713f88cb3c2cfe50`, after the unsigned on-host run. Each bundle's release binding records the manifest digest above.

**Changes from 0.5.2.** After an effect is dispatched, the witness records an abort as ABORTED only when the executor proves no effect happened; otherwise it records UNKNOWN and suspends (finding F; formalized in `GRBS/B10AbortAfterDispatch.lean` and `GRBS/B10bAbortEvidence.lean`). The suite adds `write_inplace_race`, `abort_after_effect_latches` and `witness_cross_role_ops`, and the runner and verifier excuse only outcomes each case declares.

**Scope and limits.** Isolated case fixtures launch the installed bytes, not a live governed root. Not established: a reproducible build (source-to-binary provenance is unavailable), external review, production lifecycle, migration from 0.5.2. Corrections ship in the release's `qualification/v053/ERRATA.md`.

## darmd 0.5.2 (19 October 2026)

| Item | SHA-256 |
| --- | --- |
| `release-manifest.json` | `12384f6c17db76fa99d08cd4d29068bc6bd04949e2cd791e3f8278cb954d74ee` |
| `darmd` binary | `94991df1168366dea991228105935c28814bd6263ac318d73f91c24baf9517bb` |
| Signed qualification evidence archive | `889eb58a0ad4077b4b1eb40d58b5f69ff0e36401ebc870f5afc8eec5c5ba55c9` |

Signed qualification accepted on 19 October 2026 (kernel floor: 50 PASS, 2 OUT_OF_SCOPE, 0 FAIL, reproduced), signed by key `713f88cb3c2cfe50`. Known defect: an abort after dispatch can record ABORTED over an effect that happened (finding F), fixed in 0.5.3.
