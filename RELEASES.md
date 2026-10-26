# DARM releases

Release identities published by PerceptraAI Lab. Check any copy against these SHA-256 digests. Qualification evidence is signed with the key in [SIGNING-KEY.md](SIGNING-KEY.md).

## darmd 0.5.3 (qualified 25 October 2026)

| Item | SHA-256 |
| --- | --- |
| `release-manifest.json` | `73b1d5339af1a6a7a4265c34081428b0fe3e318ca68c438570cc795063af10e6` |
| `darmd` binary | `a16e360e77a59a10f473d53a15cd1b059ea66ab2e2b73ea364bfa48dc4d19c21` |
| Gate 7 suite 0.3.2 (55 cases) | `b7da0796f782218e88b22745eb2c6f80e6d24c97c68c4ac2854de67e1d936910` |
| Release archive `darm-v053-final.tgz` | `e927721534d7cc64a616efef09a9eecfaead250bed39f3f5028895e28c013bf1` |

**Qualification** (`tools/run_qualification.sh`, disposable Hyper-V host, Ubuntu 24.04.5, kernel 6.8.0-147-generic, BPF-LSM active). Userspace: 49 PASS, 3 OUT_OF_SCOPE, 3 FAIL; qualified for STRICT_PROFILE and C8 (bundle `4da229371def438ead9bcfdc6b87671b0b2d9f7671c46cb23a27073c06ce9be6`). Kernel floor: 52 PASS, 3 OUT_OF_SCOPE, 0 FAIL; qualified for STRICT_KERNEL_RELATIVE and C8 (bundle `65ccbf9b3d8df6ad9441fdc30dfc348c63ec0925cd4a74b777704076b44f1236`). Both verifiers reported CURRENT after a fresh rerun, and both assessments' release bindings record the manifest digest above. All four bundles (both assessments and both reproductions) are signed by key `713f88cb3c2cfe50`, after the unsigned on-host run.

**Changes from 0.5.2.** After an effect is dispatched, the witness records an abort as ABORTED only when the executor proves no effect happened; otherwise it records UNKNOWN and suspends (finding F; formalized in `GRBS/B10AbortAfterDispatch.lean` and `GRBS/B10bAbortEvidence.lean`). The suite adds `write_inplace_race`, `abort_after_effect_latches` and `witness_cross_role_ops`, and the runner and verifier excuse only outcomes each case declares.

**Reproducible build.** The binary was rebuilt from the release source and reproduced byte for byte on two machines: the original build host and an independent Hyper-V VM with a fresh crate download. Conditions: Ubuntu 24.04 with rustc, cargo and libstd-rust-dev `1.75.0+dfsg0ubuntu1-0ubuntu7.4`, binutils `2.42-4ubuntu2.10`, gcc `4:13.2.0-7ubuntu1`, libc6-dev `2.39-0ubuntu8.9`; `cargo build --release --locked` run as root, because the binary embeds crate source paths under `/root/.cargo/registry`. Source tree digest `7c455fb82961c877347b79f7a53a147bfb20d5bae08a951a250edbf9ae95da19`. Signed statement: [`provenance/darmd-0.5.3.provenance.dsse.json`](provenance/darmd-0.5.3.provenance.dsse.json) (SHA-256 `a925af3392d1d810f3f032d54e28fd3bb29c01ac06de0febe34d270eee907909`), signed by key `713f88cb3c2cfe50`. Not claimed: a hermetic or isolated build environment, any SLSA build level, other toolchains or distributions, or the prebuilt floor artifacts.

**Scope and limits.** Isolated case fixtures launch the installed bytes, not a live governed root. In both profiles, `write_inplace_race` remains OUT_OF_SCOPE under `A_single_writer`: a writer with legitimate access that modifies a governed file in place is excluded by assumption, not by mechanism, even with the kernel floor. Not established: independent external review, production lifecycle, migration from 0.5.2. Corrections ship in the release's `qualification/v053/ERRATA.md`.

## darmd 0.5.2 (qualified 19 October 2026)

| Item | SHA-256 |
| --- | --- |
| `release-manifest.json` (as pinned by the installed pilot configuration) | `12384f6c17db76fa99d08cd4d29068bc6bd04949e2cd791e3f8278cb954d74ee` |
| `darmd` binary | `94991df1168366dea991228105935c28814bd6263ac318d73f91c24baf9517bb` |
| Signed qualification evidence archive | `889eb58a0ad4077b4b1eb40d58b5f69ff0e36401ebc870f5afc8eec5c5ba55c9` |

Signed qualification (kernel floor: 50 PASS, 2 OUT_OF_SCOPE, 0 FAIL, reproduced), signed by key `713f88cb3c2cfe50`, and accepted in a static evidence review (review kit 2GYkEA); that review is not an independent external review. Known defect: an abort after dispatch can record ABORTED over an effect that happened (finding F), fixed in 0.5.3.
