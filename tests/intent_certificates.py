"""E24 intent-gate certificates for the Python broker (DARM Guard v0.7).

Each case: a B3 configuration, a principal intent list, and a sequence of
three proposals run through the real Broker.handle, consuming intents as in
production. One Lean fact per case, proved by decide +kernel: the admit
sequence and the remaining intents equal E24's intentStep folded over the
same proposals. Floors: consumptions, intent rejections, kernel rejections
that keep the intent, exhausted intents. Evidence on sampled inputs.
"""
import os, random, sys, tempfile
from collections import Counter
from datetime import datetime

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from broker_certificates import gen, lean_cfg, lean_prop, lst, s, TOOLS
from darm_guard.broker import AuditLog, Broker, BrokerConfig
from darm_guard.kernel import KernelClient

OUT = "tests/generated/intent_certificates.lean"
N = int(os.environ.get("DARM_CERT_N", "300"))
SEED = int(os.environ.get("DARM_CERT_SEED", "20260924"))
MIN = int(os.environ.get("DARM_CERT_MIN", "10"))
FLOORS = ["consumed", "intent_reject", "kept_on_reject", "exhausted"]


def main():
    rng = random.Random(SEED)
    kernel = KernelClient(os.environ.get("DARM_KERNEL_PATH") or None)
    audit = AuditLog(tempfile.mktemp(suffix=".jsonl"))
    lines = ["import E24EpistemicPremiseTransfer", "",
             f"-- {N} three-step intent sequences (seed {SEED}), each certified against E24.", ""]
    tally = Counter()
    for i in range(N):
        pol, cred, reg, pats, p1 = gen(rng)
        p2 = p1 if rng.random() < 0.5 else gen(rng)[4]
        p3 = gen(rng)[4]
        expired = rng.random() < 0.15
        intents = [rng.choice(TOOLS) for _ in range(rng.randint(0, 3))]
        cfg = BrokerConfig(pol, tuple(cred), frozenset(reg), "/nonexistent",
                           datetime(2000, 1, 1) if expired else None,
                           1 if expired else None, tuple(pats))
        b = Broker(cfg, kernel, audit, intents=intents)
        outs, spent = [], set()
        for p in (p1, p2, p3):
            had = p["tool"] in b.intents
            r = b.handle(p)
            if r["decision"] == "reject" and r.get("error"):
                sys.exit(f"case {i}: no decision ({r}); refusing to certify")
            admitted = r["decision"] == "admit"
            outs.append(admitted)
            if admitted:
                tally["consumed"] += 1
                spent.add(p["tool"])
            elif r.get("failure") == "intent":
                tally["intent_reject"] += 1
                if p["tool"] in spent:
                    tally["exhausted"] += 1
            elif had:
                tally["kept_on_reject"] += 1
        C = lean_cfg(pol, cred, reg, pats, expired)
        P1, P2, P3 = lean_prop(p1), lean_prop(p2), lean_prop(p3)
        bools = "[" + ", ".join("true" if o else "false" for o in outs) + "]"
        lines += ["example :",
                  "    (let c := DARM.E24.claimUserAsked",
                  f"     let s1 := DARM.E24.intentStep {C} {{ intents := {lst(intents, s)} }} {P1} c",
                  f"     let s2 := DARM.E24.intentStep {C} s1.2 {P2} c",
                  f"     let s3 := DARM.E24.intentStep {C} s2.2 {P3} c",
                  "     ([s1.1.isSome, s2.1.isSome, s3.1.isSome], s3.2.intents)) =",
                  f"    ({bools}, {lst(b.intents, s)}) := by",
                  "  decide +kernel", ""]
    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    open(OUT, "w").write("\n".join(lines))
    print(f"wrote {N} sequence certificates to {OUT}")
    for k in FLOORS:
        print(f"  {k:16s} {tally[k]}")
    short = [k for k in FLOORS if tally[k] < MIN]
    if short:
        sys.exit(f"coverage gap, fewer than {MIN} cases for: {short}")


if __name__ == "__main__":
    main()
