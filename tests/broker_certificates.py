"""B3 correspondence certificates for the Python broker (DARM Guard v0.6).

Generates seeded broker configurations (policies with selector and payload
rules; registries with exact values and patterns; fresh or expired
credentials) and proposals, runs each through the Python broker's pure
decision path (Broker.decide), and emits two Lean facts per case, each
proved by `decide +kernel`, about darm-monitor's B3 model:
  * (brokerStep cfg p).isSome equals the Python broker's admit decision;
  * the provenance labels the Python broker assigned equal B3's canonicalize.
Coverage floors ensure the certificates exercise admission, provenance and
temporal rejection, admitted untrusted payload, and pattern-derived
provenance. Evidence on sampled inputs, not a proof of the Python code.
"""
import json, os, random, sys
from collections import Counter
from datetime import datetime

sys.path.insert(0, os.path.expanduser(os.environ.get("DARM_GUARD_SRC", "~/darm-guard")))
from darm_guard.broker import Broker, BrokerConfig
from darm_guard.kernel import KernelClient

OUT = "tests/generated/broker_certificates.lean"
N = int(os.environ.get("DARM_CERT_N", "1000"))
SEED = int(os.environ.get("DARM_CERT_SEED", "20260923"))
MIN = int(os.environ.get("DARM_CERT_MIN", "10"))

TOOLS = ["read_file", "write_file", "send"]
KEYS = ["path", "content"]
VALUES = ["/workspace/a", "/workspace/b", "/workspace/reports/q3", "/etc/p", "/tmp/x"]
PREFIXES = ["/workspace/", "/tmp/"]
PATTERNS = ["/workspace/reports/", "/tmp/"]
FLOORS = ["admit", "provenance", "temporal", "admit_untrusted_payload", "admit_derived"]


def mk_rule(rng, k):
    """Payload rules are free-form content; selector rules keep values and prefixes."""
    if rng.random() < 0.35:
        return {"key": k, "allowedValues": [], "allowedPrefixes": [""], "payload": True}
    return {"key": k, "allowedValues": rng.sample(VALUES, rng.randint(0, 2)),
            "allowedPrefixes": rng.sample(PREFIXES, rng.randint(0, 2)), "payload": False}


def gen(rng):
    tools = [{"tool": t, "rules": [mk_rule(rng, k) for k in rng.sample(KEYS, rng.randint(1, 2))]}
             for t in TOOLS if rng.random() < 0.85]
    cred = rng.sample(TOOLS, rng.randint(1, 3))
    reg = rng.sample(VALUES, rng.randint(0, 3))
    pats = rng.sample(PATTERNS, rng.randint(1, 2))
    prop = {"tool": rng.choice(TOOLS),
            "args": [[k, rng.choice(VALUES)] for k in rng.sample(KEYS, rng.randint(0, 2))]}
    return {"tools": tools}, cred, reg, pats, prop


def s(x):
    return json.dumps(x)


def lst(xs, f):
    return "[" + ", ".join(f(x) for x in xs) + "]"


def lean_cfg(pol, cred, reg, pats, expired):
    def rule(r):
        return "{ key := %s, allowedValues := %s, allowedPrefixes := %s, payload := %s }" % (
            s(r["key"]), lst(r["allowedValues"], s), lst(r["allowedPrefixes"], s),
            "true" if r["payload"] else "false")
    def tp(t):
        return "{ tool := %s, rules := %s }" % (s(t["tool"]), lst(t["rules"], rule))
    return ("({ policy := { tools := %s }, credential := { tools := %s, expired := %s }, "
            "registry := { values := %s, prefixes := %s } } : DARM.Broker3.Config)") % (
        lst(pol["tools"], tp), lst(cred, s), "true" if expired else "false",
        lst(reg, s), lst(pats, s))


def lean_prop(prop):
    pair = lambda kv: "(%s, %s)" % (s(kv[0]), s(kv[1]))
    return "({ tool := %s, args := %s } : DARM.Broker.Proposal)" % (
        s(prop["tool"]), lst(prop["args"], pair))


def main():
    rng = random.Random(SEED)
    kernel = KernelClient(os.environ.get("DARM_KERNEL_PATH") or None)
    lines = ["import B3BrokerModel", "", "open DARM.Kernel (Provenance)", "",
             f"-- {N} Python-broker decisions (seed {SEED}), each certified against B3.", ""]
    tally = Counter()
    for i in range(N):
        pol, cred, reg, pats, prop = gen(rng)
        expired = rng.random() < 0.15
        cfg = BrokerConfig(pol, tuple(cred), frozenset(reg), "/nonexistent",
                           datetime(2000, 1, 1) if expired else None,
                           1 if expired else None, tuple(pats))
        inv, _, resp = Broker(cfg, kernel, None).decide(prop)
        if inv is None or (resp["decision"] == "reject" and resp.get("error")):
            sys.exit(f"case {i}: no kernel decision ({resp}); refusing to certify")
        admitted = resp["decision"] == "admit"
        tally["admit" if admitted else resp["failure"]] += 1
        provs = [a["prov"] for a in inv["args"]]
        if admitted and "untrusted" in provs:
            tally["admit_untrusted_payload"] += 1
        if admitted and "derived" in provs:
            tally["admit_derived"] += 1
        C, P = lean_cfg(pol, cred, reg, pats, expired), lean_prop(prop)
        plist = "[" + ", ".join(f"Provenance.{x}" for x in provs) + "]"
        lines += [f"example : (DARM.Broker3.brokerStep {C}",
                  f"    {P}).isSome = {'true' if admitted else 'false'} := by",
                  "  decide +kernel", "",
                  f"example : (DARM.Broker3.canonicalize {C}",
                  f"    {P}).args.map (fun a => a.prov) = {plist} := by",
                  "  decide +kernel", ""]
    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    open(OUT, "w").write("\n".join(lines))
    print(f"wrote {2 * N} certificates ({N} cases) to {OUT}")
    for k in ["admit", "temporal", "observation", "authority", "semantic", "provenance",
              "admit_untrusted_payload", "admit_derived"]:
        print(f"  {k:24s} {tally[k]}")
    short = [k for k in FLOORS if tally[k] < MIN]
    if short:
        sys.exit(f"coverage gap, fewer than {MIN} cases for: {short}")


if __name__ == "__main__":
    main()
