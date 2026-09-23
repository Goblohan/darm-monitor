"""B1 correspondence certificates for the Python broker (DARM Guard v0.5).

Generates seeded broker configurations and proposals, runs each proposal
through the Python broker's pure decision path (Broker.decide), and emits
two Lean facts per case, each proved by `decide +kernel`:
  * (brokerStep cfg p).isSome equals the Python broker's admit decision;
  * the provenance labels the Python broker assigned equal B1's canonicalize.
If the generated file compiles, Lean's kernel confirmed the Python broker
matches the B1 model on every case. Evidence on sampled inputs, not a
proof of the Python code. Proposals the broker rejects before the kernel
(malformed, or paths not in normal form) are outside B1 and not generated.
"""
import json, os, random, sys
from collections import Counter
from datetime import datetime

sys.path.insert(0, os.path.expanduser(os.environ.get("DARM_GUARD_SRC", "~/darm-guard")))
from darm_guard.broker import Broker, BrokerConfig
from darm_guard.kernel import KernelClient

OUT = "tests/generated/broker_certificates.lean"
N = int(os.environ.get("DARM_CERT_N", "500"))
SEED = int(os.environ.get("DARM_CERT_SEED", "20260923"))
MIN = int(os.environ.get("DARM_CERT_MIN", "10"))

TOOLS = ["read_file", "list_dir", "send"]
KEYS = ["path", "to"]
VALUES = ["/workspace/a", "/workspace/b", "/workspace/docs", "/etc/p", "/tmp/x"]
PREFIXES = ["/workspace/", "/tmp/"]


def gen(rng):
    tools = []
    for t in TOOLS:
        if rng.random() < 0.85:
            rules = [{"key": k, "allowedValues": rng.sample(VALUES, rng.randint(0, 2)),
                      "allowedPrefixes": rng.sample(PREFIXES, rng.randint(0, 2))}
                     for k in rng.sample(KEYS, rng.randint(1, 2))]
            tools.append({"tool": t, "rules": rules})
    cred = rng.sample(TOOLS, rng.randint(1, 3))
    registry = rng.sample(VALUES, rng.randint(0, len(VALUES)))
    prop = {"tool": rng.choice(TOOLS),
            "args": [[k, rng.choice(VALUES)] for k in rng.sample(KEYS, rng.randint(0, 2))]}
    return {"tools": tools}, cred, registry, prop


def s(x):
    return json.dumps(x)


def lst(xs, f):
    return "[" + ", ".join(f(x) for x in xs) + "]"


def lean_cfg(pol, cred, reg, expired=False):
    def rule(r):
        return "{ key := %s, allowedValues := %s, allowedPrefixes := %s }" % (
            s(r["key"]), lst(r["allowedValues"], s), lst(r["allowedPrefixes"], s))
    def tp(t):
        return "{ tool := %s, rules := %s }" % (s(t["tool"]), lst(t["rules"], rule))
    return ("({ policy := { tools := %s }, credential := { tools := %s, expired := %s }, "
            "registry := { values := %s } } : Config)") % (
        lst(pol["tools"], tp), lst(cred, s), "true" if expired else "false", lst(reg, s))


def lean_prop(prop):
    pair = lambda kv: "(%s, %s)" % (s(kv[0]), s(kv[1]))
    return "({ tool := %s, args := %s } : Proposal)" % (s(prop["tool"]), lst(prop["args"], pair))


def main():
    rng = random.Random(SEED)
    kernel = KernelClient(os.environ.get("DARM_KERNEL_PATH") or None)
    lines = ["import B1BrokerModel", "", "open DARM.Kernel DARM.Broker", "",
             f"-- {N} Python-broker decisions (seed {SEED}), each certified against B1.", ""]
    tally = Counter()
    for i in range(N):
        pol, cred, reg, prop = gen(rng)
        expired = rng.random() < 0.15
        cfg = BrokerConfig(pol, tuple(cred), frozenset(reg), "/nonexistent",
                           datetime(2000, 1, 1) if expired else None,
                           1 if expired else None)
        inv, _, resp = Broker(cfg, kernel, None).decide(prop)
        if inv is None or (resp["decision"] == "reject" and resp.get("error")):
            sys.exit(f"case {i}: no kernel decision ({resp}); refusing to certify")
        admitted = resp["decision"] == "admit"
        tally["admit" if admitted else resp["failure"]] += 1
        C, P = lean_cfg(pol, cred, reg, expired), lean_prop(prop)
        provs = "[" + ", ".join(f"Provenance.{a['prov']}" for a in inv["args"]) + "]"
        lines += [f"example : (brokerStep {C}",
                  f"    {P}).isSome = {'true' if admitted else 'false'} := by",
                  "  decide +kernel", "",
                  f"example : (canonicalize {C}",
                  f"    {P}).args.map (fun a => a.prov) = {provs} := by",
                  "  decide +kernel", ""]
    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    open(OUT, "w").write("\n".join(lines))
    print(f"wrote {2 * N} certificates ({N} cases) to {OUT}")
    for k in ["admit", "temporal", "observation", "authority", "semantic", "provenance"]:
        print(f"  {k:12s} {tally[k]}")
    short = [k for k in ("admit", "provenance", "temporal") if tally[k] < MIN]
    if short:
        sys.exit(f"coverage gap, fewer than {MIN} cases for: {short}")


if __name__ == "__main__":
    main()
