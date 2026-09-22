"""Differential certification of the darmkernel binary against Lean's kernel.

Generates random requests (fixed seed), runs them through the compiled
binary, then writes a Lean file asserting each binary answer as a theorem
proved by `decide +kernel`. If that file compiles, every answer the binary
gave was confirmed by the Lean kernel's own evaluation of kernelDecide.
This is evidence about the compiled binary, not a proof of the compiler.
"""
import json, os, random, subprocess, sys
from collections import Counter

BIN = os.environ.get("DARM_KERNEL_BIN", ".lake/build/bin/darmkernel")
OUT = "tests/generated/binary_certificates.lean"
N = int(os.environ.get("DARM_CERT_N", "1000"))
MIN = int(os.environ.get("DARM_CERT_MIN", "10"))
SEED = int(os.environ.get("DARM_CERT_SEED", "20260922"))

TOOLS = ["read", "send", "exec"]
KEYS = ["k1", "k2"]
VALUES = ["/w/a", "/w/b", "/t/x", "/etc/p", "v1", "v2"]
PREFIXES = ["/w/", "/t/"]
EXACT = ["v1", "v2"]
PROVS = ["authoritative", "derived", "untrusted"]
OUTCOMES = ["admit", "temporal", "observation", "authority", "semantic", "provenance"]


def sample(rng, xs, lo, hi):
    return rng.sample(xs, rng.randint(lo, min(hi, len(xs))))


def gen(rng):
    tools = []
    for t in TOOLS:
        if rng.random() < 0.8:
            rules = [{"key": k, "allowedValues": sample(rng, EXACT, 0, 2),
                      "allowedPrefixes": sample(rng, PREFIXES, 0, 2)}
                     for k in sample(rng, KEYS, 0, 2)]
            tools.append({"tool": t, "rules": rules})
    cred = {"tools": sample(rng, TOOLS, 1, 3), "expired": rng.random() < 0.15}
    tool = rng.choice(TOOLS) if rng.random() < 0.85 else "unknown"
    rules = {r["key"]: r for tp in tools if tp["tool"] == tool for r in tp["rules"]}
    args = []
    for k in sample(rng, KEYS, 0, 2):
        r = rules.get(k)
        choices = (r["allowedValues"] + [x + "f" for x in r["allowedPrefixes"]]) if r else []
        v = rng.choice(choices) if choices and rng.random() < 0.7 else rng.choice(VALUES)
        args.append({"key": k, "value": v, "prov": rng.choice(PROVS)})
    return {"policy": {"tools": tools}, "credential": cred,
            "invocation": {"tool": tool, "args": args}}


def s(x):
    return json.dumps(x)


def lst(xs, f):
    return "[" + ", ".join(f(x) for x in xs) + "]"


def lean_policy(p):
    def rule(r):
        return "{ key := %s, allowedValues := %s, allowedPrefixes := %s }" % (
            s(r["key"]), lst(r["allowedValues"], s), lst(r["allowedPrefixes"], s))
    def tp(t):
        return "{ tool := %s, rules := %s }" % (s(t["tool"]), lst(t["rules"], rule))
    return "({ tools := %s } : Policy)" % lst(p["tools"], tp)


def lean_cred(c):
    return "({ tools := %s, expired := %s } : Credential)" % (
        lst(c["tools"], s), "true" if c["expired"] else "false")


def lean_inv(i):
    def arg(a):
        return "{ key := %s, value := %s, prov := Provenance.%s }" % (
            s(a["key"]), s(a["value"]), a["prov"])
    return "({ tool := %s, args := %s } : Invocation)" % (s(i["tool"]), lst(i["args"], arg))


def lean_decision(d):
    if d.get("decision") == "admit":
        return "Decision.admit"
    return "Decision.reject Failure.%s" % d["failure"]


def main():
    rng = random.Random(SEED)
    reqs = [gen(rng) for _ in range(N)]
    raw = subprocess.run([BIN], input="\n".join(json.dumps(r) for r in reqs) + "\n",
                         capture_output=True, text=True, timeout=120).stdout
    answers = [json.loads(l) for l in raw.splitlines() if l.strip()]
    if len(answers) != N:
        sys.exit(f"expected {N} answers, got {len(answers)}")
    tally = Counter()
    lines = ["import K1DecisionKernel", "", "open DARM.Kernel", "",
             f"-- {N} darmkernel answers (seed {SEED}), each certified by decide +kernel.", ""]
    for i, (r, a) in enumerate(zip(reqs, answers)):
        if "error" in a or a.get("decision") not in ("admit", "reject"):
            sys.exit(f"case {i}: binary returned an error: {a}")
        tally["admit" if a["decision"] == "admit" else a["failure"]] += 1
        lines += [f"example : kernelDecide {lean_policy(r['policy'])}",
                  f"    {lean_cred(r['credential'])}",
                  f"    {lean_inv(r['invocation'])} = {lean_decision(a)} := by",
                  "  decide +kernel", ""]
    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    open(OUT, "w").write("\n".join(lines))
    print(f"wrote {N} certificates to {OUT}")
    for k in OUTCOMES:
        print(f"  {k:12s} {tally[k]}")
    missing = [k for k in OUTCOMES if tally[k] < MIN]
    if missing:
        sys.exit(f"coverage gap, fewer than {MIN} cases for: {missing}")


if __name__ == "__main__":
    main()
