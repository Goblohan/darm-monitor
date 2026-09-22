import json, subprocess, sys

BIN = ".lake/build/bin/darmkernel"

POLICY = {"tools": [
    {"tool": "file_read", "rules": [
        {"key": "path", "allowedValues": [], "allowedPrefixes": ["/workspace/"]}]},
    {"tool": "send_email", "rules": [
        {"key": "to", "allowedValues": ["team@perceptra.ai"], "allowedPrefixes": []}]},
]}
CRED = {"tools": ["file_read"], "expired": False}

def inv(tool, key, value, prov="authoritative"):
    return {"tool": tool, "args": [{"key": key, "value": value, "prov": prov}]}

def req(invocation, cred=CRED):
    return {"policy": POLICY, "credential": cred, "invocation": invocation}

CASES = [
    ("admit: allowed path",       req(inv("file_read", "path", "/workspace/notes.txt")), "admit", None),
    ("S: forbidden path",         req(inv("file_read", "path", "/etc/passwd")),          "reject", "semantic"),
    ("P: untrusted value",        req(inv("file_read", "path", "/workspace/notes.txt", "untrusted")), "reject", "provenance"),
    ("O: unknown tool",           req(inv("code_exec", "cmd", "ls")),                     "reject", "observation"),
    ("A: tool not in credential", req(inv("send_email", "to", "team@perceptra.ai")),      "reject", "authority"),
    ("T: expired credential",     req(inv("file_read", "path", "/workspace/notes.txt"),
                                      {"tools": ["file_read"], "expired": True}),        "reject", "temporal"),
]

lines = [json.dumps(c[1]) for c in CASES] + ['{"not": "a valid request"}']
out = subprocess.run([BIN], input="\n".join(lines) + "\n",
                     capture_output=True, text=True, timeout=30).stdout.strip().splitlines()

failed = 0
for (name, _, want_dec, want_fail), line in zip(CASES, out):
    got = json.loads(line)
    ok = got.get("decision") == want_dec and got.get("failure") == want_fail
    failed += not ok
    print("PASS" if ok else "FAIL", name, "->", line)

bad = json.loads(out[-1])
ok = bad.get("decision") == "reject" and "error" in bad
failed += not ok
print("PASS" if ok else "FAIL", "malformed input fails closed ->", out[-1])

print(f"\n{len(CASES) + 1 - failed}/{len(CASES) + 1} passed")
sys.exit(1 if failed else 0)
