"""Fast, deterministic mutation adequacy gate (9 intentional faults)."""
from __future__ import annotations
import sys
import types
from pathlib import Path
from dataclasses import replace

from fixtures import NOW, POLICY, make_evidence, make_request
from verifier import decide as original_decide

SOURCE = Path(__file__).with_name("verifier.py").read_text()


def wrong_subject():
    r=make_request();r["subject_digest"]="sha256:"+"1"*64;return r,POLICY


def wrong_request():
    r=make_request();r["request_id"]="different";return r,POLICY


def bad_issuer_claim():
    return make_request(source_evidence=make_evidence(claims=["json_shape", "file_integrity", "recipient_authority", "payload_authority", "external_send_authority", "risk_certified"])),POLICY


def no_delta_evidence():
    return make_request(source_evidence=make_evidence(claims=["json_shape", "recipient_authority", "payload_authority", "external_send_authority"])),POLICY


def bad_mapping():
    r=make_request();r["mapping_id"]="forged_mapping";return r,POLICY


def bad_claim():
    r=make_request();r["claim_id"]="nonexistent_target_claim";return r,POLICY


def tamper_signature():
    r=make_request();r["source_evidence"]["signed"]["issued_at"] = NOW-31;return r,POLICY


def bad_audience():
    return make_request(source_evidence=make_evidence(audience="untrusted.consumer")),POLICY


MUTATIONS = {
    "remove-ed25519-verification": (
        'issuer.key.verify(base64.b64decode(signature, validate=True), canonical(signed))',
        'None', tamper_signature),
    "remove-subject-binding": ('if signed["subject_digest"] != subject_digest:', 'if False:',wrong_subject),
    "remove-request-binding": ('if signed["request_id"] != request_id:', 'if False:',wrong_request),
    "remove-issuer-claim-scope": ('if not set(signed["claims"]) <= issuer.permitted_claims:', 'if False:',bad_issuer_claim),
    "remove-expiry": ('if not (signed["issued_at"] <= now < signed["expires_at"]):', 'if False:',lambda: (make_request(source_evidence=make_evidence(expires_at=NOW-1)),POLICY)),
    "remove-trusted-mapping-check": ('if request["mapping_id"] != policy.mapping_id:', 'if False:',bad_mapping),
    "remove-target-delta": ('required = policy.claim_requirements[claim_id] | policy.introduced_obligations', 'required = policy.claim_requirements[claim_id]',no_delta_evidence),
    "remove-audience-binding": ('if signed["audience"] != audience:', 'if False:',bad_audience),
    "remove-trusted-target-claim": ('if not isinstance(claim_id, str) or claim_id not in policy.claim_requirements:', 'if False:',bad_claim),
}


def run():
    caught=0
    for i,(name,(old,new,case)) in enumerate(MUTATIONS.items()):
        assert SOURCE.count(old)==1, name
        request,policy=case()
        assert not original_decide(request,policy,NOW).admit, f"invalid baseline {name}"
        mod=types.ModuleType(f"hdbmut_{i}")
        sys.modules[mod.__name__]=mod
        try:
            exec(compile(SOURCE.replace(old,new,1),f"<{name}>","exec"),mod.__dict__)
            try:
                admitted=mod.decide(request,policy,NOW).admit
                detected=admitted
                why="false admission" if admitted else "still refused"
            except Exception as exc:
                detected=True
                why=f"uncaught {type(exc).__name__}"
        finally:
            sys.modules.pop(mod.__name__,None)
        caught+=int(detected)
        print(f"{'CAUGHT' if detected else 'MISSED'} {name} ({why})")
    print(f"{caught}/{len(MUTATIONS)} checks caught by targeted adversarial cases")
    return 0 if caught==len(MUTATIONS) else 1

if __name__=="__main__":
    sys.exit(run())
