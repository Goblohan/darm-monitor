"""Produce a machine-readable comparison and reproducible negative controls."""
from __future__ import annotations
import json
from datetime import datetime, timezone
from pathlib import Path
from fixtures import NOW, POLICY, make_evidence, make_request
from verifier import decide


def cases():
    good=make_request()
    weak=make_request(source_evidence=make_evidence(claims=["json_shape", "file_integrity"]))
    valid_remote=make_request(claim_id="remote_acceptance_confirmed",target_evidence=make_evidence(issuer="target-key"))
    missing_remote=make_request(claim_id="remote_acceptance_confirmed")
    wrong_repr=make_request();wrong_repr["mapping_id"]="mapping:untrusted-guess"
    wrong_subject=make_request();wrong_subject["subject_digest"]="sha256:"+"4"*64
    forged=make_request();forged["source_evidence"]["signed"]["issued_at"]-=1
    unknown_claim=make_request();unknown_claim["claim_id"]="verified_financial_advice"
    not_action=make_request();not_action["action_authorized"]=False
    return [
        ("covered_source_warrant",good,True),
        ("source_scope_missing",weak,False),
        ("remote_receipt_from_target",valid_remote,True),
        ("remote_claim_without_receipt",missing_remote,False),
        ("untrusted_heterogeneous_mapping",wrong_repr,False),
        ("valid_signature_wrong_subject",wrong_subject,False),
        ("tampered_signed_evidence",forged,False),
        ("unknown_target_claim",unknown_claim,False),
        ("valid_reliance_but_action_not_authorized",not_action,True),
    ]


def main():
    rows=[]
    for name,request,expected in cases():
        verdict=decide(request,POLICY,NOW)
        rows.append({"case":name,"expected_reliance":"ADMIT" if expected else "REFUSE",**verdict.as_dict(),"correct":verdict.admit==expected})
    unsupported=[r for r in rows if r["expected_reliance"]=="REFUSE"]
    supported=[r for r in rows if r["expected_reliance"]=="ADMIT"]
    report={
        "name":"HDB-1E × E37 Non-Laundering Research Prototype",
        "status":"synthetic deterministic mock, not deployed agent or independently audited Lean runtime",
        "clock":"fixed UTC " + datetime.fromtimestamp(NOW,timezone.utc).isoformat(),
        "metrics":{
            "cases":len(rows),"correct":sum(r["correct"] for r in rows),
            "false_admits":sum(r["reliance"]=="ADMIT" for r in unsupported),
            "unsupported":len(unsupported),
            "false_refusals":sum(r["reliance"]=="REFUSE" for r in supported),
            "supported":len(supported),
        },
        "cases":rows,
    }
    path=Path(__file__).with_name("EXPERIMENT_RESULTS.json")
    path.write_text(json.dumps(report,indent=2,sort_keys=True)+"\n")
    print(json.dumps(report["metrics"],indent=2))
    print("Saved:",path)
    return 0 if all(r["correct"] for r in rows) else 1

if __name__=="__main__":
    raise SystemExit(main())
