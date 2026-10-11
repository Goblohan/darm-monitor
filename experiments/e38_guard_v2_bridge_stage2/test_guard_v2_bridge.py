"""Native-format E38/Guard evidence tests. No broker or external system is used."""
import copy
import hashlib
import json
import os
import tempfile
from pathlib import Path
import unittest

from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey
from guard_v2_bridge import NARROW_CLAIM, verify_snapshot, read_workspace_snapshot


def message(priv, rid, target, digest, kid):
    to_sign = f'darm-attest-v2|{rid}|{target}|{digest}'.encode()
    return json.dumps({'v':2, 'rid':rid, 'target':target, 'digest':digest, 'kid':kid,
                       'sig':priv.sign(to_sign).hex()},sort_keys=True).encode()


def log_entry(e, prev):
    obj = dict(e, prev_hash=prev, ts='2026-10-09T00:00:00')
    obj['entry_hash'] = hashlib.sha256(json.dumps(obj, sort_keys=True).encode()).hexdigest()
    return obj


class BridgeTests(unittest.TestCase):
    def setUp(self):
        self.priv = Ed25519PrivateKey.generate()
        pub = self.priv.public_key().public_bytes(serialization.Encoding.Raw, serialization.PublicFormat.Raw)
        self.kid = hashlib.sha256(pub).hexdigest()[:16]
        self.ring = {'active':self.kid, 'keys':{self.kid:pub.hex()}}
        self.rid = 'r1'
        self.target='/workspace/report.txt'
        self.content=b'benign report'
        digest=hashlib.sha256(self.content).hexdigest()
        self.raw=message(self.priv,self.rid,self.target,digest,self.kid)
        self.entries=[log_entry({'event':'prepared','request_id':self.rid},'0'*64)]
        self.entries.append(log_entry({'event':'outcome','request_id':self.rid,'target':self.target,
                       'tool':'write_file','effect':'succeeded'}, self.entries[-1]['entry_hash']))
        self.make_cp()

    def make_cp(self):
        genesis=self.entries[0]['entry_hash']
        count=len(self.entries)
        head=self.entries[-1]['entry_hash']
        raw=f'darm-checkpoint-v1|{genesis}|{count}|{head}'.encode()
        self.cps=[{'v':1,'genesis':genesis,'count':count,'head':head,
                   'kid':self.kid, 'sig':self.priv.sign(raw).hex()}]

    def run_case(self,claim=NARROW_CLAIM,**kwargs):
        values=dict(raw_attestation=self.raw,content=self.content,
           logical_target=self.target,expected_request_id=self.rid,
           public_ring=self.ring,audit_entries=self.entries,
           published_checkpoints=self.cps,requested_claim=claim)
        values.update(kwargs)
        return verify_snapshot(**values)

    def test_valid_native_attestation_with_anchor(self):self.assertTrue(self.run_case().admit)
    def test_content_meaning_not_signed(self):self.assertFalse(self.run_case('validated_financial_report').admit)
    def test_no_checkpoint(self):self.assertFalse(self.run_case(published_checkpoints=[]).admit)
    def test_replayed_checkpoint_with_new_event(self):
        self.entries.append(log_entry({'event':'outcome','request_id':'r2','target':'/workspace/other.txt',
                      'tool':'write_file','effect':'succeeded'},self.entries[-1]['entry_hash']))
        self.assertFalse(self.run_case().admit)
    def test_wrong_target(self):self.assertFalse(self.run_case(logical_target='/workspace/other.txt').admit)
    def test_wrong_request(self):self.assertFalse(self.run_case(expected_request_id='r2').admit)
    def test_changed_bytes(self):self.assertFalse(self.run_case(content=b'changed').admit)
    def test_tampered_signature(self):
        a=json.loads(self.raw)
        a['sig']='00'*64
        self.assertFalse(self.run_case(raw_attestation=json.dumps(a).encode()).admit)
    def test_wrong_ring(self):
        other=copy.deepcopy(self.ring)
        other['keys']={}
        self.assertFalse(self.run_case(public_ring=other).admit)
    def test_tampered_log(self):
        self.entries[1]['effect']='failed'
        self.assertFalse(self.run_case().admit)
    def test_superseding_delete(self):
        self.entries.append(log_entry({'event':'outcome','request_id':'r2','target':self.target,
                      'tool':'delete_file','effect':'succeeded'},self.entries[-1]['entry_hash']))
        self.make_cp()
        self.assertFalse(self.run_case().admit)
    def test_stale_attestation_after_other_write(self):
        self.entries.append(log_entry({'event':'outcome','request_id':'r2','target':self.target,
                      'tool':'write_file','effect':'succeeded'},self.entries[-1]['entry_hash']))
        self.make_cp()
        self.assertFalse(self.run_case().admit)
    def test_forged_checkpoint(self):
        self.cps[0]['sig']='00'*64
        self.assertFalse(self.run_case().admit)
    def test_wrong_boundary(self):self.assertFalse(self.run_case(logical_target='/other/report.txt').admit)
    def test_malformed_schema(self):
        a=json.loads(self.raw)
        a['warrant_scope']=['everything']
        self.assertFalse(self.run_case(raw_attestation=json.dumps(a).encode()).admit)
    def test_bad_checkpoint_key_id(self):
        self.cps[0]['kid']='0000000000000000'
        self.assertFalse(self.run_case().admit)
    def test_signature_without_audit_event(self):
        self.entries=[self.entries[0]]
        self.make_cp()
        self.assertFalse(self.run_case().admit)

class WorkspaceReadTests(unittest.TestCase):
    def test_pinned_descriptor_binds_data_and_attribute(self):
        with tempfile.TemporaryDirectory() as temp:
            path = Path(temp) / 'report.txt'
            path.write_bytes(b'abc')
            try:
                os.setxattr(path, 'user.darm', b'pretend-attestation')
            except OSError as exc:
                self.skipTest(f'xattr not supported in test filesystem: {exc}')
            xattr, content = read_workspace_snapshot(temp, '/workspace/report.txt')
            self.assertEqual(xattr, b'pretend-attestation')
            self.assertEqual(content, b'abc')

    def test_symlink_leaf_refused(self):
        with tempfile.TemporaryDirectory() as temp:
            (Path(temp)/'actual.txt').write_bytes(b'abc')
            (Path(temp)/'alias.txt').symlink_to('actual.txt')
            with self.assertRaises(OSError):
                read_workspace_snapshot(temp, '/workspace/alias.txt')

    def test_symlink_directory_refused(self):
        with tempfile.TemporaryDirectory() as temp:
            (Path(temp)/'dir').mkdir()
            (Path(temp)/'dir'/'f.txt').write_bytes(b'abc')
            (Path(temp)/'alias').symlink_to('dir',target_is_directory=True)
            with self.assertRaises(OSError):
                read_workspace_snapshot(temp, '/workspace/alias/f.txt')

    def test_noncanonical_target_refused(self):
        with tempfile.TemporaryDirectory() as temp:
            with self.assertRaises(ValueError):
                read_workspace_snapshot(temp, '/workspace/../elsewhere')

    def test_hard_link_refused(self):
        with tempfile.TemporaryDirectory() as temp:
            (Path(temp)/'a.txt').write_bytes(b'abc')
            os.link(Path(temp)/'a.txt',Path(temp)/'b.txt')
            with self.assertRaises(ValueError):
                read_workspace_snapshot(temp, '/workspace/a.txt')

if __name__=='__main__':unittest.main()
