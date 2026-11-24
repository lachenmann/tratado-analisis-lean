"""Audit A3 separately from the frozen preceding fingerprints."""
from pathlib import Path
import sys
import subprocess
from check_audit import ROOT, ALLOWED, parse_baseline, parse_log
from check_release_v012 import require

CERT = ROOT / "certificates/v0.2.0"

def main():
    require(len(sys.argv) == 2, "Usage: python scripts/check_cauchy_a3.py cauchy-a3.log")
    names = (CERT / "A3_QUERIES.txt").read_text(encoding="utf-8").splitlines()
    got = parse_log(Path(sys.argv[1]).read_text(encoding="utf-8-sig"))
    old = parse_baseline((ROOT / "certificates/v0.1.2/AXIOMAS.txt").read_text(encoding="utf-8"))
    a1 = parse_baseline((CERT / "A1_AXIOMAS.txt").read_text(encoding="utf-8"))
    a2 = parse_baseline((CERT / "A2_AXIOMAS.txt").read_text(encoding="utf-8"))
    require(len(old) == 952 and len(a1) == 20 and len(a2) == 62, "Historical count mismatch")
    prev = set(old) | set(a1) | set(a2)
    require(len(prev) == 1034, "Historical duplicate names")
    require(len(names) == 40 and len(set(names)) == 40 and set(got) == set(names),
            f"A3 declaration mismatch: {set(names) ^ set(got)}")
    require(not (set(got) & prev), "A3 name duplicates a certified declaration")
    for name in names:
        print(name + "|" + (",".join(got[name]) if got[name] else "<none>"), flush=True)
    errors = [f"A3 forbidden axioms: {name}: {ax}" for name, ax in got.items()
              if not set(ax) <= ALLOWED]
    if errors:
        raise SystemExit("\n".join(errors))
    require(got == parse_baseline((CERT / "A3_AXIOMAS.txt").read_text(encoding="utf-8")),
            "Certified A3 fingerprints changed")
    a3_blobs = {
        "TratadoAnalisis/Rationals/AbsoluteValue.lean": "6a9c08ab375e44296df57ddd483b7d0a3b35bdf4",
        "TratadoAnalisis/Cauchy/RationalDistance.lean": "f0ccc9fc486d303e46355c581889b40255883c68",
        "TratadoAnalisis/Bridges/RationalAbsoluteValue.lean": "c697ef5b5b309007716907fb179a58e160377fa7",
        "tests/CauchyA3.lean": "57850027bdae3f038adcde462200a7728a4520f4",
    }
    for path, sha in a3_blobs.items():
        actual = subprocess.check_output(["git", "hash-object", "--no-filters", path], cwd=ROOT).decode("ascii").strip()
        require(actual == sha, f"Certified A3 source changed: {path}")
    print(f"PASS TA-LEAN-0011 A3: {len(got)} new queries; 1034 preserved; no new Choice or sorryAx", flush=True)

if __name__ == "__main__":
    main()
