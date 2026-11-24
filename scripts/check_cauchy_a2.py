"""Audit A2 separately from the frozen 972 preceding fingerprints."""
from pathlib import Path
import sys
from check_audit import ROOT, ALLOWED, parse_baseline, parse_log
from check_release_v012 import require

CERT = ROOT / "certificates/v0.2.0"

def main():
    require(len(sys.argv) == 2, "Usage: python scripts/check_cauchy_a2.py cauchy-a2.log")
    names = (CERT / "A2_QUERIES.txt").read_text(encoding="utf-8").splitlines()
    got = parse_log(Path(sys.argv[1]).read_text(encoding="utf-8-sig"))
    old = parse_baseline((ROOT / "certificates/v0.1.2/AXIOMAS.txt").read_text(encoding="utf-8"))
    a1 = parse_baseline((CERT / "A1_AXIOMAS.txt").read_text(encoding="utf-8"))
    require(len(old) == 952 and len(a1) == 20 and not (set(old) & set(a1)), "Historical inventory mismatch")
    require(len(names) == 62 and len(set(names)) == 62 and set(got) == set(names),
            f"A2 declaration mismatch: {set(names) ^ set(got)}")
    require(not (set(got) & (set(old) | set(a1))), "A2 name duplicates a certified declaration")
    for name in names:
        print(name + "|" + (",".join(got[name]) if got[name] else "<none>"), flush=True)
    errors = [f"A2 forbidden axioms: {name}: {ax}" for name, ax in got.items()
              if not set(ax) <= ALLOWED]
    if errors:
        raise SystemExit("\n".join(errors))
    print(f"PASS TA-LEAN-0011 A2: {len(got)} new queries; 972 preserved; no new Choice or sorryAx", flush=True)

if __name__ == "__main__":
    main()
