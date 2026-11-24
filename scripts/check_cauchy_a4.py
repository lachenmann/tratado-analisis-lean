"""Audit A4 separately from the frozen preceding fingerprints."""
from pathlib import Path
import sys
from check_audit import ROOT, ALLOWED, parse_baseline, parse_log
from check_release_v012 import require

CERT = ROOT / "certificates/v0.2.0"

def main():
    require(len(sys.argv) == 2, "Usage: python scripts/check_cauchy_a4.py cauchy-a4.log")
    names = (CERT / "A4_QUERIES.txt").read_text(encoding="utf-8").splitlines()
    got = parse_log(Path(sys.argv[1]).read_text(encoding="utf-8-sig"))
    old = parse_baseline((ROOT / "certificates/v0.1.2/AXIOMAS.txt").read_text(encoding="utf-8"))
    require(len(old) == 952, "Historical count mismatch")
    prev = set(old)
    for stage, count in [("A1", 20), ("A2", 62), ("A3", 40)]:
        group = parse_baseline((CERT / f"{stage}_AXIOMAS.txt").read_text(encoding="utf-8"))
        require(len(group) == count and not (prev & set(group)), f"Historical mismatch: {stage}")
        prev.update(group)
    require(len(prev) == 1074, "Historical duplicate names")
    require(len(names) == 39 and len(set(names)) == 39 and set(got) == set(names),
            f"A4 declaration mismatch: {set(names) ^ set(got)}")
    require(not (set(got) & prev), "A4 name duplicates a certified declaration")
    for name in names:
        print(name + "|" + (",".join(got[name]) if got[name] else "<none>"), flush=True)
    errors = [f"A4 forbidden axioms: {name}: {ax}" for name, ax in got.items()
              if not set(ax) <= ALLOWED]
    if errors:
        raise SystemExit("\n".join(errors))
    print(f"PASS TA-LEAN-0011 A4: {len(got)} new queries; 1074 preserved; no new Choice or sorryAx", flush=True)

if __name__ == "__main__":
    main()
