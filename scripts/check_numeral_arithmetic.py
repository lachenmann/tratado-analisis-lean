"""Separate exact-name and axiom audit for v0.1.2 P04."""
from pathlib import Path
import sys
from check_audit import ROOT, ALLOWED, parse_log

def main():
    if len(sys.argv) != 2:
        raise SystemExit("Usage: python scripts/check_numeral_arithmetic.py numeral-arithmetic.log")
    names = (ROOT / "certificates/v0.1.2/P04_QUERIES.txt").read_text(encoding="utf-8").splitlines()
    got = parse_log(Path(sys.argv[1]).read_text(encoding="utf-8-sig"))
    if len(names) != len(set(names)) or set(names) != set(got):
        raise SystemExit("P04 declaration mismatch: " + str(set(names) ^ set(got)))
    for name in names:
        print(name + "|" + (",".join(got[name]) if got[name] else "<none>"), flush=True)
    errors = [f"P04 forbidden axioms: {name}: {ax}" for name, ax in got.items()
              if not set(ax) <= ALLOWED]
    if errors:
        raise SystemExit("\n".join(errors))
    baseline = (ROOT / "certificates/v0.1.2/P04_AXIOMAS.txt").read_text(encoding="utf-8").splitlines()
    actual = [name + "|" + (",".join(got[name]) if got[name] else "<none>") for name in names]
    if actual != baseline:
        raise SystemExit("Certified P04 fingerprints changed")
    print(f"PASS P04: {len(got)} separate queries; no Choice or sorryAx")

if __name__ == "__main__":
    main()
