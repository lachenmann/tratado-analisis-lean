"""Check the v0.1.2 P01 separate kernel audit (without changing old baselines)."""
from pathlib import Path
import sys
from check_audit import ROOT, ALLOWED, parse_log

def main():
    if len(sys.argv) != 2:
        raise SystemExit("Usage: python scripts/check_prerequisites.py prerequisites.log")
    expected = (ROOT / "certificates/v0.1.2/P01_QUERIES.txt").read_text(encoding="utf-8").splitlines()
    got = parse_log(Path(sys.argv[1]).read_text(encoding="utf-8-sig"))
    if len(expected) != len(set(expected)) or set(got) != set(expected):
        raise SystemExit("P01 declaration mismatch: " + str(set(expected) ^ set(got)))
    for name in expected:
        print(name + "|" + (",".join(got[name]) if got[name] else "<none>"), flush=True)
    errors = [f"P01 forbidden axioms: {name}: {axioms}"
              for name, axioms in got.items() if not set(axioms) <= ALLOWED]
    if errors:
        raise SystemExit("\n".join(errors))
    baseline = (ROOT / "certificates/v0.1.2/P01_AXIOMAS.txt").read_text(encoding="utf-8").splitlines()
    actual = [name + "|" + (",".join(got[name]) if got[name] else "<none>") for name in expected]
    if actual != baseline:
        raise SystemExit("Certified P01 fingerprints changed")
    print(f"PASS P01: {len(got)} separate queries; no Choice or sorryAx")

if __name__ == "__main__":
    main()
