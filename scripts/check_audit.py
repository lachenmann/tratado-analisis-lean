"""Check direct Lean #print axioms output against the immutable initial checkpoint."""
from __future__ import annotations
import collections
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
BASE = ROOT / "certificates/TA-LEAN-0010/AXIOMAS.txt"
AUDIT = ROOT / "TratadoAnalisis/Audit.lean"
PATTERN = re.compile(r"(?m)^'([^'\r\n]+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on (?:any )?axioms)[ \t]*\r?$")
ALLOWED = {"propext", "Quot.sound"}


def normalized(items):
    return tuple(sorted(a.strip() for a in items if a.strip()))


def parse_baseline(text):
    out = {}
    for row in text.splitlines():
        name, ax = row.split("|", 1)
        if name in out:
            raise ValueError(f"Duplicate baseline: {name}")
        out[name] = () if ax == "<none>" else normalized(ax.split(","))
    return out


def parse_log(text):
    out = {}
    for name, ax in PATTERN.findall(text):
        if name in out:
            raise ValueError(f"Duplicate audit output: {name}")
        out[name] = normalized(ax.split(",")) if ax else ()
    return out


def main():
    if len(sys.argv) != 2:
        raise SystemExit("Usage: python scripts/check_audit.py audit.log")
    base = parse_baseline(BASE.read_text(encoding="utf-8-sig"))
    got = parse_log(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8-sig"))
    queries = len(re.findall(r"(?m)^\s*#print\s+axioms\s+", AUDIT.read_text(encoding="utf-8-sig")))
    assert len(base) == 833, "Unexpected historical baseline length"
    assert sum("Classical.choice" in a for a in base.values()) == 65
    assert not any("sorryAx" in a for a in base.values())
    if len(got) != queries:
        raise SystemExit(f"Audit incomplete: {queries} queries; {len(got)} outputs")
    errors = []
    for name, ax in base.items():
        if got.get(name) != ax:
            errors.append(f"Regression: {name}: {ax!r} -> {got.get(name)!r}")
    new = got.keys() - base.keys()
    for name in sorted(new):
        if not set(got[name]) <= ALLOWED:
            errors.append(f"Unexpected new axioms: {name}: {got[name]!r}")
    if any("sorryAx" in a for a in got.values()):
        errors.append("sorryAx detected")
    if errors:
        raise SystemExit("\n".join(errors))
    print(f"PASS: {len(base)} historical fingerprints preserved; {len(new)} additional; {len(got)} total")
    print(f"Classical.choice: {sum('Classical.choice' in a for a in got.values())}; sorryAx: 0")


if __name__ == "__main__":
    main()
