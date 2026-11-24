"""Preserve the full v0.1.2 baseline and audit Cauchy A1 separately."""
from pathlib import Path
from collections import Counter
import re
import subprocess
import sys
from check_audit import ROOT, ALLOWED, parse_baseline, parse_log
from check_release_v012 import PINS, GROUPS, CONFIG, manifest, digest, require

CERT = ROOT / "certificates/v0.2.0"
NEW_LEAN = {
    "TratadoAnalisis/Foundations/FunctionSpace.lean",
    "TratadoAnalisis/Cauchy/RationalSequences.lean",
    "tests/CauchyA1.lean",
    "TratadoAnalisis/Foundations/RelationalFunctions.lean",
    "TratadoAnalisis/Cauchy/SequenceOperations.lean",
    "tests/CauchyA2.lean",
    "TratadoAnalisis/Rationals/AbsoluteValue.lean",
    "TratadoAnalisis/Cauchy/RationalDistance.lean",
    "TratadoAnalisis/Bridges/RationalAbsoluteValue.lean",
    "tests/CauchyA3.lean",
    "TratadoAnalisis/Cauchy/RationalConvergence.lean",
    "tests/CauchyA4.lean",
}
FORBIDDEN_PREFIXES = (
    "TratadoAnalisis.Dedekind", "TratadoAnalisis.Abstract",
    "TratadoAnalisis.Chapter7_0010", "TratadoAnalisis.Bridges",
)

def check_dependencies():
    """Check the project-local import closure of the new mathematical modules."""
    pending = ["TratadoAnalisis.Foundations.FunctionSpace",
               "TratadoAnalisis.Cauchy.RationalSequences",
               "TratadoAnalisis.Foundations.RelationalFunctions",
               "TratadoAnalisis.Cauchy.SequenceOperations",
               "TratadoAnalisis.Rationals.AbsoluteValue",
               "TratadoAnalisis.Cauchy.RationalDistance",
               "TratadoAnalisis.Cauchy.RationalConvergence"]
    seen = set()
    while pending:
        name = pending.pop()
        if name in seen:
            continue
        seen.add(name)
        require(name != "TratadoAnalisis" and
                not name.startswith(FORBIDDEN_PREFIXES),
                f"Forbidden project import: {name}")
        path = ROOT / (name.replace(".", "/") + ".lean")
        require(path.is_file(), f"Project import not found: {name}")
        for line in path.read_text(encoding="utf-8-sig").splitlines():
            m = re.match(r"^\s*(?:public\s+)?import\s+(\S+)", line)
            if m and m.group(1).startswith("TratadoAnalisis"):
                pending.append(m.group(1))
    print(f"PASS A1/A2/A3/A4: project-local import closure ({len(seen)} modules), no Dedekind or abstract post-rational imports", flush=True)

def main():
    require(len(sys.argv) == 8,
            "Usage: python scripts/check_cauchy_a1.py audit.log public-api.log prerequisites.log absolute-value.log completeness-equivalences.log numeral-arithmetic.log cauchy-a1.log")
    for name, expected in PINS.items():
        require(digest(ROOT / name) == expected, f"Historical certificate changed: {name}")
    old = manifest(ROOT / "certificates/v0.1.2/SHA256SUMS")
    require(len(old) == 159 and not (set(old) & NEW_LEAN), "Historical inventory mismatch")
    tracked = subprocess.check_output(["git", "ls-files", "-z"], cwd=ROOT).decode("utf-8").split("\0")
    actual = {p for p in tracked if p.endswith(".lean") or p in CONFIG}
    require(actual == set(old) | NEW_LEAN, f"Unexpected source paths: {actual ^ (set(old) | NEW_LEAN)}")
    for name, value in sorted(old.items()):
        require(digest(ROOT / name) == value, f"Historical source changed: {name}")
    combined = {}
    for (reference, count), logfile in zip(GROUPS, sys.argv[1:7]):
        ref = parse_baseline(reference.read_text(encoding="utf-8-sig"))
        got = parse_log(Path(logfile).read_text(encoding="utf-8-sig"))
        require(len(ref) == count and got == ref, f"Historical axiom regression: {reference.name}")
        require(not (set(combined) & set(ref)), "Duplicate historical name")
        combined.update(got)
    frozen = parse_baseline((ROOT / "certificates/v0.1.2/AXIOMAS.txt").read_text(encoding="utf-8-sig"))
    require(len(combined) == 952 and combined == frozen, "Historical aggregate changed")
    print("PASS: 159/159 v0.1.2 files; 952/952 historical axiom fingerprints unchanged", flush=True)
    check_dependencies()
    names = (CERT / "A1_QUERIES.txt").read_text(encoding="utf-8").splitlines()
    got = parse_log(Path(sys.argv[7]).read_text(encoding="utf-8-sig"))
    require(len(names) == 20 and len(set(names)) == 20 and set(got) == set(names),
            f"A1 declaration mismatch: {set(names) ^ set(got)}")
    require(not (set(got) & set(combined)), "A1 name duplicates the historical audit")
    for name in names:
        print(name + "|" + (",".join(got[name]) if got[name] else "<none>"), flush=True)
    errors = [f"A1 forbidden axioms: {name}: {ax}" for name, ax in got.items()
              if not set(ax) <= ALLOWED]
    if errors:
        raise SystemExit("\n".join(errors))
    require(got == parse_baseline((CERT / "A1_AXIOMAS.txt").read_text(encoding="utf-8")),
            "Certified A1 fingerprints changed")
    a1_blobs = {
        "TratadoAnalisis/Foundations/FunctionSpace.lean": "3165cca23feda04ad41c74f89837fe414dc2da31",
        "TratadoAnalisis/Cauchy/RationalSequences.lean": "e8875fd6472a8b959e844d38a8e542defc36e508",
        "tests/CauchyA1.lean": "fb839817ed6cc89ab1c7adc7145a1898a2f30881",
    }
    for path, sha in a1_blobs.items():
        actual = subprocess.check_output(["git", "hash-object", "--no-filters", path], cwd=ROOT).decode("ascii").strip()
        require(actual == sha, f"Certified A1 source changed: {path}")
    print("PASS TA-LEAN-0011 A1: 20 new queries; 952 preserved; no new Choice or sorryAx", flush=True)

if __name__ == "__main__":
    main()
