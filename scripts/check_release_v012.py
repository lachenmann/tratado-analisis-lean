"""Verify the complete, frozen v0.1.2 source and axiom inventories."""
from collections import Counter
from hashlib import sha256
from pathlib import Path
import re
import subprocess
import sys
from check_audit import ROOT, parse_baseline, parse_log

CERT = ROOT / "certificates/v0.1.2"
PINS = {
    "certificates/v0.1.1/SHA256SUMS": "b2acf1ca4b0a31ae05284e55508f0204f07c663138e76644328bca11decf4282",
    "certificates/v0.1.2/SHA256SUMS": "b94479ffa0f7c35b5b0877167ea64a4c2178dfc1c2034d72499475998330bf91",
    "certificates/v0.1.2/AXIOMAS.txt": "603b2708f0707c4de16d2aad4689b6c25ef889b5739d211b179ca8e932157acf",
}
CHANGED = {"TratadoAnalisis.lean", "lakefile.toml"}
CONFIG = {"lean-toolchain", "lakefile.toml", "lake-manifest.json"}
GROUPS = [
    (ROOT / "certificates/TA-LEAN-0010/AXIOMAS.txt", 833),
    (CERT / "API_AXIOMAS.txt", 25),
    (CERT / "P01_AXIOMAS.txt", 22),
    (CERT / "P02_AXIOMAS.txt", 21),
    (CERT / "P03_AXIOMAS.txt", 29),
    (CERT / "P04_AXIOMAS.txt", 22),
]


def require(ok, message):
    if not ok:
        raise SystemExit(message)


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def manifest(path):
    out = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        m = re.fullmatch(r"([0-9a-fA-F]{64})  (.+)", line)
        require(m is not None, f"Invalid manifest row: {line}")
        value, name = m.groups()
        require(name not in out, f"Duplicate manifest path: {name}")
        require(not Path(name).is_absolute() and ".." not in Path(name).parts,
                f"Invalid manifest path: {name}")
        out[name] = value.lower()
    return out


def main():
    require(len(sys.argv) == 7,
            "Usage: python scripts/check_release_v012.py audit.log public-api.log prerequisites.log absolute-value.log completeness-equivalences.log numeral-arithmetic.log")
    for name, expected in PINS.items():
        require(digest(ROOT / name) == expected, f"Frozen certificate changed: {name}")
    old = manifest(ROOT / "certificates/v0.1.1/SHA256SUMS")
    new = manifest(CERT / "SHA256SUMS")
    require(len(old) == 150 and len(new) == 159, "Unexpected manifest counts")
    require(set(old) <= set(new), "Historical source missing")
    require({p for p in old if old[p] != new[p]} == CHANGED,
            "Unexpected change to historical sources")
    tracked = subprocess.check_output(["git", "ls-files", "-z"], cwd=ROOT).decode("utf-8").split("\0")
    expected = {p for p in tracked if p.endswith(".lean") or p in CONFIG}
    require(set(new) == expected, f"Manifest coverage mismatch: {set(new) ^ expected}")
    for name, value in sorted(new.items()):
        require(digest(ROOT / name) == value, f"Source hash mismatch: {name}")
    print("PASS v0.1.2: 159/159 source/config hashes; 148/150 historical files unchanged", flush=True)
    combined = {}
    for (reference, count), logfile in zip(GROUPS, sys.argv[1:]):
        ref = parse_baseline(reference.read_text(encoding="utf-8-sig"))
        got = parse_log(Path(logfile).read_text(encoding="utf-8-sig"))
        require(len(ref) == count and got == ref, f"Exact axiom regression: {reference.name}")
        require(not (set(combined) & set(ref)), f"Duplicate declaration group: {reference.name}")
        combined.update(got)
    frozen = parse_baseline((CERT / "AXIOMAS.txt").read_text(encoding="utf-8-sig"))
    require(len(combined) == 952 and combined == frozen, "Aggregate fingerprint regression")
    require(sum("Classical.choice" in ax for ax in combined.values()) == 65, "Choice count changed")
    require(not any("sorryAx" in ax for ax in combined.values()), "sorryAx detected")
    require(all(set(ax) <= {"Classical.choice", "propext", "Quot.sound"} for ax in combined.values()), "Unexpected axiom")
    for ax, count in sorted(Counter(combined.values()).items()):
        print(f"{','.join(ax) if ax else '<none>'}: {count}", flush=True)
    print("PASS-RELEASE-CANDIDATE-v0.1.2: 952/952 exact fingerprints; 65 historical Choice; zero sorryAx", flush=True)


if __name__ == "__main__":
    main()
