"""Verify the immutable historical audit and the separate v0.1.1 public API."""
from pathlib import Path
from hashlib import sha256
import sys
from check_audit import ROOT, BASE, AUDIT, ALLOWED, parse_baseline, parse_log

CERT = ROOT / "certificates/v0.1.1"
BRIDGE = "TratadoAnalisis.Dedekind.isPositiveCut_iff_strictFromLe"
HISTORICAL = {
    "TratadoAnalisis/Audit.lean": "d9efc1b495c02371cfe5b55a8f13f87842b91a772a47a6b779352baa1357f20c",
    "certificates/TA-LEAN-0010/SHA256SUMS": "70c86f483ba75671dc695f5ae834d255e94aee357ff7932736885f188007fea6",
    "certificates/TA-LEAN-0010/AXIOMAS.txt": "ac6c676c2d9c3246123eb84e2da348b8c4df2bf43e059f4735bcafde865c5dc2",
    "certificates/TA-LEAN-0010/README.md": "49810d0d33a8be0d2a9bd6c9ec5696299fcde282ef562fb751561340a63accef",
}

def require(condition, message):
    if not condition:
        raise SystemExit(message)

def main():
    if len(sys.argv) != 3:
        raise SystemExit("Usage: python scripts/check_public_api.py audit.log public-api.log")
    for path, expected in HISTORICAL.items():
        require(sha256((ROOT / path).read_bytes()).hexdigest() == expected,
                f"Historical file changed: {path}")
    base = parse_baseline(BASE.read_text(encoding="utf-8-sig"))
    old = parse_log(Path(sys.argv[1]).read_text(encoding="utf-8-sig"))
    require(len(base) == 833 and old == base, "Historical 833 fingerprints changed")
    pairs = [tuple(row.split("\t")) for row in (CERT / "API_ALIASES.tsv").read_text(encoding="utf-8").splitlines()]
    aliases = dict(pairs)
    require(len(pairs) == len(aliases) == 24, "Expected 24 unique aliases")
    new = parse_log(Path(sys.argv[2]).read_text(encoding="utf-8-sig"))
    require(set(new) == set(aliases) | {BRIDGE}, "Unexpected API declarations or missing queries")
    for name, target in aliases.items():
        require(target in base and new[name] == base[target], f"Alias footprint mismatch: {name}")
    require(set(new[BRIDGE]) <= ALLOWED, "Unexpected axioms for positivity bridge")
    require(not any("sorryAx" in ax or "Classical.choice" in ax for ax in new.values()),
            "Forbidden axiom in public API")
    print("PASS: 833 historical fingerprints; 24 aliases match their originals")
    print(f"PASS: positivity bridge {new[BRIDGE]}; 25 separate API queries; no new Choice or sorryAx")

if __name__ == "__main__":
    main()
