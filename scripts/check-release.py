"""Check pinned dependencies or validate the fresh Lean audit output."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
NAMESPACE = "OddZetaSix.B40a."
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
AUDITED = (
    "exists_irrational_riemannZeta_seven_to_fifteen",
    "content_arithmetic_exp",
    "determinant_analytic_rate",
    "rational_det_valuation",
    "small_prime_cost_rate",
    "high_prime_cost_rate",
)

def check_audit(path):
    output = path.read_text(encoding="utf-8")
    for name in AUDITED:
        pattern = r"'" + re.escape(NAMESPACE + name) + r"' depends on axioms:\s*\[([^\]]*)\]"
        hits = re.findall(pattern, output)
        if len(hits) != 1:
            raise SystemExit(f"Missing or duplicate audit entry for {name}")
        actual = {item.strip() for item in hits[0].split(",")}
        if actual != STANDARD:
            raise SystemExit(f"{name} dependencies changed: {sorted(actual)}")
        print(f"{name}: exact dependency set verified")

def verify_tracked_lean(path):
    """Compare actual Lean source bytes to the pinned Git tree, including stat-clean paths."""
    tree = subprocess.check_output(["git", "-C", str(path), "ls-tree", "-rz", "HEAD"])
    count = 0
    for entry in tree.split(b"\0"):
        if not entry:
            continue
        header, name = entry.split(b"\t", 1)
        if not name.endswith(b".lean"):
            continue
        mode, kind, expected = header.split()
        if kind != b"blob" or mode not in (b"100644", b"100755"):
            raise SystemExit(f"Unexpected source type: {name!r}")
        data = (path / name.decode("utf-8")).read_bytes()
        def blob_id(contents):
            header = b"blob " + str(len(contents)).encode("ascii") + b"\0"
            return hashlib.sha1(header + contents).hexdigest().encode("ascii")
        if blob_id(data) != expected and blob_id(data.replace(b"\r\n",b"\n")) != expected:
            raise SystemExit(f"Source blob mismatch: {name!r}")
        count += 1
    return count


def check_sources():
    manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
    for package in manifest["packages"]:
        if package["type"] != "git":
            continue
        path = ROOT / ".lake/packages" / package["name"]
        def git(*args):
            return subprocess.check_output(["git","-C",str(path),*args],text=True).strip()
        head = git("rev-parse","HEAD")
        status = git("status","--porcelain","--untracked-files=all")
        if head != package["rev"] or status:
            raise SystemExit(f"Unexpected checkout: {package['name']} {head} {status}")
        checked = verify_tracked_lean(path)
        print(f"{package['name']} {head} clean; {checked} tracked Lean source blobs matched")
    vendor = ROOT / "PNTDependency"
    provenance = json.loads((vendor/"provenance.json").read_text(encoding="utf-8"))
    for item in provenance["modules"]:
        data = (vendor/item["path"]).read_bytes()
        # Git source hashes refer to LF text on all platforms.
        digest = hashlib.sha256(data.replace(b"\r\n",b"\n")).hexdigest()
        if digest != item["sha256"]:
            raise SystemExit(f"Vendored source mismatch: {item['path']}")
    print(f"{len(provenance['modules'])} vendored module hashes verified")

def cache_roots():
    """Direct upstream imports from all release sources and the local PNT package."""
    roots = set()
    for directory in (ROOT/"OddZetaSix", ROOT/"PNTDependency/src"):
        for source in directory.rglob("*.lean"):
            for line in source.read_text(encoding="utf-8").splitlines():
                match = re.match(r"^(?:public )?import\s+(.*)$", line)
                if match:
                    for name in match.group(1).split("--",1)[0].split():
                        if name.split(".")[0] in {"Mathlib", "Batteries", "Aesop", "Qq"}:
                            roots.add(name)
    if not roots:
        raise SystemExit("No cache roots found")
    print("\n".join(sorted(roots)))

if __name__ == "__main__":
    if sys.argv[1:] == ["sources"]:
        check_sources()
    elif sys.argv[1:] == ["cache-roots"]:
        cache_roots()
    elif len(sys.argv)==3 and sys.argv[1]=="audit":
        check_audit(Path(sys.argv[2]))
    else:
        raise SystemExit("Use 'sources', 'cache-roots', or 'audit PATH'.")
