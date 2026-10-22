"""Small, fail-closed execution and provenance helpers."""
import datetime
import hashlib
import json
import os
import subprocess
import time
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
REPO = HERE.parent
PINS = json.loads((HERE / "pins.json").read_text())
TARGET = PINS["target"]
ALLOWED = PINS["permitted_axioms"]
MODELS = PINS["model_roots"]
ROOTS = [TARGET] + MODELS + ALLOWED
TOOLS = HERE / ".tools"


def digest(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def save(path, data):
    path = Path(path)
    temp = path.with_suffix(path.suffix + ".tmp")
    temp.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n")
    temp.replace(path)


def run(argv, cwd=HERE, log=None, stdout_file=None, expect=0, env=None):
    argv = [str(a) for a in argv]
    started = time.monotonic()
    merged = dict(os.environ)
    merged["ELAN_TOOLCHAIN"] = PINS["lean"]
    merged["PATH"] = str(Path.home() / ".elan/bin") + os.pathsep + merged.get("PATH", "")
    if env:
        merged.update(env)
    if log:
        Path(log).parent.mkdir(parents=True, exist_ok=True)
        with Path(log).open("wb") as errors:
            if stdout_file:
                with Path(stdout_file).open("wb") as output:
                    result = subprocess.run(argv, cwd=cwd, env=merged, stdout=output, stderr=errors)
            else:
                result = subprocess.run(argv, cwd=cwd, env=merged, stdout=errors, stderr=subprocess.STDOUT)
    else:
        result = subprocess.run(argv, cwd=cwd, env=merged)
    receipt = {"argv": argv, "cwd": str(cwd), "returncode": result.returncode,
               "seconds": round(time.monotonic() - started, 3)}
    if log:
        receipt.update(log=str(log), log_sha256=digest(log))
    if expect is not None and result.returncode != expect:
        tail = Path(log).read_text(errors="replace")[-6000:] if log else ""
        raise RuntimeError(f"Command returned {result.returncode}: {argv}\n{tail}")
    return receipt


def binaries():
    return {
        "exporter": TOOLS / "lean4export/.lake/build/bin/lean4export",
        "nanoda": TOOLS / "nanoda/target/release/nanoda_bin",
        "comparator": HERE / "compare-driver/.lake/build/bin/fccompare",
    }


def source_check():
    record = json.loads((HERE / "reference/proof-source-lock.json").read_text())
    for name, expected in record["sha256"].items():
        if digest(REPO / name) != expected:
            raise ValueError("Pinned proof source changed: " + name)
    expected_lean = {p for p in record["sha256"] if p.endswith(".lean")}
    actual_lean = {p.relative_to(REPO).as_posix() for root in ["lean", "FClikelean"]
                   for p in (REPO / root).rglob("*.lean") if ".lake" not in p.parts}
    if expected_lean != actual_lean:
        raise ValueError("Unexpected or missing proof Lean sources")
    reference = json.loads((HERE / "reference/source.json").read_text())
    raw = (HERE / "reference/KalaiFullFlags.pr.lean").read_bytes()
    blob = hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()
    if hashlib.sha256(raw).hexdigest() != reference["sha256"] or blob != reference["git_blob"]:
        raise ValueError("PR statement snapshot changed")
    if (HERE / "lean-toolchain").read_text().strip() != PINS["lean"]:
        raise ValueError("Unexpected Lean version")
    original = json.loads((REPO / "lean/lake-manifest.json").read_text())
    manifest = json.loads((HERE / "lake-manifest.json").read_text())
    expected = {p["name"]: p["rev"] for p in original["packages"]}
    actual = {p["name"]: p["rev"] for p in manifest["packages"] if p["type"] == "git"}
    if expected != actual:
        raise ValueError("Verification dependencies differ from proof manifest")
    return {"proof_commit": record["commit"], "proof_files": len(record["sha256"]),
            "proof_lock_sha256": digest(HERE / "reference/proof-source-lock.json"),
            "pr_statement": reference, "dependency_revisions": actual,
            "publication_metadata": record.get("publication_metadata", {})}


def check_dependency_checkouts():
    manifest = json.loads((HERE / "lake-manifest.json").read_text())
    for package in manifest["packages"]:
        if package["type"] != "git":
            continue
        path = HERE / ".lake/packages" / package["name"]
        actual = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=path, text=True).strip()
        if actual != package["rev"]:
            raise ValueError("Dependency checkout changed: " + package["name"])


def nanoda_config(export, statements, target=TARGET):
    # This pinned nanoda opens the pretty-printer destination without creating
    # it. Start with a fresh empty file so missing output is never inherited.
    statements = Path(statements).resolve()
    statements.parent.mkdir(parents=True, exist_ok=True)
    statements.write_text("")
    return {"export_file_path": str(Path(export).resolve()), "use_stdin": False,
            "permitted_axioms": ALLOWED, "unpermitted_axiom_hard_error": True,
            "unsafe_permit_all_axioms": False, "num_threads": 2,
            "nat_extension": True, "string_extension": True,
            "pp_declars": [target], "unknown_pp_declar_hard_error": True,
            "pp_output_path": str(Path(statements).resolve()), "pp_to_stdout": False,
            "print_success_message": True, "print_axioms": True}
