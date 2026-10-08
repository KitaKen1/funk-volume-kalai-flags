"""Build and audit the distributed proof targets, pins and generated sources."""
from pathlib import Path
from datetime import datetime, timezone
import argparse
import hashlib
import json
import re
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[2]
LEAN = ROOT / "lean"
EVIDENCE = LEAN / "evidence"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
ROOTS = [
    "Funk.symmetricFunk_lower_bound", "Funk.kalai_full_flags",
    "Funk.mem_polarIncidence", "Funk.isClosed_polarIncidence",
    "Funk.isClosed_translated_coordinatePolar", "Funk.polarIncidence_indicator_section",
    "Funk.measurable_polarVolume_kernel", "Funk.funkVolume_eq_polarIncidence_integral",
    "Funk.symmetricFunk_explicit", "Funk.symmetricFunk_metric_radius",
    "Funk.kalai_halfspace_full_flags", "Funk.translated_coordinatePolar_closure",
    "Funk.translated_coordinatePolar_interior", "Funk.funkVolume_open_body_eq",
    "FunkVolume.symmetricFunkVolume", "Funk.FormalConjectures.kalaiFullFlags",
]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def code_only(text):
    """Remove nested Lean comments and string literals before token scanning."""
    result, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end == -1 else end
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            result.append(" ")
        else:
            result.append(text[i])
            i += 1
    if depth:
        raise ValueError("Unclosed Lean comment")
    return "".join(result)


def check_sources():
    manifest = json.loads((EVIDENCE / "proof-sources.json").read_text())
    for relative, expected in manifest["sha256"].items():
        path = ROOT / relative
        if digest(path) != expected:
            raise ValueError(f"Source changed: {relative}")
        if path.suffix == ".lean":
            found = re.findall(r"\b(?:sorry|admit|axiom|unsafe|native_decide)\b", code_only(path.read_text()))
            if found:
                raise ValueError(f"Disallowed proof-source token in {relative}: {found}")
    upstream = json.loads((LEAN / "vendor/oai-mass/manifest.json").read_text())
    for item in upstream["modules"]:
        path = (LEAN / "vendor/oai-mass").joinpath(*item["module"].split(".")).with_suffix(".lean")
        if digest(path) != item["sha256"]:
            raise ValueError(f"Upstream source changed: {item['module']}")
    fc = json.loads((LEAN / "vendor/formal-conjectures/manifest.json").read_text())
    for item in fc["modules"]:
        path = (LEAN / "vendor/formal-conjectures").joinpath(*item["module"].split(".")).with_suffix(".lean")
        if digest(path) != item["sha256"]:
            raise ValueError(f"FC utility source changed: {item['module']}")
    subprocess.run(["python3", str(LEAN / "scripts/make_final_theorems.py"), "--check"], check=True)
    subprocess.run(["python3", str(LEAN / "scripts/make_lean4web.py"), "--check"], check=True)
    subprocess.run(["python3", str(LEAN / "scripts/make_lean4web.py"), "--edition", "pinned", "--check"], check=True)
    return len(manifest["sha256"]), upstream["count"]


def run(command, cwd, filename, stages):
    started = time.monotonic()
    with (EVIDENCE / filename).open("w") as log:
        result = subprocess.run(command, cwd=cwd, stdout=log, stderr=subprocess.STDOUT)
    stages.append({"command": command, "directory": cwd.relative_to(ROOT).as_posix(),
                   "log": filename, "exit_code": result.returncode,
                   "seconds": round(time.monotonic() - started, 3),
                   "log_sha256": digest(EVIDENCE / filename)})
    if result.returncode:
        raise RuntimeError(f"Command failed; see {EVIDENCE / filename}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--skip-build", action="store_true", help="Use already built modular libraries")
    parser.add_argument("--include-web", action="store_true", help="Also compile the complete standalone file")
    args = parser.parse_args()
    EVIDENCE.mkdir(exist_ok=True)
    stages = []
    count, vendor_count = check_sources()
    if not args.skip_build:
        run(["lake", "--wfail", "build"], LEAN, "package-build.log", stages)
        # The reference statements are built only for the separate-environment
        # type comparison; they are not dependencies of FinalTheorems.
        run(["lake", "--wfail", "build", "KalaiFullFlags", "SymmetricFunkVolume"],
            LEAN, "fc-statement-build.log", stages)
    source = "import Funk.OpenBodyConvention\nimport FinalTheorems\n\n#eval Lean.versionString\n"
    source += "example : Funk.FunkLowerBoundGoal := Funk.symmetricFunk_lower_bound\n"
    source += "example : Funk.KalaiFullFlagsGoal := Funk.kalai_full_flags\n"
    source += "\n".join(f"#check {name}\n#print axioms {name}" for name in ROOTS) + "\n"
    path = None
    try:
        with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", prefix="PackageAudit", dir=LEAN, delete=False) as handle:
            handle.write(source)
            path = Path(handle.name)
        run(["lake", "env", "lean", "-j1", "-Ewarning", path.name], LEAN, "package-axioms.log", stages)
    finally:
        if path:
            path.unlink(missing_ok=True)
    log = (EVIDENCE / "package-axioms.log").read_text()
    if '"4.34.1"' not in log:
        raise ValueError("Unexpected Lean toolchain version")
    matches = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log)
    axioms = {}
    for name, values in matches:
        used = {x.strip() for x in values.split(",") if x.strip()}
        if not used <= ALLOWED:
            raise ValueError(f"Unpermitted axioms in {name}: {used - ALLOWED}")
        axioms[name] = sorted(used)
    if set(axioms) != set(ROOTS):
        raise ValueError("Missing or unexpected axiom reports")
    run(["lake", "env", "lean", "-j1", "-Ewarning", "evidence/CheckFCTargets.lean"],
        LEAN, "fc-exact-targets.log", stages)
    fc_log = (EVIDENCE / "fc-exact-targets.log").read_text()
    if fc_log.count("Exact FC target type match:") != 2:
        raise ValueError("FC target type comparisons incomplete")
    web_map = json.loads((ROOT / "lean4web/source-map.json").read_text())
    if args.include_web:
        web = ROOT / "lean4web"
        run(["lake", "env", "lean", "-j1", "FunkKalaiLean4Web.lean"],
            web, "standalone-build.log", stages)
        web_log = (EVIDENCE / "standalone-build.log").read_text()
        if f'"{web_map["lean"]}"' not in web_log:
            raise ValueError("Unexpected standalone Lean toolchain version")
        if re.search(r": error:", web_log):
            raise ValueError("Standalone error diagnostic")
        web_reports = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", web_log)
        expected_web = set(ROOTS[:2] + ROOTS[-2:])
        if {name for name, _ in web_reports} != expected_web:
            raise ValueError("Standalone axiom reports incomplete")
        for name, values in web_reports:
            if not {x.strip() for x in values.split(",") if x.strip()} <= ALLOWED:
                raise ValueError(f"Standalone axiom failure: {name}")
    check_sources()
    record = {"format": 1, "status": "passed", "checked_at": datetime.now(timezone.utc).isoformat(),
              "lean": "4.34.1", "source_files_checked": count, "unchanged_upstream_modules": vendor_count,
              "exact_goal_type_checks": 2, "axioms": axioms, "executions": stages,
              "exact_fc_target_type_checks": 2, "fc_model_declaration_checks": 15,
              "ordinary_lean_compilation": True, "independent_kernel_replay_this_run": False,
              "standalone_compiled_this_run": args.include_web,
              "standalone_lean": web_map["lean"], "standalone_mathlib": web_map["mathlib"],
              "standalone_sha256": digest(ROOT / "lean4web/FunkKalaiLean4Web.lean"),
              "build_cache_scope": "Existing fixed-version artifacts may be reused; not a cold build.",
              "third_party_semantic_review_complete": False}
    (EVIDENCE / "package-audit.json").write_text(json.dumps(record, indent=2) + "\n")
    print(f"Audit passed: {count} source/config files, {vendor_count} upstream modules, {len(axioms)} axiom closures.")


if __name__ == "__main__":
    main()
