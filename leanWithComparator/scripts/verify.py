"""Fresh comparison and nanoda replay of the exact pinned FC final theorem."""
import argparse
import json
import os
import platform
import re
import shutil
import subprocess
from pathlib import Path
from common import (HERE, REPO, TOOLS, PINS, TARGET, ALLOWED, MODELS, ROOTS, binaries,
                    check_dependency_checkouts, digest, nanoda_config, now, run, save, source_check)
from make_challenge import generate
import controls


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=HERE / "evidence")
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    path = output / "result.json"
    result = {"status": "running", "started_at": now(), "target": TARGET,
              "permitted_axioms": ALLOWED, "definition_holes": [], "executions": {},
              "comparator": False, "independent_nanoda_replay": False, "negative_controls": False,
              "scope": {"mathlib_cache": "Trusted fixed-revision Mathlib cache may be used",
                        "proof_build_cache_hit": os.environ.get("FC_PROOF_CACHE_HIT") == "true",
                        "proof_build_cache_matched_key": os.environ.get("FC_PROOF_CACHE_MATCHED_KEY", ""),
                        "full_dependency_cold_build": False,
                        "landrun_pipeline": False, "adversarial_build_sandbox": False,
                        "independent_human_semantic_review": False},
              "environment": {"platform": platform.platform(), "architecture": platform.machine(),
                              "lean": PINS["lean"], "rust": PINS["rust"]}}
    if os.environ.get("GITHUB_ACTIONS") == "true":
        result["ci"] = {"repository": os.environ["GITHUB_REPOSITORY"],
                        "sha": os.environ["GITHUB_SHA"], "run_id": os.environ["GITHUB_RUN_ID"],
                        "run_attempt": os.environ["GITHUB_RUN_ATTEMPT"],
                        "url": os.environ["GITHUB_SERVER_URL"] + "/" + os.environ["GITHUB_REPOSITORY"]
                               + "/actions/runs/" + os.environ["GITHUB_RUN_ID"]}
    save(path, result)

    def stage(name, argv, cwd=HERE, stdout_file=None):
        result["current_stage"] = name
        save(path, result)
        print(json.dumps({"stage": name, "status": "started"}), flush=True)
        receipt = run(argv, cwd=cwd, log=output / (name + ".log"), stdout_file=stdout_file)
        result["executions"][name] = receipt
        save(path, result)
        print(json.dumps({"stage": name, "status": "passed", "seconds": receipt["seconds"]}), flush=True)
        return output / (name + ".log")

    try:
        result["inputs"] = source_check()
        result["challenge_generation"] = generate(check=True)
        check_dependency_checkouts()
        result["verification_git_sha"] = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=REPO, text=True).strip()
        tools_lock = json.loads((TOOLS / "tools-lock.json").read_text())
        if tools_lock["status"] != "passed":
            raise ValueError("Tools have no successful fresh build receipt")
        for name, binary in binaries().items():
            if digest(binary) != tools_lock["binaries"][name]["sha256"]:
                raise ValueError("Tool binary differs from build receipt: " + name)
        shutil.copy2(TOOLS / "tools-lock.json", output / "tools-lock.json")
        shutil.copytree(TOOLS / "logs", output / "tool-build-logs")
        stage("challenge-build", ["lake", "--wfail", "build", "ChallengeFC", "RawPRFC"])
        # Freeze challenge export BEFORE compiling the solution modules.
        stage("challenge-export", ["lake", "env", binaries()["exporter"], "ChallengeFC", "--", *ROOTS],
              stdout_file=output / "challenge.ndjson")
        stage("solution-build", ["lake", "--wfail", "build", "SolutionFC", "AuditFC", "ModelAuditFC"])
        model_log = stage("raw-pr-model-agreement", ["lake", "env", "lean", "-j1", "-Ewarning", "ModelAuditFC.lean"])
        if "Exact raw PR model/target agreement: 12 declarations" not in model_log.read_text():
            raise ValueError("Raw PR interface agreement was not confirmed")
        result["raw_pr_model_target_agreement"] = True
        axiom_log = stage("axioms", ["lake", "env", "lean", "-j1", "-Ewarning", "AuditFC.lean"])
        reports = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", axiom_log.read_text())
        if len(reports) != 1 or reports[0][0] != TARGET:
            raise ValueError("Missing exact final-target axiom report")
        used = sorted(x.strip() for x in reports[0][1].split(",") if x.strip())
        if not set(used) <= set(ALLOWED):
            raise ValueError("Unpermitted final-target axioms: " + str(used))
        result["reported_axioms"] = used
        stage("solution-export", ["lake", "env", binaries()["exporter"], "SolutionFC", "--", *ROOTS],
              stdout_file=output / "solution.ndjson")
        with (output / "challenge.ndjson").open() as h:
            challenge_meta = json.loads(next(h))["meta"]
        with (output / "solution.ndjson").open() as h:
            solution_meta = json.loads(next(h))["meta"]
        if challenge_meta != solution_meta:
            raise ValueError("Different export metadata/toolchains")
        result["export_meta"] = solution_meta
        stage("comparator", [binaries()["comparator"], output / "challenge.ndjson",
                             output / "solution.ndjson", TARGET, *MODELS])
        result["comparator"] = True
        result["compared_model_roots"] = MODELS
        save(path, result)
        config = output / "nanoda-config.json"
        statements = output / "checked-statements.txt"
        save(config, nanoda_config(output / "solution.ndjson", statements))
        log = stage("nanoda", [binaries()["nanoda"], config])
        success = re.fullmatch(r"Checked (\d+) declarations with no errors\s*", log.read_text())
        if not success or TARGET not in statements.read_text():
            raise ValueError("Independent checker lacks success and exact target output")
        result.update(independent_nanoda_replay=True, checked_declarations=int(success[1]))
        save(path, result)
        print(json.dumps({"stage": "negative-controls", "status": "started"}), flush=True)
        result["current_stage"] = "negative-controls"
        save(path, result)
        result["controls"] = controls.execute(output / "controls")
        result["negative_controls"] = True
        if source_check() != result["inputs"]:
            raise ValueError("Inputs changed during verification")
        check_dependency_checkouts()
        result["evidence_sha256"] = {p.relative_to(output).as_posix(): digest(p)
            for p in output.rglob("*") if p.is_file() and p != path and not p.name.endswith(".tmp")}
        result.update(status="passed", finished_at=now(), current_stage="complete")
        save(path, result)
        print(json.dumps({"status": "passed", "target": TARGET,
                          "checked_declarations": result["checked_declarations"],
                          "reported_axioms": used}), flush=True)
    except Exception as error:
        result.update(status="failed", error=str(error), finished_at=now())
        save(path, result)
        raise


if __name__ == "__main__":
    main()
