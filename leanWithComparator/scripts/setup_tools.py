"""Build immutable tool sources; do not use historical Mac binaries."""
import json
import os
import platform
import subprocess
from common import HERE, TOOLS, PINS, binaries, digest, now, run, save


def main():
    TOOLS.mkdir(exist_ok=True)
    logdir = TOOLS / "logs"
    logdir.mkdir(exist_ok=True)
    record = {"status": "running", "started_at": now(), "tools": {}, "executions": []}
    result = TOOLS / "tools-lock.json"
    save(result, record)
    try:
        for name, pin in PINS["tools"].items():
            path = TOOLS / name
            if not path.exists():
                path.mkdir()
                run(["git", "init", str(path)])
                run(["git", "remote", "add", "origin", pin["repository"]], cwd=path)
                run(["git", "fetch", "--depth", "1", "origin", pin["commit"]], cwd=path)
                run(["git", "checkout", "--detach", "FETCH_HEAD"], cwd=path)
            commit = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=path, text=True).strip()
            if commit != pin["commit"]:
                raise ValueError("Wrong tool revision: " + name)
            if subprocess.check_output(["git", "status", "--porcelain", "--untracked-files=no"], cwd=path):
                raise ValueError("Tracked tool source changed: " + name)
            record["tools"][name] = dict(pin, actual_commit=commit)
        for name, command, cwd in [
            ("exporter", ["lake", "build"], TOOLS / "lean4export"),
            ("nanoda", ["cargo", "+" + PINS["rust"], "build", "--release", "--locked", "--jobs", "2"], TOOLS / "nanoda"),
            ("nanoda-tests", ["cargo", "+" + PINS["rust"], "test", "--release", "--locked", "--lib", "--jobs", "2"], TOOLS / "nanoda"),
            ("driver", ["lake", "build"], HERE / "compare-driver"),
        ]:
            record["executions"].append(run(command, cwd=cwd, log=logdir / (name + ".log")))
            save(result, record)
        record.update(status="passed", finished_at=now(), platform=platform.platform(),
                      architecture=platform.machine(), lean=PINS["lean"], rust=PINS["rust"],
                      binaries={k: {"path": str(v), "sha256": digest(v)} for k, v in binaries().items()})
        save(result, record)
        print(json.dumps({"tools": "passed", "binaries": record["binaries"]}), flush=True)
    except Exception as error:
        record.update(status="failed", error=str(error), finished_at=now())
        save(result, record)
        raise


if __name__ == "__main__":
    main()
