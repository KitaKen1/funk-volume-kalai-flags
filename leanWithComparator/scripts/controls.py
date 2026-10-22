"""Exercise the same comparator and external checker on small valid/invalid exports."""
import json
import re
from common import HERE, ALLOWED, binaries, nanoda_config, run, save

TARGET = "FCControl.target"
MODEL = "FCControl.Subject"


def break_proof(source, destination):
    names = {0: ""}
    changed = 0
    with source.open() as src, destination.open("w") as dst:
        for line in src:
            item = json.loads(line)
            if "in" in item:
                value = item.get("str", item.get("num"))
                suffix = value.get("str", str(value.get("i")))
                prefix = names[value["pre"]]
                names[item["in"]] = prefix + ("." if prefix else "") + suffix
            if "thm" in item and names[item["thm"]["name"]] == TARGET:
                # A well-formed export whose proof is a proposition, not its proof.
                item["thm"]["value"] = item["thm"]["type"]
                line = json.dumps(item, separators=(",", ":")) + "\n"
                changed += 1
            dst.write(line)
    if changed != 1:
        raise ValueError("Failed to mutate exactly the intended theorem proof")


def execute(output):
    output.mkdir(parents=True, exist_ok=False)
    tools = binaries()
    roots = [TARGET, MODEL] + ALLOWED
    entries = {}
    for kind in ["Challenge", "Valid", "Sorry", "Axiom", "Weakened", "Type", "Missing"]:
        module = "Controls." + kind
        run(["lake", "build", module], log=output / (kind + "-build.log"))
        exported = output / (kind + ".ndjson")
        export_roots = roots if kind != "Missing" else [MODEL] + ALLOWED
        run(["lake", "env", tools["exporter"], module, "--", *export_roots],
            log=output / (kind + "-export.log"), stdout_file=exported)
    challenge = output / "Challenge.ndjson"
    for kind, expected in [
        ("Valid", None), ("Sorry", "Illegal axiom detected: 'sorryAx'"),
        ("Axiom", "Illegal axiom detected: 'FCControl.cheat'"),
        ("Weakened", "Const does not match"),
        ("Type", "theorem statement do not match"),
        ("Missing", "Const not found in solution"),
    ]:
        log = output / (kind + "-compare.log")
        receipt = run([tools["comparator"], challenge, output / (kind + ".ndjson"), TARGET, MODEL],
                      log=log, expect=None)
        text = log.read_text()
        if expected:
            if receipt["returncode"] == 0 or expected not in text:
                raise ValueError("Wrong rejection or unexpected acceptance: " + kind)
            entries[kind] = {"expected": "reject", "passed": True,
                             "stage": "comparator", "reason": expected, "execution": receipt}
        elif receipt["returncode"] != 0:
            raise ValueError("Positive comparator control failed: " + text)
    statements = output / "valid-statements.txt"
    config = output / "valid-nanoda.json"
    save(config, nanoda_config(output / "Valid.ndjson", statements, TARGET))
    receipt = run([tools["nanoda"], config], log=output / "valid-nanoda.log")
    if not re.fullmatch(r"Checked (\d+) declarations with no errors\s*",
                        (output / "valid-nanoda.log").read_text()) or TARGET not in statements.read_text():
        raise ValueError("Positive external-kernel control lacks expected success")
    entries["Valid"] = {"expected": "accept", "passed": True, "stage": "comparator+nanoda",
                        "nanoda_execution": receipt}
    broken = output / "Broken.ndjson"
    break_proof(output / "Valid.ndjson", broken)
    run([tools["comparator"], challenge, broken, TARGET, MODEL], log=output / "broken-compare.log")
    config = output / "broken-nanoda.json"
    save(config, nanoda_config(broken, output / "broken-statements.txt", TARGET))
    receipt = run([tools["nanoda"], config], log=output / "broken-nanoda.log", expect=None)
    if receipt["returncode"] == 0:
        raise ValueError("External checker accepted a malformed proof")
    entries["Broken"] = {"expected": "reject", "passed": True, "stage": "nanoda",
                         "mutation": "target proof replaced by its type expression",
                         "comparator_accepted": True, "execution": receipt}
    result = {"status": "passed", "fixture_target": TARGET, "cases": entries,
              "scope": "Small compiled fixtures, using the same driver, exporter, checker and axiom policy"}
    save(output / "result.json", result)
    return result
