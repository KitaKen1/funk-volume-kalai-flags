"""Generate a pinned, Mathlib-only file; preserve a scope per source module."""
from pathlib import Path
import argparse
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[2]
LEAN = ROOT / "lean"
WEB = ROOT / "lean4web"


def sha(data):
    return hashlib.sha256(data).hexdigest()


def generate(edition="live"):
    visited, active, sources, imports = set(), set(), [], set()
    live = edition == "live"
    compatibility = {
        "OAI.Analysis.Mahler.NormSquareJet": (
            '''      (((smulRightL ℝ E (E →L[ℝ] ℝ)).continuous.comp
        ((continuous_const (y := (2 : ℝ))).smul hpa)).clm_apply hpa)''',
            '''      ((isBoundedBilinearMap_smulRight (𝕜 := ℝ) (E := E)
        (F := E →L[ℝ] ℝ)).continuous.comp
          (((continuous_const (y := (2 : ℝ))).smul hpa).prodMk hpa))'''),
        "OAI.Analysis.Mahler.LogScalarJet": (
            '''      (((smulRightL ℝ E (E →L[ℝ] ℝ)).continuous.comp
        ((((hv.pow 2).inv₀ (fun q => pow_ne_zero _ (hn q))).neg).smul hpa)).clm_apply hpa)''',
            '''      ((isBoundedBilinearMap_smulRight (𝕜 := ℝ) (E := E)
        (F := E →L[ℝ] ℝ)).continuous.comp
          (((((hv.pow 2).inv₀ (fun q => pow_ne_zero _ (hn q))).neg).smul hpa).prodMk hpa))'''),
    }

    def resolve(module):
        if module == "FinalTheorems":
            return LEAN / "FinalTheorems.lean"
        if module.startswith("FormalConjecturesUtil."):
            return (LEAN / "vendor/formal-conjectures").joinpath(*module.split(".")).with_suffix(".lean")
        if module.startswith("Funk."):
            return LEAN.joinpath(*module.split(".")).with_suffix(".lean")
        if module.startswith("OAI."):
            return (LEAN / "vendor/oai-mass").joinpath(*module.split(".")).with_suffix(".lean")
        if module == "Mathlib" or module.startswith(("Mathlib.", "Lean.", "Batteries.")):
            return None
        raise ValueError(f"Unexpected import: {module}")

    def visit(module):
        if module in active:
            raise ValueError(f"Import cycle: {module}")
        if module in visited:
            return
        path = resolve(module)
        if path is None:
            imports.add(module)
            return
        active.add(module)
        text = path.read_text()
        for group in re.findall(r"^(?:public (?:meta )?)?import ([^\n]+)$", text, re.M):
            for dependency in group.split():
                # FC attributes are publication metadata, not part of the target type.
                if module == "FinalTheorems" and dependency == "FormalConjecturesUtil.Attributes.Basic":
                    continue
                # The core closure already imports every Mathlib definition used
                # by these targets; avoid requiring the optional umbrella artifact.
                if module == "FinalTheorems" and dependency == "Mathlib":
                    continue
                visit(dependency)
        body = re.sub(r"^(?:public (?:meta )?)?import [^\n]+\n", "", text, flags=re.M)
        body = re.sub(r"^module\n", "", body, flags=re.M)
        if module.startswith("FormalConjecturesUtil."):
            body = body.replace("public meta section", "meta section").replace("public section", "section")
            body += "\nend\n"
        if module == "FormalConjecturesUtil.Answer":
            # The default answer elaborator is unchanged. Reading a registered
            # option from its defining single file cannot evaluate its initializer.
            body = re.sub(r"register_option google.answer : AnswerSetting := \{.*?\n\}\n", "", body, flags=re.S)
            body = body.replace("match google.answer.get (← getOptions) with",
                                "match AnswerSetting.alwaysTrue with")
        if module == "FinalTheorems":
            body = body.replace("@[expose] public section", "")
            body = re.sub(r"@\[category research solved, AMS 52,\s*formal_proof using lean4 at \"[^\"]+\"\]\n", "", body)
            body = re.sub(r"^#(?:check|print axioms) .*\n", "", body, flags=re.M)
        body = body.strip()
        if live and module in compatibility:
            old, new = compatibility[module]
            if body.count(old) != 1:
                raise ValueError(f"Compatibility patch does not match once: {module}")
            body = body.replace(old, new)
        sources.append((path, module, body))
        active.remove(module)
        visited.add(module)

    # This independent branch must precede the homogeneous-flux branch:
    # in its original import closure, OAI.Mahler.sphereFlux is not visible.
    # Otherwise flattening resolves its unqualified sphereFlux references to
    # that later definition rather than the opened OAI.MahlerStokes.sphereFlux.
    # The branch is already in Funk.OpenBodyConvention's dependency closure. No proof edits.
    visit("OAI.Analysis.Mahler.SourceRegularMass")
    visit("Funk.OpenBodyConvention")
    visit("FinalTheorems")
    header = "\n".join("import " + m for m in sorted(imports)) + "\n\n"
    lean_version = "4.35.0-rc4" if live else "4.34.1"
    mathlib = "021ce68bf125a049beee22b3fc7664d78728e21d" if live else "d13f23b723b8a846827a245b89c10fc7d3f11612"
    header += (f'''/-!
# Symmetric Funk volume / Kalai full flags: complete single-file proof

Generated by ../lean/scripts/make_lean4web.py. Lean {lean_version}, Mathlib
{mathlib}. Only Mathlib imports are needed.
Every Funk and OAI dependency is included below. Original OAI code is
Apache-2.0; see ../lean/vendor/oai-mass/LICENSE and ../THIRD_PARTY.md.
Each source is placed in a section to restore its local notation and opens.
The last two theorems copy the FC definitions and target statements, with proofs.
FC placeholders are not imported. The official answer elaborator is included
with its default mode fixed to avoid a same-file option initializer.
The live edition ports two continuity proofs to a bounded-bilinear-map API.
Public Lean4Web projects change; use the exact versions given above.
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

#eval Lean.versionString
''' if live else '''/-!
# Symmetric Funk volume / Kalai full flags: complete single-file proof

Generated by ../lean/scripts/make_lean4web.py. Lean 4.34.1, Mathlib
d13f23b723b8a846827a245b89c10fc7d3f11612. Only Mathlib imports are needed.
Every Funk and OAI dependency is included below. Original OAI code is
Apache-2.0; see ../lean/vendor/oai-mass/LICENSE and ../THIRD_PARTY.md.
Each source is placed in a section to restore its local notation and opens.
The last two theorems copy the FC definitions and target statements, with proofs.
FC placeholders are not imported. The official answer elaborator is included
with its default mode fixed to avoid a same-file option initializer.
Local compilation does not certify the public Lean4Web server's version.
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

#eval Lean.versionString
''')
    content = header
    mapping = []
    for i, (path, module, body) in enumerate(sources):
        label = f"SourceScope{i:03d}"
        relative = path.relative_to(ROOT).as_posix()
        prefix = f"\n-- Source: {relative}\nsection {label}\n\n"
        start = len(content.splitlines()) + len(prefix.splitlines()) + 1
        content += prefix + body + f"\n\nend {label}\n"
        row = {"module": module, "source": relative,
               "source_sha256": sha(path.read_bytes()),
               "first_body_line": start, "body_lines": len(body.splitlines())}
        if live:
            row["compatibility_patch"] = ("bounded bilinear continuity of smulRight"
                                           if module in compatibility else None)
        if module == "FormalConjecturesUtil.Answer":
            row["tooling_adaptation"] = "Remove google.answer option registration; fix its original default AnswerSetting.alwaysTrue."
        if module == "FinalTheorems":
            row["tooling_adaptation"] = "Remove FC metadata attributes; preserve all geometric definitions, theorem types and proofs."
        mapping.append(row)
    content += '''
#check Funk.symmetricFunk_lower_bound
#check Funk.kalai_full_flags
#check Funk.symmetricFunk_metric_radius
#check Funk.kalai_halfspace_full_flags
#print axioms Funk.symmetricFunk_lower_bound
#print axioms Funk.kalai_full_flags
#check FunkVolume.symmetricFunkVolume
#print axioms FunkVolume.symmetricFunkVolume
#check Funk.FormalConjectures.kalaiFullFlags
#print axioms Funk.FormalConjectures.kalaiFullFlags
'''
    output = content.encode()
    info = {"format": 2, "edition": edition, "lean": lean_version,
            "mathlib": mathlib,
            "sources": mapping, "modules": len(mapping),
            "mathlib_imports": sorted(imports), "bytes": len(output),
            "lines": len(content.splitlines()), "sha256": sha(output),
            "transformation": "Remove imports/module visibility; dependency order; one section per source; default-mode FC answer elaboration and removal of FC metadata attributes; two continuity API ports in the live edition.",
            "compatibility_patches": ([{"module": module, "old": old, "new": new}
                                      for module, (old, new) in compatibility.items()] if live else [])}
    if not live:
        info = {"format": 1, "lean": lean_version, "mathlib": mathlib,
                "sources": mapping, "modules": len(mapping),
                "mathlib_imports": sorted(imports), "bytes": len(output),
                "lines": len(content.splitlines()), "sha256": sha(output),
                "transformation": "Remove imports/module visibility; dependency order; one section per source; default-mode FC answer elaboration and removal of FC metadata attributes. No mathematical proof edits."}
    return output, (json.dumps(info, indent=2, ensure_ascii=False) + "\n").encode()


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="Require byte-for-byte regeneration")
    parser.add_argument("--edition", choices=["live", "pinned"], default="live")
    args = parser.parse_args()
    code, manifest = generate(args.edition)
    destination = WEB if args.edition == "live" else WEB / "pinned-4.34.1"
    targets = [(destination / "FunkKalaiLean4Web.lean", code), (destination / "source-map.json", manifest)]
    for path, data in targets:
        if args.check:
            if path.read_bytes() != data:
                raise SystemExit(f"Generated file differs: {path}")
        else:
            path.write_bytes(data)
    print("Lean4Web file: " + ("regeneration matches" if args.check else "generated"))
