"""Only replace the PR module header/imports; keep its namespace body verbatim."""
import argparse
import hashlib
from common import HERE, save, source_check


def generate(check=False):
    source_check()
    raw = (HERE / "reference/KalaiFullFlags.pr.lean").read_text()
    marker = "namespace Funk.FormalConjectures\n"
    if raw.count(marker) != 1 or raw.count("  sorry\n") != 1:
        raise ValueError("Unexpected PR source layout")
    body = raw[raw.index(marker):]
    prefix = ("-- Generated from the pinned PR snapshot. Mathematical body is verbatim.\n"
              "import Mathlib\n"
              "import FormalConjecturesUtil.Answer\n"
              "import FormalConjecturesUtil.Attributes.Basic\n\n")
    # Full Mathlib offers two definitionally equal PartialOrder dictionaries.
    # Align synthesis with the pinned proof's narrower import closure. The raw
    # variant remains untouched and ModelAuditFC checks all model/target types
    # and definition values against that raw compiled interface.
    setting = ("-- Match the proof's instance path; checked against RawPRFC by ModelAuditFC.\n"
               "attribute [-instance] CompletePartialOrder.toPartialOrder\n\n")
    for name, output in [("RawPRFC.lean", prefix + body),
                         ("ChallengeFC.lean", prefix + setting + body)]:
        path = HERE / name
        if check:
            if path.read_text() != output:
                raise ValueError("Generated reference does not match the actual PR: " + name)
        else:
            path.write_text(output)
    return {"namespace_body_verbatim": True,
            "namespace_body_sha256": hashlib.sha256(body.encode()).hexdigest(),
            "changes": ["replace module/public import/public section wrapper with 4.34.1 imports",
                        "Challenge only: disable redundant CompletePartialOrder.toPartialOrder instance path"],
            "raw_pr_variant": "RawPRFC.lean, without instance-path alignment",
            "answer": "answer(True), unchanged", "placeholder": "one intentional Challenge sorry"}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    print(generate(args.check))
