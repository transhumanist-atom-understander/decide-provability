#!/usr/bin/env python3
"""Build the tableau of a GL sentence read from stdin, with letters as sentence letters and
connectives → ∧ ∨ ¬ ↔ □ ◇ ⊥ ⊤ at their usual precedences:

    echo '□(□p → p) → □p' | ./gltableau.py          # as text
    echo '□(□p → p) → □p' | ./gltableau.py --tex    # as a prooftree
    echo '□(□p → p) → □p' | ./gltableau.py --lean   # as a ProvabilityLogic derivation
    echo '□(□p → p) → □p' | ./gltableau.py --verify # ... checked by Lean

Exits 0 if the tableau closes (the sentence is a theorem), 1 if not, 2 on a parse error;
--verify exits 0 only if Lean accepts the derivation.
"""
import subprocess, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parent / "ProvabilityLogic"


def tableau(sentence, *flags):
    """The output of `tableau` (built by `lake build` here) and whether the tableau closed."""
    p = subprocess.run([HERE / ".lake/build/bin/tableau", *flags], input=sentence,
                       capture_output=True, text=True)
    if p.returncode == 2:
        print(p.stderr, end="", file=sys.stderr)
        sys.exit(2)
    return p.stdout, p.returncode == 0


def text(sentence):
    return tableau(sentence)[0]


def tex(sentence):
    return tableau(sentence, "--tex")[0]


def lean(sentence):
    """A Lean file deriving `sentence` in ProvabilityLogic's labelled sequent calculus for GL,
    which Lean checks in that repo (`lake env lean`, so the repo must be built)."""
    return (HERE / "rules.lean").read_text() + tableau(sentence, "--lean")[0]


def verify(sentence):
    """Lean's verdict on `lean(sentence)`: `True` if it checks, else its messages."""
    p = subprocess.run(["lake", "env", "lean", "--stdin"], input=lean(sentence), cwd=REPO,
                       capture_output=True, text=True)
    return (p.stdout + p.stderr) or True


def main():
    sentence = sys.stdin.read().strip()
    flag = sys.argv[1] if sys.argv[1:] else ""
    if flag == "--verify":
        verdict = verify(sentence)
        print("verified" if verdict is True else verdict)
        sys.exit(verdict is not True)
    output, closed = tableau(sentence, *sys.argv[1:])
    print(output, end="")
    sys.exit(not closed)


if __name__ == "__main__":
    main()
