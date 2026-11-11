# Coth sums and Barnes integrals in Lean

This project proves the case with denominator `n^5` of the Gamma-function
Mellin--Barnes integral formula for the hyperbolic-cotangent sum.
The theorem is `coth_fifth_power_barnes_integral` in `MainTheorem.lean`.
That short file displays the complete statement, including the explicit real
integral, and refers to the proof in `CothSums/Evaluation.lean`.
The mathematical definitions are in `CothSums/Definitions.lean`.

The accompanying paper is *Mellin-Barnes integrals of Gamma functions for the sums of coth(pi n)/n^(4m+1), and a hypergeometric evaluation for m = 1*, concept DOI
`10.5281/zenodo.24128140`.
This project treats the fifth-power case only.

## Versions

- Bundle: 1.0.0.
- Lean: `leanprover/lean4:v4.33.0`.
- Mathlib: `db584cd6d46c92f209a44c0f1c829460d327499d`.

The toolchain and dependency commit are fixed by `lean-toolchain`,
`lakefile.toml`, and `lake-manifest.json`.

## Check the proof

Install the specified Lean toolchain with elan. From the project root, run:

```sh
lake --keep-toolchain exe cache get
lake --keep-toolchain build
lake --keep-toolchain env lean MainTheorem.lean
```

The first command supplies the pinned dependencies and their precompiled files;
Internet access is needed if they are not already present.
The final command prints:

```text
'coth_fifth_power_barnes_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Reuse an existing local Mathlib build

An existing checkout at the exact commit above, together with its matching Lean
build and dependencies, can be used without downloading another copy.
Set `MATHLIB_DIR` to that checkout. The following commands require Python 3 and
Git and leave the recorded dependency manifest unchanged:

```sh
export MATHLIB_DIR=/path/to/mathlib4
python3 - <<'PY'
import json
import os
import pathlib
import subprocess

root = pathlib.Path(os.environ["MATHLIB_DIR"]).resolve()
pin = "db584cd6d46c92f209a44c0f1c829460d327499d"
assert subprocess.check_output(
    ["git", "-C", str(root), "rev-parse", "HEAD"], text=True
).strip() == pin
manifest = json.loads(pathlib.Path("lake-manifest.json").read_text())
entries = []
for package in manifest["packages"]:
    name = package["name"]
    if name == "mathlib":
        directory = root
    else:
        directory = root / ".lake" / "packages" / name
        if not directory.is_dir():
            directory = root.parent / name
    if not directory.is_dir():
        raise SystemExit("Missing local dependency: " + name)
    if package["type"] == "git":
        revision = subprocess.check_output(
            ["git", "-C", str(directory), "rev-parse", "HEAD"], text=True
        ).strip()
        if revision != package["rev"]:
            raise SystemExit("Wrong local dependency revision: " + name)
    entries.append({
        "name": name,
        "type": "path",
        "dir": str(directory),
        "scope": package.get("scope", ""),
        "inherited": package["inherited"],
        "configFile": package["configFile"],
        "manifestFile": package["manifestFile"],
    })
pathlib.Path("local-packages.json").write_text(json.dumps({"schemaVersion": "1.2.0", "packages": entries}, indent=2) + "\n")
PY
lake --keep-toolchain --no-cache --packages=local-packages.json build
lake --keep-toolchain --no-cache --packages=local-packages.json env lean MainTheorem.lean
```

Here `local-packages.json` is only a local path selection; it is not part of the
source archive. The axiom output is the same as above.
The formal result relies on the Lean kernel, the pinned Mathlib, and the stated
mathematical definitions. There are no additional axioms or incomplete proofs.

## License

MIT; see `LICENSE`. Dependencies retain their respective licenses.

Assisted by AI.
