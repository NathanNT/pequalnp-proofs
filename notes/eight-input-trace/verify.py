from pathlib import Path
import os
import shutil
import subprocess
import sys
import tempfile

notes = Path(__file__).resolve().parent
project = Path(sys.argv[1]).resolve()
toolchain = Path(sys.argv[2]).resolve()
cache = project / ".lake/build/lib/lean"
source = notes.parent.parent / "lean"
blob = "984c51fe7a9a80a63838582fe3f8746a7fef7154"
prior = subprocess.check_output(["git", "-C", sys.argv[3], "cat-file", "blob", blob])
actual = subprocess.check_output(["git", "hash-object", "--stdin"], input=prior).decode().strip()
if actual != blob:
    raise ValueError("Le blob importé diffère de la source acceptée dans #8718")
specs = [
    ("PEqualNP.Outside.L_meta_4628", source / "PEqualNP/Outside/L_meta_4628.lean", "statement.txt"),
    ("PEqualNP.Outside.L_meta_3676", prior, None),
    ("PEqualNP.Research.Prior4628", notes / "Prior4628.lean", "statement.txt"),
]

with tempfile.TemporaryDirectory(prefix="pnp-recherche-") as directory:
    build = Path(directory)
    (build / "PEqualNP").mkdir()
    shutil.copytree(cache / "PEqualNP/Defs", build / "PEqualNP/Defs")
    shutil.copy2(cache / "PEqualNP/Defs.olean", build / "PEqualNP")
    libraries = [build, cache, *(p / ".lake/build/lib/lean"
                 for p in sorted((project / ".lake/packages").iterdir()) if p.is_dir())]
    env = dict(os.environ, LEAN_SYSROOT=str(toolchain), LEAN_NUM_THREADS="2",
               LEAN_PATH=os.pathsep.join(map(str,libraries)),
               PATH=str(toolchain/"bin") + os.pathsep + os.environ["PATH"])
    ext = ".exe" if os.name == "nt" else ""
    for module, content, statement in specs:
        rel = Path(*module.split(".")).with_suffix(".lean")
        (build / rel.parent).mkdir(parents=True, exist_ok=True)
        (build / rel).write_bytes(content if isinstance(content, bytes) else content.read_bytes())
        subprocess.run([toolchain / "bin" / ("lean"+ext), "-o", rel.with_suffix(".olean"), rel],
                       cwd=build, env=env, check=True)
        if statement:
            subprocess.run([project / ".lake/build/bin" / ("checklemma"+ext),
                            module, notes / statement, "check"], cwd=build, env=env, check=True)

