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
specs = []
names = [
    ("Outside.L_meta_2668", None),
    ("Research.SensitiveProjection", "4051/sensitive-statement.txt"),
    ("Research.RawReaderBound", "4051/raw-statement.txt"),
    ("Research.PairOrDecoder", "4051/pair-or-statement.txt"),
    ("Research.HeawoodExtensions", "4781/heawood-statement.txt"),
    ("Research.HeawoodSupport", "4781/heawood-support-statement.txt"),
    ("Research.BoundaryDominance", "3754/dominance-statement.txt"),
]
for name, statement in names:
    mod = "PEqualNP." + name
    specs.append((mod, source / Path(*mod.split(".")).with_suffix(".lean"), statement))

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

