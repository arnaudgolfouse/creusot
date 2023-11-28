#!/usr/bin/python3

import sys
import subprocess
import shutil
import urllib.request
import platform
import os
from pathlib import Path

WHY3_PATH: Path
ALT_ERGO_PATH: Path
CVC4_PATH: Path
CVC5_PATH: Path
Z3_PATH: Path


def main(ci_dir: Path):
    global WHY3_PATH, ALT_ERGO_PATH, CVC4_PATH, CVC5_PATH, Z3_PATH
    check_environment()

    dependencies_dir = ci_dir.joinpath("dependencies")
    bin_dir = dependencies_dir.joinpath("bin")
    include_dir = dependencies_dir.joinpath("include")

    match platform.system():
        case "Linux" | "Darwin":
            WHY3_PATH = dependencies_dir.joinpath("_opam", "bin", "why3")
            ALT_ERGO_PATH = dependencies_dir.joinpath("_opam", "bin", "alt-ergo")
            CVC4_PATH = bin_dir.joinpath("cvc4")
            CVC5_PATH = bin_dir.joinpath("cvc5")
            Z3_PATH = bin_dir.joinpath("z3")
        case "Windows":
            WHY3_PATH = dependencies_dir.joinpath("_opam", "bin", "why3.exe")
            ALT_ERGO_PATH = dependencies_dir.joinpath("_opam", "bin", "alt-ergo.exe")
            CVC4_PATH = bin_dir.joinpath("cvc4.exe")
            CVC5_PATH = bin_dir.joinpath("cvc5.exe")
            Z3_PATH = bin_dir.joinpath("z3.exe")
        case other:
            raise RuntimeError(f"unsupported system: {other}")

    for dir in [dependencies_dir, bin_dir, include_dir]:
        dir.mkdir(exist_ok=True)

    dependencies_dir.joinpath(".gitignore").write_text("*")

    if not dependencies_dir.joinpath("_opam").exists():
        subprocess.check_call(
            args=["opam", "switch", "create", "."], cwd=dependencies_dir
        )

    install_why3(dependencies_dir)
    install_alt_ergo(dependencies_dir)
    install_cvc4()
    install_cvc5()
    install_z3(dependencies_dir, bin_dir, include_dir)

    shutil.copyfile(ci_dir.joinpath("why.conf"), dependencies_dir.joinpath("why3.conf"))
    for prover_name, prover_path in [
        ("Alt-Ergo", ALT_ERGO_PATH),
        ("CVC4", CVC4_PATH),
        ("CVC5", CVC5_PATH),
        ("Z3", Z3_PATH),
    ]:
        subprocess.check_call(
            args=[
                WHY3_PATH,
                "config",
                "add-prover",
                prover_name,
                prover_path,
                "-C",
                dependencies_dir.joinpath("why3.conf"),
            ]
        )


def check_environment():
    if platform.architecture()[0] != "64bit":
        raise RuntimeError(f"Unsupported architecture: {platform.architecture()[0]}")
    for cmd in ["opam"]:
        if shutil.which(cmd) is None:
            raise RuntimeError(
                f"ERROR: command {cmd} does not exists, please install it."
            )


# Pinned to https://gitlab.inria.fr/why3/why3.git
#
# Via opam
def install_why3(in_dir: Path):
    if WHY3_PATH.exists():
        return
    print("installing why3...")
    subprocess.check_call(
        args=[
            "opam",
            "pin",
            "add",
            "--yes",
            "why3",
            "https://gitlab.inria.fr/why3/why3.git",
        ],
        cwd=in_dir,
    )
    subprocess.check_call(
        args=[
            "opam",
            "pin",
            "add",
            "--yes",
            "why3-ide",
            "https://gitlab.inria.fr/why3/why3.git",
        ],
        cwd=in_dir,
    )
    subprocess.check_call(
        args=[
            "opam",
            "install",
            "--yes",
            "lablgtk3",
            "lablgtk3-sourceview3",
            "ocamlgraph",
            "why3",
            "why3-ide",
        ],
        cwd=in_dir,
    )


# Version 2.4.3
#
# Via opam
def install_alt_ergo(in_dir: Path):
    if ALT_ERGO_PATH.exists():
        return
    print("installing Alt-Ergo...")
    subprocess.check_call(
        args=[
            "opam",
            "install",
            "--yes",
            "alt-ergo.2.4.3",
        ],
        cwd=in_dir,
    )


# Version 1.8
#
# Direct download
def install_cvc4():
    if CVC4_PATH.exists():
        return
    print("installing cvc4...")
    url: str
    match platform.system():
        case "Linux":
            url = "https://github.com/CVC4/CVC4/releases/download/1.8/cvc4-1.8-x86_64-linux-opt"
        case "Darwin":
            url = (
                "https://github.com/CVC4/CVC4/releases/download/1.8/cvc4-1.8-macos-opt"
            )
        case "Windows":
            url = "https://github.com/CVC4/CVC4/releases/download/1.8/cvc4-1.8-win64-opt.exe"
        case other:
            raise RuntimeError(f"unsupported system: {other}")
    with urllib.request.urlopen(url) as response:
        cvc4 = response.read()
    open(CVC4_PATH, "wb").write(cvc4)
    os.chmod(CVC4_PATH, 0o700)


# Version 1.0.5
#
# Direct download
def install_cvc5():
    if CVC5_PATH.exists():
        return
    print("installing cvc5...")
    url: str
    match platform.system():
        case "Linux":
            url = "https://github.com/cvc5/cvc5/releases/download/cvc5-1.0.5/cvc5-Linux"
        case "Darwin":
            url = "https://github.com/cvc5/cvc5/releases/download/cvc5-1.0.5/cvc5-macOS"
        case "Windows":
            url = "https://github.com/cvc5/cvc5/releases/download/cvc5-1.0.5/cvc5-Win64.exe"
        case other:
            raise RuntimeError(f"unsupported system: {other}")
    with urllib.request.urlopen(url) as response:
        cvc5 = response.read()
    open(CVC5_PATH, "wb").write(cvc5)
    os.chmod(CVC5_PATH, 0o700)


# Version 4.12.1
#
# Direct download
def install_z3(in_dir: Path, bin_dir: Path, include_dir: Path):
    if Z3_PATH.exists():
        return
    print("installing Z3...")
    z3_archive: Path = in_dir.joinpath("z3-archive.zip")
    z3_data: Path = in_dir.joinpath("z3-data")
    url_base: str
    match platform.system():
        case "Linux":
            url_base = "z3-4.12.1-x64-glibc-2.35"
        case "Darwin":
            url_base = "z3-4.12.1-x64-osx-10.16"
        case "Windows":
            url_base = "z3-4.12.1-x64-win"
        case other:
            raise RuntimeError(f"unsupported system: {other}")
    url = f"https://github.com/Z3Prover/z3/releases/download/z3-4.12.1/{url_base}.zip"

    with urllib.request.urlopen(url) as response:
        z3_zip = response.read()
    open(z3_archive, "wb").write(z3_zip)
    shutil.unpack_archive(
        filename=z3_archive,
        extract_dir=z3_data,
    )
    z3_bin_dir = z3_data.joinpath(url_base, "bin")
    z3_include_dir = z3_data.joinpath(url_base, "include")
    for elem in os.listdir(z3_bin_dir):
        shutil.move(z3_bin_dir.joinpath(elem), bin_dir)
    for elem in os.listdir(z3_include_dir):
        shutil.move(z3_include_dir.joinpath(elem), include_dir)

    os.remove(z3_archive)
    shutil.rmtree(z3_data)
    os.chmod(Z3_PATH, 0o700)


if __name__ == "__main__":
    main(Path(sys.argv[0]).parent.absolute().resolve())
