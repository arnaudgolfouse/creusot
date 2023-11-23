#!/bin/sh

# The script auto-install all required provers locally, and sets up a corresponding why3 configuration file.

# Setup
THIS_SCRIPT_PATH=$(dirname "$0")
THIS_SCRIPT_PATH=$(realpath $THIS_SCRIPT_PATH)
mkdir -p $THIS_SCRIPT_PATH/dependencies
mkdir -p $THIS_SCRIPT_PATH/dependencies/bin/
mkdir -p $THIS_SCRIPT_PATH/dependencies/include/

cd $THIS_SCRIPT_PATH/dependencies/

echo '*' > .gitignore

# Why3
if [ ! -f "./_opam/bin/why3" ]; then
	opam switch create ./
	opam pin add --yes why3 https://gitlab.inria.fr/why3/why3.git
	opam pin add --yes why3-ide https://gitlab.inria.fr/why3/why3.git
	opam install --yes lablgtk3 lablgtk3-sourceview3 ocamlgraph why3 why3-ide
fi

# Alt-Ergo
if [ ! -f "./_opam/bin/alt-ergo" ]; then
	opam install --yes alt-ergo.2.4.3
fi

# CVC4
if [ ! -f "./bin/cvc4" ]; then
	wget https://github.com/CVC4/CVC4/releases/download/1.8/cvc4-1.8-x86_64-linux-opt
	mv ./cvc4-1.8-x86_64-linux-opt ./bin/cvc4
	chmod +x ./bin/cvc4
fi

# CVC5
if [ ! -f "./bin/cvc5" ]; then
	wget https://github.com/cvc5/cvc5/releases/download/cvc5-1.0.5/cvc5-Linux
	mv ./cvc5-Linux ./bin/cvc5
	chmod +x ./bin/cvc5
fi

# Z3
if [ ! -f "./z3-4.12.1-x64-glibc-2.35.zip" ]; then
	wget https://github.com/Z3Prover/z3/releases/download/z3-4.12.1/z3-4.12.1-x64-glibc-2.35.zip
	unzip z3-4.12.1-x64-glibc-2.35.zip
	mv z3-4.12.1-x64-glibc-2.35/bin/* ./bin/
	mv z3-4.12.1-x64-glibc-2.35/include/* ./include/
	chmod +x ./bin/z3
fi

# Add prover paths to the config
cp ../why.conf ./why3.conf
./_opam/bin/why3 config add-prover Alt-Ergo $THIS_SCRIPT_PATH/dependencies/_opam/bin/alt-ergo -C ./why3.conf
./_opam/bin/why3 config add-prover CVC4 $THIS_SCRIPT_PATH/dependencies/bin/cvc4 -C ./why3.conf
./_opam/bin/why3 config add-prover CVC5 $THIS_SCRIPT_PATH/dependencies/bin/cvc5 -C ./why3.conf
./_opam/bin/why3 config add-prover Z3 $THIS_SCRIPT_PATH/dependencies/bin/z3 -C ./why3.conf
