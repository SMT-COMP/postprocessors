#!/bin/sh
OPAM_VERSION=2.1.2
OPAM_INSTALLER=opam-${OPAM_VERSION}-x86_64-linux

rm -rf scrambler postprocessors dolmen
cp -a ../../scrambler .
rm -rf ./scrambler/.git
make -C scrambler cleanall
mkdir ./postprocessors
cp -a ../Makefile ../*-track postprocessors
make -C postprocessors clean
cp -a ../../trace-executor .
rm -rf ./trace-executor/.git
rm -rf ./trace-executor/docker
make -C trace-executor clean
cp -a ../../dolmen .
make -C dolmen clean
test -e ${OPAM_INSTALLER} || \
    wget https://github.com/ocaml/opam/releases/download/${OPAM_VERSION}/${OPAM_INSTALLER}

docker build -t smtcomp .
