#!/bin/sh

rm -rf scramblere postprocessors
cp -a ../../scrambler .
rm -rf ./scrambler/.git
make -C scrambler cleanall
mkdir ./postprocessors
cp -a ../Makefile ../*-track postprocessors
make -C postprocessors clean

docker build -t smtcomp .
