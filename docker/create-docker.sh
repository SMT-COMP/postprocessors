#!/bin/sh

rm -rf scrambler postprocessors
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

docker build -t smtcomp .
