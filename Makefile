## 
## Makefile for SMT-COMP post-processors
##

# make all will build all post-processor tar balls.
#
# You need to checkout the scrambler repository into the same parent
# directory as the postprocessor respository.

YEAR=2022

SCRAMBLER_DIR = ../scrambler
DOLMEN_DIR = ../dolmen
DOLMEN_MAIN_EXE = _build/default/src/bin/main.exe
POSTPROCESSORS = SMT-COMP-$(YEAR)-single-query-post-processor.tar.gz \
	SMT-COMP-$(YEAR)-incremental-post-processor.tar.gz \
	SMT-COMP-$(YEAR)-unsat-core-post-processor.tar.gz \
	SMT-COMP-$(YEAR)-model-validation-post-processor.tar.gz \
	SMT-COMP-$(YEAR)-proof-post-processor.tar.gz

all: $(POSTPROCESSORS) test

# targets to prepare StarExec postprocessors

$(SCRAMBLER_DIR)/scrambler:
	make -C $(SCRAMBLER_DIR) scrambler
unsat-core-track/scrambler: $(SCRAMBLER_DIR)/scrambler
	cp $< $@

$(DOLMEN_DIR)/$(DOLMEN_MAIN_EXE):
	bash -c 'eval `opam env`; make -C $(DOLMEN_DIR)'
model-validation-track/dolmen: $(DOLMEN_DIR)/$(DOLMEN_MAIN_EXE)
	cp $< $@

SMT-COMP-$(YEAR)-single-query-post-processor.tar.gz: single-query-track/process
	tar -C single-query-track -czf $@ process

SMT-COMP-$(YEAR)-incremental-post-processor.tar.gz: incremental-track/process
	tar -C incremental-track -czf $@ process

SMT-COMP-$(YEAR)-unsat-core-post-processor.tar.gz: unsat-core-track/process unsat-core-track/scrambler
	unsat-core-track/unpack_validation_solvers.sh
	tar -C unsat-core-track -czf $@ process scrambler validation_solvers

SMT-COMP-$(YEAR)-model-validation-post-processor.tar.gz: model-validation-track/process model-validation-track/process.dolmen model-validation-track/requirements.txt model-validation-track/ModelValidator.py model-validation-track/dolmen
	pip3 install -r model-validation-track/requirements.txt
	cd model-validation-track; pyinstaller -F ModelValidator.py
	cp model-validation-track/dist/ModelValidator model-validation-track
	tar -C model-validation-track -czf $@ process process.dolmen ModelValidator dolmen

SMT-COMP-$(YEAR)-proof-post-processor.tar.gz: single-query-track/process
	tar -C proof-track -czf $@ process

test:
	(cd single-query-track; ./run_tests.sh)
	(cd unsat-core-track; ./run-tests.sh)
	(cd model-validation-track; ./run-tests.sh)
	(cd proof-track; ./run_tests.sh)

.PHONY: all clean test

clean:
	rm -rf model-validation-track/pysmt
	rm -f model-validation-track/ModelValidator
	rm -f unsat-core-track/scrambler
	rm -rf unsat-core-track/validation_solvers
	rm -f $(POSTPROCESSORS)

dist: $(POSTPROCESSORS)
	cp $(POSTPROCESSORS) /dist
