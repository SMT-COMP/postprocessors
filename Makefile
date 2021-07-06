## 
## Makefile for SMT-COMP post-processors
##

# make all will build all post-processor tar balls.
#
# You need to checkout the scrambler repository into the same parent
# directory as the postprocessor respository.


SCRAMBLER_DIR = ../scrambler
POSTPROCESSORS = SMT-COMP-2021-single-query-post-processor.tar.gz \
	SMT-COMP-2021-incremental-post-processor.tar.gz \
	SMT-COMP-2021-unsat-core-post-processor.tar.gz \
	SMT-COMP-2021-model-validation-post-processor.tar.gz

all: $(POSTPROCESSORS) test

# targets to prepare StarExec postprocessors

$(SCRAMBLER_DIR)/scrambler:
	make -C $(SCRAMBLER_DIR) scrambler
unsat-core-track/scrambler: $(SCRAMBLER_DIR)/scrambler
	cp $< $@

SMT-COMP-2021-single-query-post-processor.tar.gz: single-query-track/process
	tar -C single-query-track -czf $@ process

SMT-COMP-2021-incremental-post-processor.tar.gz: incremental-track/process
	tar -C incremental-track -czf $@ process

SMT-COMP-2021-unsat-core-post-processor.tar.gz: unsat-core-track/process unsat-core-track/scrambler
	unsat-core-track/unpack_validation_solvers.sh
	tar -C unsat-core-track -czf $@ process scrambler validation_solvers

SMT-COMP-2021-model-validation-post-processor.tar.gz: model-validation-track/process model-validation-track/requirements.txt model-validation-track/ModelValidator.py
	pip3 install -r model-validation-track/requirements.txt
	cd model-validation-track; pyinstaller -F ModelValidator.py
	cp model-validation-track/dist/ModelValidator model-validation-track
	tar -C model-validation-track -czf $@ process ModelValidator

test:
	(cd unsat-core-track; ./run-tests.sh)

.PHONY: all clean test

clean:
	rm -rf model-validation-track/pysmt
	rm -f model-validation-track/ModelValidator
	rm -f unsat-core-track/scrambler
	rm -rf unsat-core-track/validation_solvers
	rm -f $(POSTPROCESSORS)

dist: $(POSTPROCESSORS)
	cp $(POSTPROCESSORS) /dist
