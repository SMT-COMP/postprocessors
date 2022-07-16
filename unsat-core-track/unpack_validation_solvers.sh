#!/bin/bash

SCRIPTDIR=`dirname $(readlink -f "$0")`

cd $SCRIPTDIR

# clean up validation_solver directory
rm -rf validation_solvers
mkdir validation_solvers

# prepare download
# the directory may already exists,
# so we don't have to re-download for each build
mkdir -p download

tail -n +2 validation_solvers.csv | (
    IFS=,
    while read SOLVER ID CONFIG; do
        # download solver, if not already downloaded
        if [ \! -e "download/${ID}.zip" ]; then
            curl -o download/${ID}.zip 'https://www.starexec.org/starexec/secure/download?type=solver&id='${ID}
        fi

        # unpack solver to staging area
        rm -rf stage
        mkdir -p stage
        cd stage
        unzip ../download/${ID}.zip

        # now move solver directory to validation_solvers
        mv * ../validation_solvers/${SOLVER}

        # clean up staging area
        cd ..
        rmdir stage || echo "Solver directory not clean"

        # change name of starexec_run script if not default.
        if [ "${CONFIG}" != "default" ]; then
            mv validation_solvers/${SOLVER}/bin/starexec_run_${CONFIG} \
               validation_solvers/${SOLVER}/bin/starexec_run_default
        fi
    done
)

## HACK to make vampire work with `timeout` command.

sed -i 's!^./vampire!exec ./vampire!' validation_solvers/vampire/bin/starexec_run_default
