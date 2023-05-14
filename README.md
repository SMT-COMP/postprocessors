# SMT-COMP Postprocessors

This repository contains postprocessors for SMT-COMP.

## Building

The postprocessors are now build using a docker script.  Checkout the
scrambler and the postprocessors in the same directory and run the
scripts in the docker sub-directory.

```
git clone https://github.com/SMT-COMP/scrambler
git clone https://github.com/SMT-COMP/postprocessors
git clone https://github.com/SMT-COMP/dolmen
git clone https://github.com/bobot/ocaml-flint --recursive
cd postprocessors/docker
./create-docker.sh
./build-docker.sh
ls -l *.tar.gz
```

## Installing on StarExec

Note that only leaders may upload post-processors to starexec, see
the [StarExec Wiki].

The tarballs created in the docker directory can be uploaded directly.

[StarExec Wiki]: https://wiki.uiowa.edu/display/stardev/User+Guide#UserGuide-Creatingnewpost-processors
