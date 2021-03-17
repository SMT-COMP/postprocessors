#!/bin/sh

docker run -v $(pwd):/dist:z smtcomp make -C scrambler dist
docker run -v $(pwd):/dist:z smtcomp make -C postprocessors dist
docker run -v $(pwd):/dist:z smtcomp sh -c "chown $(id -u):$(id -g) /dist/*.tar.gz"
