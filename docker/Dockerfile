FROM centos:7
RUN yum -y install gcc gcc-c++ make flex bison glibc-static libstdc++-static python3 cython git unzip patch gmp-devel bzip2
RUN yum -y install centos-release-scl
RUN yum -y install devtoolset-7
RUN yum install -y epel-release
RUN yum install -y bubblewrap
COPY ./opam-2.1.2-x86_64-linux /usr/local/bin/opam
RUN chmod a+rx /usr/local/bin/opam

RUN opam init -y --compiler=4.13.1
RUN opam update
RUN opam install -y cmdliner.1.1.1 dune.3.2.0 spelll.0.4 gen.1.0 fmt.0.9.0 linol-lwt.0.4 menhir.20220210 pp_loc.2.1.0 zarith.1.12 farith dune-site dune-configurator ctypes
RUN yum -y install mpfr-devel

WORKDIR /smtcomp
COPY ./scrambler ./scrambler
COPY ./postprocessors ./postprocessors
COPY ./trace-executor ./trace-executor
COPY ./dolmen ./dolmen
