FROM centos:7
RUN yum -y install gcc gcc-c++ make flex bison glibc-static libstdc++-static python3 cython git

WORKDIR /smtcomp
COPY ./scrambler ./scrambler
COPY ./postprocessors ./postprocessors
