# -------------
# OS Base image
# -------------
# >> Includes system-wide dependencies
FROM ubuntu:20.04 as lib-base
ARG DEBIAN_FRONTEND=noninteractive
RUN apt-get update && \
    apt-get -y --no-install-recommends install \
        cmake \
        make \
        clang \
        g++ \
        curl \
        default-jdk \
        python3 \
        python3-setuptools \
        python-is-python3 \
        sudo

# ----------------
# Z3 Builder Image
# ----------------
# >> Includes build files and compiles the basic z3 sources
FROM lib-base as builder
COPY ./ /z3-source/
WORKDIR /z3-source/
RUN python scripts/mk_make.py
WORKDIR /z3-source/build/
RUN make
RUN sudo make install
WORKDIR /z3-source/

# -------
# Bare z3
# -------
# >> Includes only stnadard z3 installations.
# >> Can be used as a standalone interface to z3.
FROM builder as bare-z3
ENTRYPOINT [ "z3" ]

# TODO: introduce Python-binding stage
# ...

# TODO(optional): introduce C/C++ -binding stage
# ...
