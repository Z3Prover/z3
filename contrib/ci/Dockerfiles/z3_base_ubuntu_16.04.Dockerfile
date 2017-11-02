FROM ubuntu:16.04

RUN apt-get update && \
    apt-get -y --no-install-recommends install \
        binutils \
        clang \
        clang-3.9 \
        cmake \
        doxygen \
        default-jdk \
        gcc-multilib \
        gcc-5-multilib \
        git \
        graphviz \
        g++-multilib \
        g++-5-multilib \
        libgmp-dev \
        libgomp1 \
        libomp5 \
        libomp-dev \
        llvm-3.9 \
        make \
        mono-devel \
        ninja-build \
        python3 \
        python3-setuptools \
        python2.7 \
        python-setuptools \
        sudo

# Create `user` user for container with password `user`.  and give it
# password-less sudo access
RUN useradd -m user && \
    echo user:user | chpasswd && \
    cp /etc/sudoers /etc/sudoers.bak && \
    echo 'user  ALL=(root) NOPASSWD: ALL' >> /etc/sudoers
USER user
WORKDIR /home/user
ENV ASAN_SYMBOLIZER_PATH=/usr/lib/llvm-3.9/bin/llvm-symbolizer
