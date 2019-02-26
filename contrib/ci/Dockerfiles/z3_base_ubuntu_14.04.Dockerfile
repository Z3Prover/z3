FROM ubuntu:14.04

RUN apt-get update && \
    apt-get -y --no-install-recommends install \
        apt-transport-https \
        binutils \
        clang-3.9 \
        curl \
        doxygen \
        default-jdk \
        gcc-multilib \
        gcc-4.8-multilib \
        git \
        graphviz \
        g++-multilib \
        g++-4.8-multilib \
        libgmp-dev \
        libgomp1 \
        lib32gomp1 \
        llvm-3.9 \
        make \
        ninja-build \
        python3 \
        python3-setuptools \
        python2.7 \
        python-setuptools

RUN curl -SL https://packages.microsoft.com/config/ubuntu/14.04/packages-microsoft-prod.deb --output packages-microsoft-prod.deb && \
    dpkg -i packages-microsoft-prod.deb && \
    apt-get update && \
    apt-get -y --no-install-recommends install dotnet-sdk-2.1

RUN curl -SL https://cmake.org/files/v3.12/cmake-3.12.0-Linux-x86_64.sh --output cmake-3.12.0-Linux-x86_64.sh && \
    sh cmake-3.12.0-Linux-x86_64.sh --prefix=/usr/local --exclude-subdir

# Create `user` user for container with password `user`.  and give it
# password-less sudo access
RUN useradd -m user && \
    echo user:user | chpasswd && \
    cp /etc/sudoers /etc/sudoers.bak && \
    echo 'user  ALL=(root) NOPASSWD: ALL' >> /etc/sudoers
USER user
WORKDIR /home/user
ENV ASAN_SYMBOLIZER_PATH=/usr/lib/llvm-3.9/bin/llvm-symbolizer
