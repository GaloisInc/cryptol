FROM haskell:8.6 AS build
RUN apt-get update \
    && apt-get install -y wget libncurses-dev unzip \
    && wget https://github.com/Z3Prover/z3/releases/download/Z3-4.8.5/z3-4.8.5-x64-debian-8.11.zip \
    && unzip z3*.zip \
    && mv z3-*/bin/z3 /usr/local/bin
RUN useradd -m cryptol \
    && su -c '/opt/cabal/bin/cabal v2-update' cryptol
COPY --chown=cryptol:cryptol . /cryptol
USER cryptol
WORKDIR /cryptol
ARG CRYPTOLPATH="/home/cryptol/.cryptol"
ARG TESTS="modsys parser issues regression renamer mono-binds"
ARG DIFF="diff"
ARG IGNORE_EXPECTED="--ignore-expected"
ARG CABAL_BUILD_FLAGS="-j"
ARG CABAL_INSTALL_FLAGS="${CABAL_BUILD_FLAGS}"
RUN ./cry build
ARG TIME=""
RUN ./cry test
RUN mkdir -p rootfs/"${CRYPTOLPATH}" \
    && cp -r lib/* rootfs/"${CRYPTOLPATH}" \
    && mkdir -p rootfs/usr/local \
    && rm -r cryptol-*-Linux-*_unknown/share/doc \
    && mv cryptol-*-Linux-*_unknown/* rootfs/usr/local \
    && cp /usr/local/bin/z3 rootfs/usr/local/bin/z3
USER root
RUN chown -R root:root /cryptol/rootfs


from debian:stretch AS solvers

# Install needed packages for building
RUN apt-get update \
    && apt-get install -y curl cmake gcc g++ git libreadline-dev
RUN useradd -m user
RUN install -d -o user -g user /solvers
USER user
WORKDIR /solvers
RUN mkdir -p rootfs/usr/local/bin

# Build abc from Galois' fork
RUN git clone https://github.com/GaloisInc/abc.git
RUN cd abc && make -j$(nproc)
RUN cp abc/abc rootfs/usr/local/bin

# Build Boolector release 3.2.1 from source
RUN curl -L https://github.com/Boolector/boolector/archive/3.2.1.tar.gz | tar xz
RUN cd boolector* && ./contrib/setup-lingeling.sh && ./contrib/setup-btor2tools.sh && ./configure.sh && cd build && make -j$(nproc)
RUN cp boolector*/build/bin/boolector rootfs/usr/local/bin

# Install yices 2.6.2
RUN curl -L https://yices.csl.sri.com/releases/2.6.2/yices-2.6.2-x86_64-pc-linux-gnu-static-gmp.tar.gz | tar xz
RUN cp yices*/bin/yices-smt2 rootfs/usr/local/bin

# Install cvc4 1.8
RUN curl -L https://github.com/CVC4/CVC4/releases/download/1.8/cvc4-1.8-x86_64-linux-opt --output rootfs/usr/local/bin/cvc4

# Install Mathsat 5.6.3
RUN curl -L https://mathsat.fbk.eu/download.php?file=mathsat-5.6.3-linux-x86_64.tar.gz | tar xz
RUN cp mathsat-5.6.3-linux-x86_64/bin/mathsat rootfs/usr/local/bin

# Set executable and run tests
RUN chmod +x rootfs/usr/local/bin/*
COPY --from=build /cryptol/rootfs /
ENV PATH=/solvers/rootfs/usr/local/bin:$PATH
RUN ! $(cryptol -c ":s prover=abc" | tail -n +2 | grep -q .) \
    && ! $(cryptol -c ":s prover=mathsat" | tail -n +2 | grep -q .) \
    && ! $(cryptol -c ":s prover=z3" | tail -n +2 | grep -q .) \
    && ! $(cryptol -c ":s prover=cvc4" | tail -n +2 | grep -q .) \
    && ! $(cryptol -c ":s prover=yices" | tail -n +2 | grep -q .) \
    && ! $(cryptol -c ":s prover=boolector" | tail -n +2 | grep -q .)


FROM debian:stretch-slim
RUN apt-get update \
    && apt-get install -y libgmp10 libgomp1 libffi6 wget libncurses5 unzip \
    && apt-get clean && rm -rf /var/lib/apt/lists/*
COPY --from=build /cryptol/rootfs /
COPY --from=solvers /solvers/rootfs /
RUN useradd -m cryptol && chown -R cryptol:cryptol /home/cryptol
USER cryptol
ENTRYPOINT ["/usr/local/bin/cryptol"]
