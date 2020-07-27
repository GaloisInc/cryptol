from debian:buster AS solvers

# Install needed packages for building
RUN apt-get update \
    && apt-get install -y curl cmake gcc g++ git libreadline-dev unzip
RUN useradd -m user
RUN install -d -o user -g user /solvers
USER user
WORKDIR /solvers
RUN mkdir -p rootfs/usr/local/bin

# Get Z3 4.8.8 from GitHub
RUN curl -L https://github.com/Z3Prover/z3/releases/download/z3-4.8.8/z3-4.8.8-x64-ubuntu-16.04.zip --output z3.zip
RUN unzip z3.zip
RUN mv z3-*/bin/z3 rootfs/usr/local/bin

# Build abc from GitHub. (Latest version.)
RUN git clone https://github.com/berkeley-abc/abc.git
RUN cd abc && make -j$(nproc)
RUN cp abc/abc rootfs/usr/local/bin

# Build Boolector release 3.2.1 from source
RUN curl -L https://github.com/Boolector/boolector/archive/3.2.1.tar.gz | tar xz
RUN cd boolector* && ./contrib/setup-lingeling.sh && ./contrib/setup-btor2tools.sh && ./configure.sh && cd build && make -j$(nproc)
RUN cp boolector*/build/bin/boolector rootfs/usr/local/bin

# Install Yices 2.6.2
RUN curl -L https://yices.csl.sri.com/releases/2.6.2/yices-2.6.2-x86_64-pc-linux-gnu-static-gmp.tar.gz | tar xz
RUN cp yices*/bin/yices-smt2 rootfs/usr/local/bin \
    && cp yices*/bin/yices rootfs/usr/local/bin

# Install CVC4 1.8
RUN curl -L https://github.com/CVC4/CVC4/releases/download/1.8/cvc4-1.8-x86_64-linux-opt --output rootfs/usr/local/bin/cvc4

# Install MathSAT 5.6.3 - Uncomment if you are in compliance with MathSAT's license.
# RUN curl -L https://mathsat.fbk.eu/download.php?file=mathsat-5.6.3-linux-x86_64.tar.gz | tar xz
# RUN cp mathsat-5.6.3-linux-x86_64/bin/mathsat rootfs/usr/local/bin

# Set executable and run tests
RUN chmod +x rootfs/usr/local/bin/*

FROM haskell:8.8 AS build

RUN apt-get update && apt-get install -y libncurses-dev
COPY --from=solvers /solvers/rootfs /
RUN useradd -m cryptol
COPY --chown=cryptol:cryptol . /cryptol
USER cryptol
WORKDIR /cryptol
ENV PATH=/cryptol/rootfs/usr/local/bin:$PATH
ARG CRYPTOLPATH="/cryptol/.cryptol"
ENV LANG=C.UTF-8 \
    LC_ALL=C.UTF-8
COPY cabal.GHC-8.8.3.config cabal.project.freeze
RUN mkdir -p rootfs/usr/local/bin
RUN cabal v2-update
RUN cabal v2-install --install-method=copy --installdir=rootfs/usr/local/bin exe:cryptol
RUN cabal v2-install --install-method=copy --installdir=bin test-lib
RUN ./bin/test-runner --ext=.icry --exe=./rootfs/usr/local/bin/cryptol -F -b tests
ENV PATH=/usr/local/bin:/cryptol/rootfs/usr/local/bin:$PATH
RUN    ! $(cryptol -c ":s prover=abc" | tail -n +2 | grep -q .) \
#    && ! $(cryptol -c ":s prover=mathsat" | tail -n +2 | grep -q .) \
    && ! $(cryptol -c ":s prover=cvc4" | tail -n +2 | grep -q .) \
    && ! $(cryptol -c ":s prover=yices" | tail -n +2 | grep -q .) \
    && ! $(cryptol -c ":s prover=boolector" | tail -n +2 | grep -q .) \
    && ! $(cryptol -c ":s prover=z3" | tail -n +2 | grep -q .)
RUN mkdir -p rootfs/"${CRYPTOLPATH}" \
    && cp -r lib/* rootfs/"${CRYPTOLPATH}"
USER root
RUN chown -R root:root /cryptol/rootfs

FROM debian:buster-slim
RUN apt-get update \
    && apt-get install -y libgmp10 libgomp1 libffi6 libncurses6 libtinfo6 libreadline7 \
    && apt-get clean && rm -rf /var/lib/apt/lists/*
RUN useradd -m cryptol && chown -R cryptol:cryptol /home/cryptol
COPY --from=build /cryptol/rootfs /
COPY --from=solvers /solvers/rootfs /
USER cryptol
ENV LANG=C.UTF-8 \
    LC_ALL=C.UTF-8
ENTRYPOINT ["/usr/local/bin/cryptol"]
