ARG GHCVER="8.10.3"
ARG GHCVER_BOOTSTRAP="8.10.2"
FROM debian:buster-20210511 AS solvers

# Install needed packages for building
RUN apt-get update \
    && apt-get install -y curl cmake gcc g++ git libreadline-dev unzip
RUN useradd -m user
RUN install -d -o user -g user /solvers
USER user
WORKDIR /solvers
RUN mkdir -p rootfs/usr/local/bin

# Get Z3 4.8.8 from GitHub
RUN curl -L https://github.com/Z3Prover/z3/releases/download/z3-4.8.8/z3-4.8.8-x64-ubuntu-16.04.zip --output z3.zip && \
    unzip z3.zip && \
    mv z3-*/bin/z3 rootfs/usr/local/bin

# Build abc from GitHub. (Latest version.)
RUN git clone https://github.com/berkeley-abc/abc.git && \
    ( cd abc && make -j$(nproc) ) && \
    cp abc/abc rootfs/usr/local/bin

# Build Boolector release 3.2.1 from source
RUN curl -L https://github.com/Boolector/boolector/archive/3.2.1.tar.gz | tar xz && \
    ( cd boolector* && ./contrib/setup-lingeling.sh && ./contrib/setup-btor2tools.sh && ./configure.sh && cd build && make -j$(nproc) ) && \
    cp boolector*/build/bin/boolector rootfs/usr/local/bin

# Install Yices 2.6.2
RUN curl -L https://yices.csl.sri.com/releases/2.6.2/yices-2.6.2-x86_64-pc-linux-gnu-static-gmp.tar.gz | tar xz && \
    cp yices*/bin/yices-smt2 rootfs/usr/local/bin \
    && cp yices*/bin/yices rootfs/usr/local/bin

# Install CVC4 1.8
# The latest CVC4 1.8 and the release version has a minor discrepency between it, causing sbv to fail
# https://github.com/CVC4/CVC4/releases/download/1.8/cvc4-1.8-x86_64-linux-opt
RUN latest="$(curl -sSL 'http://cvc4.cs.stanford.edu/downloads/builds/x86_64-linux-opt/unstable/' | grep linux-opt | tail -n1 | sed -e 's/.*href="//' -e 's/\([^>]*\)">.*$/\1/')" && \
    curl --output rootfs/usr/local/bin/cvc4 -sSL "https://cvc4.cs.stanford.edu/downloads/builds/x86_64-linux-opt/unstable/$latest"

# Install MathSAT 5.6.3 - Uncomment if you are in compliance with MathSAT's license.
# RUN curl -L https://mathsat.fbk.eu/download.php?file=mathsat-5.6.3-linux-x86_64.tar.gz | tar xz
# RUN cp mathsat-5.6.3-linux-x86_64/bin/mathsat rootfs/usr/local/bin

# Set executable and run tests
RUN chmod +x rootfs/usr/local/bin/*

FROM debian:buster-20210511 AS toolchain
ARG PORTABILITY=false
RUN apt-get update && apt-get install -y libncurses-dev libz-dev \
    build-essential curl libffi-dev libffi6 libgmp-dev libgmp10 libncurses-dev libncurses5 libtinfo5 libnuma-dev \
    $(if ${PORTABILITY}; then echo git autoconf python3; fi)
ENV GHCUP_INSTALL_BASE_PREFIX=/opt \
    PATH=/opt/.ghcup/bin:$PATH
RUN curl -o /usr/local/bin/ghcup "https://downloads.haskell.org/~ghcup/0.1.14/x86_64-linux-ghcup-0.1.14" && \
    chmod +x /usr/local/bin/ghcup
COPY --from=solvers /solvers/rootfs /
RUN ghcup install cabal --set
ENV PATH=/root/.cabal/bin:$PATH
ADD ./cryptol-remote-api/ghc-portability.patch .
ARG GHCVER
ARG GHCVER_BOOTSTRAP
RUN if ${PORTABILITY}; then \
        ghcup install ghc ${GHCVER_BOOTSTRAP} && \
        ghcup set ghc ${GHCVER_BOOTSTRAP} && \
        cabal v2-update && \
        cabal v2-install alex happy-1.19.12 && \
        git clone --recurse-submodules --depth 1 --branch ghc-${GHCVER}-release https://gitlab.haskell.org/ghc/ghc.git && \
        cd ./ghc && \
        git apply ../ghc-portability.patch && \
        ./boot && \
        ./configure && \
        make -j && \
        make install && \
        cd .. && \
        rm -rf ./ghc && \
        ghcup rm ghc ${GHCVER_BOOTSTRAP}; \
    else \
        ghcup install ghc ${GHCVER} && \
        ghcup set ghc ${GHCVER}; \
    fi

FROM toolchain AS build

RUN useradd -u 1000 -m cryptol
COPY --chown=cryptol:cryptol . /cryptol
USER cryptol
WORKDIR /cryptol
ENV PATH=/cryptol/rootfs/usr/local/bin:$PATH
ARG CRYPTOLPATH="/cryptol/.cryptol"
ENV LANG=C.UTF-8 \
    LC_ALL=C.UTF-8
COPY cabal.GHC-${GHCVER}.config cabal.project.freeze

RUN if ${PORTABILITY}; then SERVERS_NOT_THREADED="true"; fi

RUN cabal v2-update && \
    cabal v2-build -j ${SERVERS_NOT_THREADED:+-fNotThreaded} cryptol-remote-api:exe:cryptol-remote-api cryptol-remote-api:exe:cryptol-eval-server && \
    mkdir -p rootfs/usr/local/bin && \
    cp $(cabal v2-exec which cryptol-remote-api) rootfs/usr/local/bin && \
    cp $(cabal v2-exec which cryptol-eval-server) rootfs/usr/local/bin
ENV PATH=/usr/local/bin:/cryptol/rootfs/usr/local/bin:$PATH
RUN mkdir -p rootfs/"${CRYPTOLPATH}" \
    && cp -r lib/* rootfs/"${CRYPTOLPATH}"
USER root
RUN chown -R root:root /cryptol/rootfs

FROM debian:buster-20210511-slim
RUN apt-get update \
    && apt-get install -y libgmp10 libgomp1 libffi6 libncurses6 libtinfo6 libreadline7 libnuma-dev openssl \
    && apt-get clean && rm -rf /var/lib/apt/lists/*
RUN useradd -m cryptol && chown -R cryptol:cryptol /home/cryptol
COPY --from=build /cryptol/rootfs /
COPY --from=solvers /solvers/rootfs /
USER cryptol
ENV LANG=C.UTF-8 \
    LC_ALL=C.UTF-8
ENTRYPOINT ["/usr/local/bin/cryptol-remote-api"]
WORKDIR /home/cryptol
# Create self-signed certificates for HTTPS testing purposes - N.B.,
# clients must opt in to accepting these by passing `verify=False` to
# the `cryptol.connect` method (otherwise a security error is raised).
RUN openssl req -nodes -newkey rsa:2048 -keyout server.key -out server.csr \
      -subj "/C=GB/ST=London/L=London/O=Acme Widgets/OU=IT Department/CN=localhost"
RUN openssl x509 -req -days 365 -in server.csr -signkey server.key -out server.crt
CMD ["http", "--host", "0.0.0.0", "--port", "8080", "/"]
EXPOSE 8080
