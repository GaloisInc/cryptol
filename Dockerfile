FROM haskell:8.6 AS build
RUN apt-get update \
    && apt-get install -y wget libncurses-dev unzip \
    && wget https://github.com/Z3Prover/z3/releases/download/z3-4.7.1/z3-4.7.1-x64-debian-8.10.zip \
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
RUN make tarball
ARG TIME=""
RUN make test
RUN mkdir -p rootfs/"${CRYPTOLPATH}" \
    && cp -r lib/* rootfs/"${CRYPTOLPATH}" \
    && mkdir -p rootfs/usr/local \
    && rm -r cryptol-*-Linux-*_unknown/share/doc \
    && mv cryptol-*-Linux-*_unknown/* rootfs/usr/local \
    && cp /usr/local/bin/z3 rootfs/usr/local/bin/z3
USER root
RUN chown -R root:root /cryptol/rootfs

FROM debian:stretch-slim
RUN apt-get update \
    && apt-get install -y libgmp10 libgomp1 libffi6 wget libncurses5 unzip
COPY --from=build /cryptol/rootfs /
RUN useradd -m cryptol && chown -R cryptol:cryptol /home/cryptol
USER cryptol
ENTRYPOINT ["/usr/local/bin/cryptol"]
