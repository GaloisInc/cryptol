FROM haskell:8.8 AS build
RUN apt-get update \
    && apt-get install -y locales wget libncurses-dev unzip \
    && wget https://github.com/Z3Prover/z3/releases/download/z3-4.8.8/z3-4.8.8-x64-ubuntu-16.04.zip \
    && wget https://github.com/CVC4/CVC4/releases/download/1.8/cvc4-1.8-x86_64-linux-opt \
    && unzip z3*.zip \
    && mv z3-*/bin/z3 /usr/local/bin \
    && mv cvc4-1.8-x86_64-linux-opt /usr/local/bin/cvc4 \
    && chmod +x /usr/local/bin/cvc4
RUN useradd -m cryptol \
    && su -c '/opt/cabal/bin/cabal v2-update' cryptol
COPY --chown=cryptol:cryptol . /cryptol
USER cryptol
WORKDIR /cryptol
ARG CRYPTOLPATH="/home/cryptol/.cryptol"
ENV LANG=C.UTF-8 \
    LC_ALL=C.UTF-8
COPY cabal.GHC-8.8.3.config cabal.project.freeze
RUN mkdir -p rootfs/usr/local/bin
RUN cabal v2-install --install-method=copy --installdir=rootfs/usr/local/bin exe:cryptol
RUN cabal v2-install --install-method=copy --installdir=bin test-lib
RUN ./bin/test-runner --ext=.icry --exe=./rootfs/usr/local/bin/cryptol -F -b tests
RUN mkdir -p rootfs/"${CRYPTOLPATH}" \
    && cp -r lib/* rootfs/"${CRYPTOLPATH}" \
    && cp /usr/local/bin/z3 rootfs/usr/local/bin/z3 \
    && cp /usr/local/bin/cvc4 rootfs/usr/local/bin/cvc4
USER root
RUN chown -R root:root /cryptol/rootfs

FROM debian:buster-slim
RUN apt-get update \
    && apt-get install -y libgmp10 libgomp1 libffi6 wget libncurses6 libtinfo6 unzip \
    && apt-get clean && rm -rf /var/lib/apt/lists/*
RUN useradd -m cryptol && chown -R cryptol:cryptol /home/cryptol
COPY --from=build /cryptol/rootfs /
USER cryptol
ENV LANG=C.UTF-8 \
    LC_ALL=C.UTF-8
ENTRYPOINT ["/usr/local/bin/cryptol"]
