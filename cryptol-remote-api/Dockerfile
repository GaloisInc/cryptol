ARG GHCVER="8.10.7"
ARG GHCVER_BOOTSTRAP="8.10.2"
FROM ubuntu:22.04 AS toolchain
ARG PORTABILITY=false
RUN apt-get update && \
    apt-get install -y \
      # ghcup requirements
      build-essential curl libffi-dev libffi8 libgmp-dev libgmp10 libncurses-dev libncurses6 libtinfo6 \
      # Cryptol dependencies
      zlib1g-dev \
      # GHC build dependencies
      $(if ${PORTABILITY}; then echo git autoconf python3 libnuma-dev; fi) \
      # Miscellaneous
      unzip
ENV GHCUP_INSTALL_BASE_PREFIX=/opt \
    PATH=/opt/.ghcup/bin:$PATH
RUN curl -o /usr/local/bin/ghcup "https://downloads.haskell.org/~ghcup/0.1.17.7/x86_64-linux-ghcup-0.1.17.7" && \
    chmod +x /usr/local/bin/ghcup
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
WORKDIR /cryptol/rootfs/usr/local/bin
RUN curl -sL -o solvers.zip "https://github.com/GaloisInc/what4-solvers/releases/download/snapshot-20221212/ubuntu-22.04-bin.zip" && \
    unzip solvers.zip && rm solvers.zip && chmod +x *
USER root
RUN chown -R root:root /cryptol/rootfs

FROM ubuntu:22.04
RUN apt-get update \
    && apt-get install -y libgmp10 libgomp1 libffi8 libncurses6 libtinfo6 libreadline8 libnuma-dev openssl \
    && apt-get clean && rm -rf /var/lib/apt/lists/*
RUN useradd -m cryptol && chown -R cryptol:cryptol /home/cryptol
COPY --from=build /cryptol/rootfs /
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
