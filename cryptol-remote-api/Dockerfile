ARG GHCVER="9.2.8"
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
ENV LANG=C.UTF-8 \
    LC_ALL=C.UTF-8
ENV GHCUP_INSTALL_BASE_PREFIX=/opt \
    PATH=/opt/.ghcup/bin:$PATH
RUN curl -o /usr/local/bin/ghcup "https://downloads.haskell.org/~ghcup/0.1.19.4/x86_64-linux-ghcup-0.1.19.4" && \
    chmod +x /usr/local/bin/ghcup
RUN ghcup install cabal 3.10.1.0 --set
ENV PATH=/root/.cabal/bin:$PATH
ADD ./cryptol-remote-api/ghc-portability.patch .
ARG GHCVER
ARG GHCVER_BOOTSTRAP
RUN if ${PORTABILITY}; then \
        ghcup install ghc ${GHCVER_BOOTSTRAP} && \
        ghcup set ghc ${GHCVER_BOOTSTRAP} && \
        cabal v2-update && \
        # We pin specific versions of alex and happy that are necessary to build
        # GHC. In general, we don't want to build the latest versions of each
        # tool, as GHC may not support them (see, for example,
        # https://gitlab.haskell.org/ghc/ghc/-/issues/24302).
        cabal v2-install alex-3.4.0.1 happy-1.20.1.1 && \
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
# The URL here is based on the same logic used to specify BIN_ZIP_FILE in
# `.github/workflow/ci.yml`, but specialized to x86-64 Ubuntu.
RUN curl -sL -o solvers.zip "https://github.com/GaloisInc/what4-solvers/releases/download/snapshot-20230711/ubuntu-22.04-X64-bin.zip" && \
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
