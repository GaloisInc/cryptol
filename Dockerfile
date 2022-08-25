FROM ubuntu:22.04 AS build

RUN apt-get update && \
    apt-get install -y \
      # ghcup requirements
      build-essential curl libffi-dev libffi8 libgmp-dev libgmp10 libncurses-dev libncurses6 libtinfo6 \
      # Cryptol dependencies
      zlib1g-dev \
      # Miscellaneous
      unzip
RUN useradd -m cryptol
COPY --chown=cryptol:cryptol . /cryptol
USER cryptol
WORKDIR /cryptol
RUN mkdir -p rootfs/usr/local/bin
WORKDIR /cryptol/rootfs/usr/local/bin
RUN curl -o solvers.zip -sL "https://github.com/GaloisInc/what4-solvers/releases/download/snapshot-20220812/ubuntu-22.04-bin.zip"
RUN unzip solvers.zip && rm solvers.zip && chmod +x *
WORKDIR /cryptol
ENV PATH=/cryptol/rootfs/usr/local/bin:/home/cryptol/.local/bin:/home/cryptol/.ghcup/bin:$PATH
RUN z3 --version
ARG CRYPTOLPATH="/cryptol/.cryptol"
ENV LANG=C.UTF-8 \
    LC_ALL=C.UTF-8
COPY cabal.GHC-8.10.7.config cabal.project.freeze
RUN mkdir -p /home/cryptol/.local/bin && \
    curl -L https://downloads.haskell.org/~ghcup/0.1.17.7/x86_64-linux-ghcup-0.1.17.7 -o /home/cryptol/.local/bin/ghcup && \
    chmod +x /home/cryptol/.local/bin/ghcup
RUN mkdir -p /home/cryptol/.ghcup && \
    ghcup --version && \
    ghcup install cabal 3.6.2.0 && \
    ghcup install ghc 8.10.7 && \
    ghcup set ghc 8.10.7
RUN cabal v2-update && \
    cabal v2-build -j cryptol:exe:cryptol && \
    cp $(cabal v2-exec which cryptol) rootfs/usr/local/bin && \
    cabal v2-install --install-method=copy --overwrite-policy=always --installdir=bin test-lib
RUN ./bin/test-runner --ext=.icry --exe=./rootfs/usr/local/bin/cryptol -F -b tests
ENV PATH=/usr/local/bin:/cryptol/rootfs/usr/local/bin:$PATH
RUN    ! $(cryptol -c ":s prover=yices" | tail -n +2 | grep -q .) \
    #    && ! $(cryptol -c ":s prover=mathsat" | tail -n +2 | grep -q .) \
    && ! $(cryptol -c ":s prover=cvc4" | tail -n +2 | grep -q .) \
    && ! $(cryptol -c ":s prover=abc" | tail -n +2 | grep -q .) \
    # && ! $(cryptol -c ":s prover=boolector" | tail -n +2 | grep -q .) \
    && ! $(cryptol -c ":s prover=z3" | tail -n +2 | grep -q .)
RUN mkdir -p rootfs/"${CRYPTOLPATH}" \
    && cp -r lib/* rootfs/"${CRYPTOLPATH}"
USER root
RUN chown -R root:root /cryptol/rootfs

FROM ubuntu:22.04
RUN apt-get update \
    && apt-get install -y libgmp10 libgomp1 libffi8 libncurses6 libtinfo6 libreadline8 \
    && apt-get clean && rm -rf /var/lib/apt/lists/*
RUN useradd -m cryptol && chown -R cryptol:cryptol /home/cryptol
COPY --from=build /cryptol/rootfs /
USER cryptol
ENV LANG=C.UTF-8 \
    LC_ALL=C.UTF-8
ENTRYPOINT ["/usr/local/bin/cryptol"]
