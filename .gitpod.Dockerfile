
FROM gitpod/workspace-full

# Install docker buildx plugin
RUN mkdir -p ~/.docker/cli-plugins && \
    wget \
      https://github.com/docker/buildx/releases/download/v0.5.1/buildx-v0.5.1.linux-amd64 \
      -O ~/.docker/cli-plugins/docker-buildx && \
    chmod a+x ~/.docker/cli-plugins/docker-buildx

USER root

# Install Dropbear SSH server
RUN apt-get update && DEBIAN_FRONTEND=noninteractive apt-get install -yq \
        dropbear \
    && apt-get clean && rm -rf /var/lib/apt/lists/* /tmp/*

# Install Chisel
RUN curl https://i.jpillora.com/chisel! | bash

# Install GHC
ARG GHCVER="9.2.8"
ENV GHCUP_INSTALL_BASE_PREFIX=/opt \
    PATH=/opt/.ghcup/bin:$PATH
RUN curl -o /usr/local/bin/ghcup "https://downloads.haskell.org/~ghcup/0.1.19.4/x86_64-linux-ghcup-0.1.19.4" && \
    chmod +x /usr/local/bin/ghcup
RUN ghcup install cabal --set
ENV PATH=/root/.cabal/bin:$PATH
RUN ghcup install ghc ${GHCVER} && \
    ghcup set ghc ${GHCVER}
