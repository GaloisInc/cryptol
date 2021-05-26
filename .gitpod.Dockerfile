
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
