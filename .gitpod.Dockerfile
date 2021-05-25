
FROM gitpod/workspace-full

USER root

# Install Dropbear SSH server
RUN apt-get update && DEBIAN_FRONTEND=noninteractive apt-get install -yq \
        dropbear \
    && apt-get clean && rm -rf /var/lib/apt/lists/* /tmp/*

# Install Chisel
RUN curl https://i.jpillora.com/chisel! | bash
