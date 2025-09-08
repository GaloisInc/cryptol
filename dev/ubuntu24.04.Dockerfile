#
# Note: If building this container from a machine running non-X86 hardware
# (like Apple M1 / M2 chips), you'll need to build and run the container
# specifying the platform e.g.
# $ docker build --platform linux/amd64 ubuntu24.04.Dockerfile
#
FROM ubuntu:24.04
WORKDIR /home/

RUN apt-get -y upgrade \
    && apt-get -y update \
    && apt-get install -y \
        build-essential \
        git
RUN ["git", "clone", "https://github.com/GaloisInc/cryptol.git"]

WORKDIR /home/cryptol
RUN ["dev/dev_setup.sh"]

# Hardcode the environment variables we're going to need
ENV LANG="C.UTF-8" LC_ALL="C.UTF-8" PATH=$PATH:/root/.ghcup/bin

CMD ["/bin/bash"]
