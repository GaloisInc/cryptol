#
# Note: If building this container from a machine running non-X86 hardware
# (like Apple M1 / M2 chips), you'll need to build and run the container
# specifying the platform e.g.
# $ docker build --platform linux/amd64 ubuntu22.04.Dockerfile
#
FROM ubuntu:22.04
WORKDIR /home/

ENV LANG="C.UTF-8" LC_ALL="C.UTF-8"

RUN apt-get -y upgrade \
    && apt-get -y update \
    && apt-get install -y \
        build-essential \
        git
RUN ["git", "clone", "https://github.com/GaloisInc/cryptol.git"]

WORKDIR /home/cryptol
RUN ["dev/dev_setup.sh"]
RUN ["source", "dev/env.sh"]
CMD ["/bin/sh"]