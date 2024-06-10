FROM ubuntu:20.04
WORKDIR /home/

RUN ["apt-get", "-y", "upgrade"]
RUN ["apt-get", "-y", "update"]
RUN ["apt-get", "install", "-y", "git"]
RUN ["git", "clone", "https://github.com/GaloisInc/cryptol.git"]

COPY dev_setup.sh ./cryptol/
CMD ["/bin/bash"]