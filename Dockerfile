FROM alpine:edge AS build
RUN adduser -D cryptol \
    && apk add -X http://dl-cdn.alpinelinux.org/alpine/edge/testing z3 \
    && rm /usr/lib/libz3.so* \
    && apk add build-base cabal ghc wget ncurses-dev \
    && su -c 'cabal update' cryptol
COPY --chown=cryptol:cryptol . /cryptol
USER cryptol
WORKDIR /cryptol
ARG CRYPTOLPATH="/home/cryptol/.cryptol"
ARG TESTS="modsys parser issues regression renamer mono-binds"
ARG DIFF="diff"
ARG IGNORE_EXPECTED="--ignore-expected"
ARG CABAL_BUILD_FLAGS="-j"
ARG CABAL_INSTALL_FLAGS="${CABAL_BUILD_FLAGS}"
RUN make tarball
RUN make test
RUN mkdir -p rootfs/"${CRYPTOLPATH}" \
    && cp -r lib/* rootfs/"${CRYPTOLPATH}" \
    && mkdir -p rootfs/usr/local \
    && rm -r cryptol-*-Linux-*_unknown/share/doc \
    && mv cryptol-*-Linux-*_unknown/* rootfs/usr/local
USER root
RUN chown -R root:root /cryptol/rootfs

FROM alpine:edge
COPY --from=build /cryptol/rootfs /
RUN adduser -D cryptol \
    && chown -R cryptol:cryptol /home/cryptol \
    && apk add -X http://dl-cdn.alpinelinux.org/alpine/edge/testing z3 \
    && rm /usr/lib/libz3.so* \
    && apk add gmp libffi musl ncurses-libs \
    && rm -r /var/cache/apk/*
USER cryptol
ENTRYPOINT ["/usr/local/bin/cryptol"]
