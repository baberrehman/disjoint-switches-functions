# Disjoint Switches + Disjoint Functions Coq artifact
#
#   docker build -t disjoint-switches-functions .
#   docker run --rm -it disjoint-switches-functions
#
# Then:  cd /home/coq/code/section3 && make
#        (same for section4, section51, section52)
#
# Matches the paper artifact: Coq 8.13, TLC 20210316, Metalib coq8.10.

FROM coqorg/coq:8.13.2

USER root
RUN apt-get update \
 && apt-get install -y --no-install-recommends \
      vim \
      git \
      make \
      ca-certificates \
 && rm -rf /var/lib/apt/lists/*

USER coq
SHELL ["/bin/bash", "--login", "-c"]

# Install libraries from git so we never `opam update` the frozen 8.13
# switch (the 4.07.1+flambda variant has been archived on opam.ocaml.org).
RUN eval "$(opam env)" \
 && git clone --depth 1 --branch 20210316 \
      https://github.com/charguer/tlc.git /tmp/tlc \
 && make -C /tmp/tlc -j "$(nproc)" \
 && make -C /tmp/tlc install \
 && rm -rf /tmp/tlc \
 && git clone --depth 1 --branch coq8.10 \
      https://github.com/plclub/metalib.git /tmp/metalib \
 && METALIB_DIR=/tmp/metalib \
 && if [ -d /tmp/metalib/Metalib ]; then METALIB_DIR=/tmp/metalib/Metalib; fi \
 && make -C "$METALIB_DIR" -j "$(nproc)" \
 && make -C "$METALIB_DIR" install \
 && rm -rf /tmp/metalib

COPY --chown=coq:coq code /home/coq/code
COPY --chown=coq:coq README.md /home/coq/code/README.md

WORKDIR /home/coq/code
CMD ["/bin/bash"]
