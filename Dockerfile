FROM ubuntu:jammy

# Install system packages
RUN apt-get update -yq \
&& apt-get install -yq --no-install-recommends \
   autoconf automake ca-certificates git \
   ocaml-nox opam pkg-config sudo libgmp-dev \
&& apt-get clean \
&& rm -fr /var/lib/apt/lists/*

# Add rocq user and drop root
RUN useradd -lmU -s /bin/bash -G sudo -p '' rocq
WORKDIR /home/rocq
USER rocq

# Install common packages
RUN set -x \
&& opam init -j$(nproc) --compiler 4.14.0 --auto-setup --yes --disable-completion --disable-sandboxing \
&& opam repo add --all-switches --set-default rocq-released https://rocq-prover.org/opam/released \
&& opam install -vyj$(nproc) dune num ocamlfind zarith conf-findutils conf-gmp opam-depext \
&& opam clean -acrs --logs \
&& opam config list && opam list

ENTRYPOINT ["opam", "exec", "--"]
CMD ["/bin/bash", "--login"]

# Install coq libraries
RUN opam install -vyj$(nproc) rocq-core=9.1.1 rocq-stdlib=9.0.0 rocq-stdpp=1.13.0 rocq-stdpp-bitvector=1.13.0 rocq-iris=4.5.0 rocq-equations=1.3.1+9.1 \
&& opam clean -acrs --logs \
&& opam config list && opam list

# Copy the artifact
COPY --chown=rocq:rocq . griotte
WORKDIR griotte
