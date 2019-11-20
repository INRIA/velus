FROM ocaml/opam2:4.07

RUN opam update &&\
    opam depext -i -j 50 coq.8.9.0 menhir.20181113 ocamlbuild

COPY init.sh $HOME/

CMD ["/bin/bash", "--init-file", "~/init.sh"]
