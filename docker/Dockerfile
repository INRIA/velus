FROM debian:testing

RUN apt-get update && \
    apt-get install -y sudo opam m4 libc6-dev-i386

# Add a default omnipotent user
RUN useradd -m developer && \
    echo "developer ALL=(ALL) NOPASSWD: ALL" > /etc/sudoers.d/developer && \
    chmod 0440 /etc/sudoers.d/developer

# Set environment variables
USER developer
ENV HOME /home/developer

# Set-up Coq-8.4
RUN opam init -a --compiler=4.02.3 && \
    eval `opam config env` && \
    opam repo add coq-released https://coq.inria.fr/opam/released && \
    opam install -j4 coq.8.4.6 menhir.20170101

# Add instructions on Bash startup
COPY motd.sh $HOME/
RUN echo ". ~/motd.sh" >> $HOME/.bashrc

# Compiler instructions
COPY make.sh $HOME/

# Compile project & give a shell
CMD ["/bin/bash", "-l", "-c", "~/make.sh"]