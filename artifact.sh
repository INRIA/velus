#!/usr/bin/env sh

# Clean up
make realclean
./tests/clean.sh

# Tarball
tar -czf velus.tar.gz \
    CompCert \
    readme.md \
    configure \
    includes \
    variables.mk \
    tools/automake.mll \
    Makefile \
    vfiles \
    src/ \
    extraction/ \
    tests/*.lus \
    examples/ \
    doc/
