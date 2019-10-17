#!/bin/bash

cd $HOME/velus
make realclean
./configure x86_64-linux
make
